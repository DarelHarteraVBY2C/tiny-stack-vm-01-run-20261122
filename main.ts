// Tiny stack VM, ISA v1.
import { readFileSync, writeFileSync, mkdirSync, readdirSync, existsSync } from 'node:fs';
import { join } from 'node:path';

const IN_DIR = process.env.MAKEFUN_INPUT_DIR || '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR || '/output';
const MAX_STEPS = 1000000, MAX_OUT = 65536, CAP = 256, CALLS = 64, MEMW = 256;

// One exception ends a run; code is the exit code.
class Stop extends Error {
  constructor(code) { super('stop ' + code); this.code = code; }
}

// Binary ops; div-by-zero is checked by the caller (trap 4).
const BIN = {
  16: (a, b) => (a + b) | 0, 17: (a, b) => (a - b) | 0,
  18: (a, b) => Math.imul(a, b), 19: (a, b) => Math.trunc(a / b) | 0,
  20: (a, b) => (a % b) | 0, 21: (a, b) => Math.trunc((a >>> 0) / (b >>> 0)) | 0,
  22: (a, b) => ((a >>> 0) % (b >>> 0)) | 0, 24: (a, b) => a & b,
  25: (a, b) => a | b, 26: (a, b) => a ^ b,
  28: (a, b) => a << (b & 31), 29: (a, b) => a >> (b & 31),
  30: (a, b) => (a >>> (b & 31)) | 0, 32: (a, b) => (a === b ? 1 : 0),
  33: (a, b) => (a < b ? 1 : 0), 34: (a, b) => ((a >>> 0) < (b >>> 0) ? 1 : 0),
};

const IMM = { 1: 1, 2: 4, 48: 2, 49: 2, 50: 2, 51: 2 };

class Engine {
  constructor(prog, input) {
    this.prog = prog; this.input = input;
    this.pc = 0; this.steps = 0; this.nextIn = 0;
    this.sp = 0; this.csp = 0;
    this.vals = new Int32Array(CAP);
    this.rets = new Int32Array(CALLS);
    this.cells = new Int32Array(MEMW);
    this.sink = new Uint8Array(MAX_OUT);
    this.sunk = 0;
  }

  push(v) {
    if (this.sp >= CAP) throw new Stop(3);
    this.vals[this.sp++] = v | 0;
  }

  pop() {
    if (this.sp <= 0) throw new Stop(2);
    return this.vals[--this.sp];
  }

  need(n) {
    if (this.sp < n) throw new Stop(2);
  }

  exec(op) {
    if (op === 0) throw new Stop(0);
    if (op === 1) {
      const b = this.prog[this.pc + 1];
      this.push(b >= 128 ? b - 256 : b);
      this.pc += 2;
    } else if (op === 2) {
      const q = this.pc;
      this.push(this.prog[q + 1] | (this.prog[q + 2] << 8) | (this.prog[q + 3] << 16) | (this.prog[q + 4] << 24));
      this.pc += 5;
    } else if (op === 3) { this.pop(); this.pc++; }
    else if (op === 4) { this.need(1); this.push(this.vals[this.sp - 1]); this.pc++; }
    else if (op === 5) {
      this.need(2);
      const t = this.vals[this.sp - 1];
      this.vals[this.sp - 1] = this.vals[this.sp - 2];
      this.vals[this.sp - 2] = t;
      this.pc++;
    } else if (op === 6) { this.need(2); this.push(this.vals[this.sp - 2]); this.pc++; }
    else if (op === 7) {
      this.need(3);
      const c = this.vals[this.sp - 1], b = this.vals[this.sp - 2], a = this.vals[this.sp - 3];
      this.vals[this.sp - 3] = b; this.vals[this.sp - 2] = c; this.vals[this.sp - 1] = a;
      this.pc++;
    } else if (op === 23) { this.need(1); this.vals[this.sp - 1] = (-this.vals[this.sp - 1]) | 0; this.pc++; }
    else if (op === 27) { this.need(1); this.vals[this.sp - 1] = ~this.vals[this.sp - 1]; this.pc++; }
    else if (op >= 16 && op <= 34 && op !== 31) {
      this.need(2);
      const b = this.pop(), a = this.pop();
      if (b === 0 && op >= 19 && op <= 22) throw new Stop(4);
      this.push(BIN[op](a, b));
      this.pc++;
    } else if (op === 48 || op === 49 || op === 50) {
      const w = this.prog[this.pc + 1] | (this.prog[this.pc + 2] << 8);
      const off = w >= 32768 ? w - 65536 : w;
      if (op === 48) this.pc = this.pc + 3 + off;
      else {
        const v = this.pop();
        if ((op === 49 && v === 0) || (op === 50 && v !== 0)) this.pc = this.pc + 3 + off;
        else this.pc += 3;
      }
    } else if (op === 51) {
      if (this.csp >= CALLS) throw new Stop(7);
      this.rets[this.csp++] = this.pc + 3;
      this.pc = this.prog[this.pc + 1] | (this.prog[this.pc + 2] << 8);
    } else if (op === 52) {
      if (this.csp <= 0) throw new Stop(8);
      this.pc = this.rets[--this.csp];
    } else if (op === 64) {
      const addr = this.pop();
      if (addr < 0 || addr >= MEMW) throw new Stop(6);
      this.push(this.cells[addr]);
      this.pc++;
    } else if (op === 65) {
      this.need(2);
      const addr = this.pop(), v = this.pop();
      if (addr < 0 || addr >= MEMW) throw new Stop(6);
      this.cells[addr] = v;
      this.pc++;
    } else if (op === 80) {
      const t = String(this.pop());
      if (this.sunk + t.length > MAX_OUT) throw new Stop(11);
      for (let i = 0; i < t.length; i++) this.sink[this.sunk++] = t.charCodeAt(i);
      this.pc++;
    } else if (op === 81) {
      const v = this.pop();
      if (this.sunk >= MAX_OUT) throw new Stop(11);
      this.sink[this.sunk++] = v & 255;
      this.pc++;
    } else if (op === 82) {
      this.push(this.nextIn < this.input.length ? this.input[this.nextIn++] : -1);
      this.pc++;
    } else if (op === 83) throw new Stop(this.pop() & 255);
    else throw new Stop(5);
  }

  run() {
    for (;;) {
      if (this.steps >= MAX_STEPS) throw new Stop(10);
      const at = this.pc;
      if (at < 0 || at >= this.prog.length) throw new Stop(9);
      const op = this.prog[at];
      if (at + 1 + (IMM[op] || 0) > this.prog.length) throw new Stop(9);
      this.steps++;
      this.exec(op);
    }
  }
}

function runOne(prog, input) {
  const vm = new Engine(prog, input);
  let code = 0;
  try { vm.run(); } catch (e) { if (e instanceof Stop) code = e.code; else throw e; }
  return [vm.sink.subarray(0, vm.sunk), code];
}

for (const id of readdirSync(IN_DIR).sort()) {
  const dir = join(IN_DIR, id);
  const progPath = join(dir, 'program.bin');
  if (!existsSync(progPath)) continue;
  const inputPath = join(dir, 'input.bin');
  const [bytes, code] = runOne(readFileSync(progPath), existsSync(inputPath) ? readFileSync(inputPath) : Buffer.alloc(0));
  const outDir = join(OUT_DIR, id);
  mkdirSync(outDir, { recursive: true });
  writeFileSync(join(outDir, 'stdout.bin'), bytes);
  writeFileSync(join(outDir, 'exit.txt'), code + '\n');
}
