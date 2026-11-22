// Tiny stack VM: a from-scratch interpreter of make.fun's tiny stack ISA.
// One run answers every instance: reads program.bin + input.bin per <id>,
// writes stdout.bin + exit.txt. Node 22, stdlib only.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const DATA_MAX = 256, CALL_MAX = 64, MEM_WORDS = 256;
const STEP_MAX = 1_000_000, OUT_MAX = 65_536;
// Trap exit codes: underflow 2, overflow 3, div-by-zero 4, bad opcode 5,
// bad memory 6, call depth 7, empty RET 8, pc 9, step limit 10, output 11.
const T = { under: 2, over: 3, div0: 4, badop: 5, mem: 6, call: 7, ret: 8, pc: 9, steps: 10, out: 11 };

const enc = new TextEncoder();

function run(prog: Uint8Array, input: Uint8Array): { out: Uint8Array; code: number } {
  const n = prog.length;
  const D = new Int32Array(DATA_MAX);
  const C = new Int32Array(CALL_MAX);
  const M = new Int32Array(MEM_WORDS);
  const out = new Uint8Array(OUT_MAX);
  let sp = 0, csp = 0, pc = 0, steps = 0, ip = 0, olen = 0;
  const done = (code: number) => ({ out: out.slice(0, olen), code });

  for (;;) {
    if (steps >= STEP_MAX) return done(T.steps);
    if (pc < 0 || pc >= n) return done(T.pc);
    const op = prog[pc];
    let imm = 0, pops = 0, pushes = 0;
    switch (op) {
      case 0x00: break;
      case 0x01: imm = 1; pushes = 1; break;
      case 0x02: imm = 4; pushes = 1; break;
      case 0x03: pops = 1; break;
      case 0x04: pops = 1; pushes = 2; break;
      case 0x05: pops = 2; pushes = 2; break;
      case 0x06: pops = 2; pushes = 3; break;
      case 0x07: pops = 3; pushes = 3; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: pops = 2; pushes = 1; break;
      case 0x17: case 0x1b: pops = 1; pushes = 1; break;
      case 0x30: imm = 2; break;
      case 0x31: case 0x32: imm = 2; pops = 1; break;
      case 0x33: imm = 2; break;
      case 0x34: break;
      case 0x40: pops = 1; pushes = 1; break;
      case 0x41: pops = 2; break;
      case 0x50: case 0x51: case 0x53: pops = 1; break;
      case 0x52: pushes = 1; break;
      default: return done(T.badop);
    }
    if (pc + imm >= n) return done(T.pc);
    steps++;
    const next = pc + 1 + imm;
    if (sp < pops) return done(T.under);
    if (sp - pops + pushes > DATA_MAX) return done(T.over);
    pc = next;

    switch (op) {
      case 0x00: return done(0);
      case 0x01: D[sp++] = (prog[next - 1] << 24) >> 24; break;
      case 0x02: D[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 0x17: D[sp - 1] = (-D[sp - 1]) | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1], a = D[sp - 2];
        let r: number;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13:
            if (b === 0) return done(T.div0);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break;
          case 0x14:
            if (b === 0) return done(T.div0);
            r = b === -1 ? 0 : (a % b) | 0; break;
          case 0x15:
            if (b === 0) return done(T.div0);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
          case 0x16:
            if (b === 0) return done(T.div0);
            r = ((a >>> 0) % (b >>> 0)) | 0; break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
        }
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = D[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (csp === CALL_MAX) return done(T.call);
        C[csp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return done(T.ret);
        pc = C[--csp];
        break;
      case 0x40: {
        const addr = D[sp - 1];
        if (addr < 0 || addr >= MEM_WORDS) return done(T.mem);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: {
        const addr = D[sp - 1], v = D[sp - 2];
        if (addr < 0 || addr >= MEM_WORDS) return done(T.mem);
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 0x50: {
        const bytes = enc.encode(String(D[sp - 1]));
        if (olen + bytes.length > OUT_MAX) return done(T.out);
        sp--;
        out.set(bytes, olen);
        olen += bytes.length;
        break;
      }
      case 0x51:
        if (olen + 1 > OUT_MAX) return done(T.out);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52:
        D[sp++] = ip < input.length ? input[ip++] : -1;
        break;
      case 0x53:
        return done(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const dir = join(I, id);
  const prog = new Uint8Array(readFileSync(join(dir, 'program.bin')));
  let input = new Uint8Array(0);
  try { input = new Uint8Array(readFileSync(join(dir, 'input.bin'))); } catch { /* empty input */ }
  const r = run(prog, input);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
