#!/usr/bin/env node
"use strict";

// Experimental valuation-uniform probe for the original TM63 table.
// Transition table transcribed from ChampionRootBridge.lean.
// Checks exact finite tape support, not only state/head endpoints.
// Number arithmetic is exact for this deliberately small test range.

const d0 = [false, false, true];
const d1 = [true, true, true];
const lh = [true, false, true, true, true, true];
const d1pow = n => Array(3 * n).fill(true);
function markerWord(m) {
  switch (m % 3) {
    case 0: return [false, true];
    case 1: return [true, false, true];
    default: return [true, true, false, true];
  }
}
function binDec(len, n) {
  let p = 2 ** (len + 1) - 1 - n;
  const out = [];
  for (let i = 0; i < len; i++) {
    if (p <= 1) break;
    out.push(...(p % 2 === 0 ? d0 : d1));
    p = Math.floor(p / 2);
  }
  return out;
}
function s1LeftFacing(L, n, m, a, z) {
  return [...binDec(a, z), ...markerWord(m), ...d0, ...binDec(L, n), ...lh];
}
function s0RightFacing(b) {
  return [false, true, true, true, false, false, ...d1pow(b + 1)];
}
function q4RightShape(b) {
  return [true, true, true, true, false, false, ...d1pow(b + 1)];
}

// Entry [write, moveRight, nextState], keyed by state/read-bit.
const tm2 = new Map([
  ["0,0", [true,  true,  1]],
  ["1,0", [true,  false, 2]],
  ["1,1", [false, true,  5]],
  ["2,0", [true,  true,  4]],
  ["2,1", [false, false, 3]],
  ["3,0", [false, false, 2]],
  ["3,1", [true,  true,  1]],
  ["4,0", [true,  true,  0]],
  ["4,1", [true,  true,  4]],
  ["5,0", [true,  true,  4]],
  ["5,1", [false, true,  3]],
]);
function initialConfig(L, n, m, a, z, b) {
  const tape = new Map();
  s1LeftFacing(L, n, m, a, z).forEach((bit, i) => { if (bit) tape.set(-i, true); });
  s0RightFacing(b).forEach((bit, i) => { if (bit) tape.set(1 + i, true); });
  return { tape, state: 3, head: 0 };
}
function step(c) {
  const read = c.tape.get(c.head) === true ? 1 : 0;
  const tr = tm2.get(`${c.state},${read}`);
  if (!tr) return false;
  const [write, moveRight, nextState] = tr;
  if (write) c.tape.set(c.head, true);
  else c.tape.delete(c.head);
  c.state = nextState;
  c.head += moveRight ? 1 : -1;
  return true;
}
function run(c, n) {
  for (let i = 0; i < n; i++) if (!step(c)) return false;
  return true;
}
function exactConfig(c, state, head, left, right) {
  if (c.state !== state || c.head !== head) return false;
  const expected = new Set();
  left.forEach((bit, i) => { if (bit) expected.add(head - i); });
  right.forEach((bit, i) => { if (bit) expected.add(head + 1 + i); });
  return expected.size === c.tape.size
    && [...expected].every(x => c.tape.has(x))
    && [...c.tape.keys()].every(x => expected.has(x));
}

const failures = [];
let tested = 0;
for (let q = 1; q <= 32; q++) {
  let t = 0, oddPart = q;
  while (oddPart % 2 === 0) { t++; oddPart /= 2; }
  const L = Math.max(4 + t, Math.ceil(Math.log2(8 * q + 1)));
  for (let a = 1; a <= 3; a++) {
    for (let b = 0; b <= 2; b++) {
      tested++;
      const c = initialConfig(L, 8 * q, 0, a, 0, b);
      let ok = run(c, 9 * a) && c.state === 3 && c.head === -3 * a;

      // Fixed 44-step prefix; its endpoint exposes the valuation-dependent run.
      ok = ok && run(c, 44) && c.state === 3 && c.head === -3 * a - 14;
      const branchBit = c.tape.get(c.head) === true ? 1 : 0;
      ok = ok && branchBit === (t > 0 ? 1 : 0);

      // Bubble the zero left across 3t ones: 3 steps per cell.
      ok = ok && run(c, 9 * t)
        && c.state === 3
        && c.head === -3 * a - 14 - 3 * t
        && c.tape.get(c.head) !== true;

      // Four-step zero exit, then scan 4+t d1-blocks from state 1.
      ok = ok && run(c, 4)
        && c.state === 1
        && c.head === -3 * a - 12 - 3 * t;
      ok = ok && run(c, 12 + 3 * t)
        && c.state === 1
        && c.head === -3 * a;

      // Final 101 boundary and existing E-scan back to the original head.
      ok = ok && run(c, 3)
        && c.state === 4
        && c.head === -3 * a + 3;
      ok = ok && run(c, 3 * (a - 1))
        && c.state === 4
        && c.head === 0;

      const q4Left = [
        true, ...d1pow(a - 1), ...markerWord(2), ...d0,
        ...binDec(L, 8 * q - 1), ...lh,
      ];
      ok = ok && exactConfig(c, 4, 0, q4Left, q4RightShape(b));

      // Existing q4 suffix: exact pre-drain S1 target.
      ok = ok && run(c, 39 + 3 * b);
      const targetLeft = s1LeftFacing(L, 8 * q - 1, 2, a + b + 1, 2 ** b - 1);
      ok = ok && exactConfig(c, 3, 5 + 3 * b, targetLeft, s0RightFacing(0));

      if (!ok) failures.push({ q, t, L, a, b, state: c.state, head: c.head });
    }
  }
}
const result = { tested, failures };
console.log(JSON.stringify(result, null, 2));
if (failures.length !== 0) process.exitCode = 1;
