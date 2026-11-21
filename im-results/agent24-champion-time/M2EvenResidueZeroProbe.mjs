#!/usr/bin/env node
"use strict";

// Finite end-to-end simulator probe for the all-q M2, n=8*k source draft.
// This is computational evidence only, not a Lean proof.
// Transition table is transcribed from ChampionRootBridge.lean.
// Tape maps store only nonblank (true) cells.

const d0 = [false, false, true];
const d1 = [true, true, true];
const lh = [true, false, true, true, true, true];
const d1pow = n => Array.from({ length: n }, () => d1).flat();

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

function leftWord(L, n, m, a, z) {
  return [...binDec(a, z), ...markerWord(m), ...d0, ...binDec(L, n), ...lh];
}

function rightWord(b) {
  return [false, true, true, true, false, false, ...d1pow(b + 1)];
}

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

function config(L, n, m, a, z, b, h = 0) {
  const tape = new Map();
  leftWord(L, n, m, a, z).forEach((bit, i) => {
    if (bit) tape.set(h - i, true);
  });
  rightWord(b).forEach((bit, i) => {
    if (bit) tape.set(h + 1 + i, true);
  });
  return { tape, state: 3, head: h };
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

function run(c, steps) {
  for (let i = 0; i < steps; i++) {
    if (!step(c)) return false;
  }
  return true;
}

function sameConfig(actual, expected) {
  return actual.state === expected.state
    && actual.head === expected.head
    && actual.tape.size === expected.tape.size
    && [...actual.tape.keys()].every(x => expected.tape.has(x));
}

function v2(n) {
  let t = 0;
  while (n % 2 === 0) {
    t++;
    n /= 2;
  }
  return t;
}

function checkCase(L, k, a, b) {
  const t = v2(k);
  const prefixCost = 12 * a + 12 * t + 107 + 3 * b;
  const phaseCost = (9 * a + 6) + (44 + (12 * t + 4) + 14)
    + 3 * a + (39 + 3 * b);
  const drainCost = 6 * 4 ** b + 42 * 2 ** b - 12 * b - 48;
  if (prefixCost !== phaseCost) {
    throw new Error(`cost decomposition mismatch: k=${k}, a=${a}, b=${b}`);
  }

  const c = config(L, 8 * k, 2, a, 0, b);
  if (!run(c, prefixCost)) {
    throw new Error(`prefix halted: L=${L}, k=${k}, a=${a}, b=${b}`);
  }
  const prefixTarget = config(L, 8 * k - 1, 1, a + b + 2, 2 ** b - 1, 0, 5 + 3 * b);
  if (!sameConfig(c, prefixTarget)) {
    throw new Error(`q4 reset-prefix mismatch: L=${L}, k=${k}, a=${a}, b=${b}, state=${c.state}, head=${c.head}`);
  }

  if (!run(c, drainCost)) {
    throw new Error(`counted drain halted: L=${L}, k=${k}, a=${a}, b=${b}`);
  }
  const finalTarget = config(L, 8 * k - 1, 1, a + b + 2, 0, 2 ** b - 1, 5 + 3 * b);
  if (!sameConfig(c, finalTarget)) {
    throw new Error(`counted-increment mismatch: L=${L}, k=${k}, a=${a}, b=${b}, state=${c.state}, head=${c.head}`);
  }
  return { L, k, v2: t, a, b, prefixCost, drainCost, total: prefixCost + drainCost };
}

const cases = [];
for (let k = 1; k <= 16; k++) {
  const minL = Math.max(4, Math.ceil(Math.log2(8 * k + 1)));
  // The second width adds eight complete binary counter blocks, checking
  // that the source tail is genuinely arbitrary rather than near-empty.
  for (const L of [minL, minL + 8]) {
    for (const a of [1, 2, 3]) {
      for (const b of [0, 1, 2]) {
        cases.push(checkCase(L, k, a, b));
      }
    }
  }
}

// Experimental a=0 extension. The current Lean theorem still assumes a>0;
// this grid is only evidence for removing the unused prefix hypothesis and
// replacing the counted wrapper's resetDrainBound with resetDrainBound_any.
const a0ExtensionCases = [];
for (let k = 1; k <= 16; k++) {
  const minL = Math.max(4, Math.ceil(Math.log2(8 * k + 1)));
  for (const L of [minL, minL + 8]) {
    for (const b of [0, 1, 2]) {
      a0ExtensionCases.push(checkCase(L, k, 0, b));
    }
  }
}

console.log(JSON.stringify({
  tested: cases.length,
  a0ExtensionCases: a0ExtensionCases.length,
  totalCases: cases.length + a0ExtensionCases.length,
  widths: "minimal admissible L and L+8",
  first: cases[0],
  last: cases[cases.length - 1],
  result: "all exact prefix and counted-drain configurations matched",
}, null, 2));
