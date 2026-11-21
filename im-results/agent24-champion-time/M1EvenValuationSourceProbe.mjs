#!/usr/bin/env node
"use strict";

// Finite end-to-end probe for the all-positive M1 valuation source draft.
// Checks both the q4 reset-prefix output and the counted-drain output.
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

function checkCase(L, n, a, b) {
  const v = v2(n);
  const prefixCost = 12 * a + 12 * v + 67 + 3 * b;
  const phaseCost = (12 * a + 12 * v + 32) + (35 + 3 * b);
  const drainCost = 6 * 4 ** b + 42 * 2 ** b - 12 * b - 48;
  if (prefixCost !== phaseCost) {
    throw new Error(`cost decomposition mismatch: n=${n}, a=${a}, b=${b}`);
  }

  const c = config(L, n, 1, a, 0, b);
  if (!run(c, prefixCost)) {
    throw new Error(`prefix halted: L=${L}, n=${n}, a=${a}, b=${b}`);
  }
  const prefixTarget = config(L, n - 1, 0, a + b + 2, 2 ** b - 1, 0, 5 + 3 * b);
  if (!sameConfig(c, prefixTarget)) {
    throw new Error(`q4 reset-prefix mismatch: L=${L}, n=${n}, a=${a}, b=${b}, state=${c.state}, head=${c.head}`);
  }

  if (!run(c, drainCost)) {
    throw new Error(`counted drain halted: L=${L}, n=${n}, a=${a}, b=${b}`);
  }
  const finalTarget = config(L, n - 1, 0, a + b + 2, 0, 2 ** b - 1, 5 + 3 * b);
  if (!sameConfig(c, finalTarget)) {
    throw new Error(`counted-increment mismatch: L=${L}, n=${n}, a=${a}, b=${b}, state=${c.state}, head=${c.head}`);
  }
  return { L, n, v2: v, a, b, prefixCost, drainCost, total: prefixCost + drainCost };
}

const cases = [];
let minWidthCases = 0;
let longTailCases = 0;
for (let n = 1; n <= 64; n++) {
  const minL = Math.max(4, Math.ceil(Math.log2(n + 1)));
  for (const L of [minL, minL + 8]) {
    for (const a of [1, 2, 3]) {
      for (const b of [0, 1, 2]) {
        cases.push(checkCase(L, n, a, b));
        if (L === minL) minWidthCases++;
        else longTailCases++;
      }
    }
  }
}

console.log(JSON.stringify({
  tested: cases.length,
  minWidthCases,
  longTailCases,
  nRange: "1..64",
  first: cases[0],
  last: cases[cases.length - 1],
  result: "all exact q4-prefix and counted-drain configurations matched",
}, null, 2));
