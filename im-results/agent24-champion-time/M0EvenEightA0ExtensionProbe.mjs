#!/usr/bin/env node
"use strict";

// Experimental a=0 extension probe for the M0 marker-0, n=8q source.
// The current Lean M0 q4-prefix proof still assumes a>0; this is only
// computational evidence for a possible separate a=0 prefix theorem.
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
  let p = (1n << BigInt(len + 1)) - 1n - BigInt(n);
  const out = [];
  for (let i = 0; i < len; i++) {
    if (p <= 1n) break;
    out.push(...(p % 2n === 0n ? d0 : d1));
    p /= 2n;
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

const cases = [];
for (let q = 1; q <= 32; q++) {
  const minL = Math.max(4, Math.ceil(Math.log2(8 * q + 1)));
  const t = v2(q);
  for (const L of [minL, minL + 8]) {
    for (const b of [0, 1, 2]) {
      const prefixCost = 12 * t + 99 + 3 * b;
      const drainCost = 6 * 4 ** b + 42 * 2 ** b - 12 * b - 48;
      const c = config(L, 8 * q, 0, 0, 0, b);
      if (!run(c, prefixCost)) {
        throw new Error(`prefix halted: L=${L}, q=${q}, b=${b}`);
      }
      const prefixTarget = config(L, 8 * q - 1, 2, b + 1, 2 ** b - 1, 0, 5 + 3 * b);
      if (!sameConfig(c, prefixTarget)) {
        throw new Error(`prefix mismatch: L=${L}, q=${q}, b=${b}`);
      }
      if (!run(c, drainCost)) {
        throw new Error(`drain halted: L=${L}, q=${q}, b=${b}`);
      }
      const finalTarget = config(L, 8 * q - 1, 2, b + 1, 0, 2 ** b - 1, 5 + 3 * b);
      if (!sameConfig(c, finalTarget)) {
        throw new Error(`final mismatch: L=${L}, q=${q}, b=${b}`);
      }
      cases.push({ L, q, v2: t, b, prefixCost, drainCost, total: prefixCost + drainCost });
    }
  }
}

console.log(JSON.stringify({
  tested: cases.length,
  qRange: "1..32",
  widths: "minimal admissible L and L+8",
  first: cases[0],
  last: cases[cases.length - 1],
  result: "all exact M0 a=0 prefix and counted-drain configurations matched",
}, null, 2));
