#!/usr/bin/env node
"use strict";

// Finite end-to-end probe of the complete 24-class TM63 source dispatcher.
// Uses BigInt in binDec: Number loses exactness once the evolving left
// counter width exceeds 52. This probe is computational evidence only.
// TM2 transition table and S1 encoding are transcribed from the Lean sources.

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

// Exact arbitrary-width binary decoder. Do not replace BigInt with Number.
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

const nextMarker = m => (m + 2) % 3;
const nextExponent = (m, a, b) => a + b + (m % 3 === 0 ? 1 : 2);
const nextRight = b => 2 ** b - 1;
const proposedIncrementCost = (m, n, a, b) =>
  6 * 4 ** b + 42 * 2 ** b + 15 + 4 * (m % 3)
  + 12 * (a + v2(n)) - 9 * b;

function sectionResult(n, m, a, b) {
  if (n === 0) return { marker: m % 3, exponent: a, right: b, cost: 0 };
  const m1 = nextMarker(m);
  const a1 = nextExponent(m, a, b);
  const b1 = nextRight(b);
  const rest = sectionResult(n - 1, m1, a1, b1);
  return {
    ...rest,
    cost: proposedIncrementCost(m, n, a, b) + rest.cost,
  };
}

const cases = [];
const residueMarkerClasses = new Set();
let simulatedSteps = 0;

for (const n0 of [24, 48]) {
  for (const m0 of [0, 1, 2]) {
    for (const a0 of [1, 2]) {
      for (const b0 of [0, 1]) {
        for (const L of [8, 16]) {
          let n = n0;
          let m = m0;
          let a = a0;
          let b = b0;
          let h = 0;
          let totalCost = 0;
          const c = config(L, n, m, a, 0, b);

          for (let j = 0; j < n0; j++) {
            residueMarkerClasses.add(`${n % 8}:${m % 3}`);
            const stepCost = proposedIncrementCost(m, n, a, b);
            if (!run(c, stepCost)) {
              throw new Error(`halt: L=${L}, n=${n}, m=${m}, a=${a}, b=${b}`);
            }

            const m1 = nextMarker(m);
            const a1 = nextExponent(m, a, b);
            const b1 = nextRight(b);
            const h1 = h + 5 + 3 * b;
            const expected = config(L, n - 1, m1, a1, 0, b1, h1);
            if (!sameConfig(c, expected)) {
              throw new Error(`step mismatch: L=${L}, n=${n}, m=${m}, a=${a}, b=${b}`);
            }

            n--;
            m = m1;
            a = a1;
            b = b1;
            h = h1;
            totalCost += stepCost;
            simulatedSteps += stepCost;
          }

          const result = sectionResult(n0, m0, a0, b0);
          if (n !== 0 || m !== result.marker || a !== result.exponent
              || b !== result.right || totalCost !== result.cost) {
            throw new Error(`sectionResult mismatch: L=${L}, n0=${n0}, m0=${m0}, a0=${a0}, b0=${b0}`);
          }
          if (!sameConfig(c, config(L, 0, result.marker, result.exponent, 0, result.right, h))) {
            throw new Error(`terminal mismatch: L=${L}, n0=${n0}, m0=${m0}, a0=${a0}, b0=${b0}`);
          }
          cases.push({ L, n0, m0, a0, b0, totalCost, terminalHead: h });
        }
      }
    }
  }
}

if (residueMarkerClasses.size !== 24) {
  throw new Error(`expected 24 residue/marker classes, got ${residueMarkerClasses.size}`);
}

console.log(JSON.stringify({
  tested: cases.length,
  distinctResidueMarkerClasses: residueMarkerClasses.size,
  classes: [...residueMarkerClasses].sort(),
  simulatedTransitions: simulatedSteps,
  first: cases[0],
  last: cases[cases.length - 1],
  result: "all stepwise dispatcher transitions and terminal configurations matched",
}, null, 2));
