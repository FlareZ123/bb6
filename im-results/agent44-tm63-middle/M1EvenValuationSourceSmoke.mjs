#!/usr/bin/env node
"use strict";

/*
 * Finite independent smoke test for
 *   m1EvenValuation_reset_prefix_source
 * in M1EvenValuationSource.lean.
 *
 * The transition table is copied from ChampionRootBridge.tm2.
 * The head-facing S1 lists are copied from S1Encoder.s1Config,
 * s1LeftFacing, s0RightFacing, binDec, d0, d1, markerWord, and lh.
 *
 * This checks only the finite grid below. It is not a proof, does not
 * replace Lean 4.36.0-rc2 compilation, and says nothing about all parameters.
 */

const TM2 = {
  "0,0": [1, 1, 1], "0,1": null,
  "1,0": [1, 0, 2], "1,1": [0, 1, 5],
  "2,0": [1, 1, 4], "2,1": [0, 0, 3],
  "3,0": [0, 0, 2], "3,1": [1, 1, 1],
  "4,0": [1, 1, 0], "4,1": [1, 1, 4],
  "5,0": [1, 1, 4], "5,1": [0, 1, 3],
};

const d0 = [0, 0, 1];
const d1 = [1, 1, 1];
const lh = [1, 1, 0, 1, 1, 1];

function markerWord(m) {
  return m % 3 === 0 ? [0, 1] : m % 3 === 1 ? [1, 0, 1] : [1, 1, 0, 1];
}

function repeat(xs, n) {
  return Array.from({ length: xs.length * n }, (_, i) => xs[i % xs.length]);
}

function binaryCounterFuel(fuel, p) {
  const out = [];
  for (let i = 0; i < fuel && p > 1; i++) {
    if (p % 2 === 0) {
      out.push(...d0);
      p = Math.floor(p / 2);
    } else {
      out.push(...d1);
      p = Math.floor(p / 2);
    }
  }
  return out;
}

function binDec(len, n) {
  return binaryCounterFuel(len, 2 ** (len + 1) - 1 - n);
}

/* Exact finite support of S1Encoder.s1Config L n m a z b h. */
function s1TapeOnes(L, n, m, a, z, b, h) {
  const left = [
    ...binDec(a, z),
    ...markerWord(m),
    ...d0,
    ...binDec(L, n),
    ...lh,
  ];
  const right = [0, 1, 1, 1, 0, 0, ...repeat(d1, b + 1)];
  const ones = new Set();
  left.forEach((bit, i) => { if (bit) ones.add(h - i); });
  right.forEach((bit, i) => { if (bit) ones.add(h + 1 + i); });
  return ones;
}

function run(ones0, state0, head0, steps) {
  const ones = new Set(ones0);
  let state = state0;
  let head = head0;

  for (let k = 0; k < steps; k++) {
    const transition = TM2[`${state},${ones.has(head) ? 1 : 0}`];
    if (transition === null || transition === undefined) {
      return { state, head, ones, haltedAt: k };
    }
    const [write, right, next] = transition;
    if (write) ones.add(head);
    else ones.delete(head);
    head += right ? 1 : -1;
    state = next;
  }
  return { state, head, ones };
}

function checkCase(len, q, v, a, b) {
  const n = (2 * q + 1) * 2 ** v;
  const L = len + 1 + v;
  const start = s1TapeOnes(L, n, 1, a, 0, b, 0);
  const steps = 12 * a + 12 * v + 67 + 3 * b;
  const actual = run(start, 3, 0, steps);

  // Parameter order is s1Config L n marker a z b head.
  const targetHead = 5 + 3 * b;
  const expected = s1TapeOnes(L, n - 1, 0, a + b + 2, 2 ** b - 1, 0, targetHead);

  const radius = Math.max(steps + 20, 100);
  const mismatches = [];
  for (let x = -radius; x <= radius; x++) {
    if (actual.ones.has(x) !== expected.has(x)) mismatches.push(x);
  }

  return {
    ok: actual.haltedAt === undefined
      && actual.state === 3
      && actual.head === targetHead
      && mismatches.length === 0,
    len, q, v, a, b, steps,
    finalState: actual.state,
    finalHead: actual.head,
    haltedAt: actual.haltedAt,
    mismatches,
  };
}

const failures = [];
let tests = 0;
for (let len = 1; len <= 3; len++) {
  for (let q = 0; q < 2 ** len; q++) {
    for (let v = 0; v <= 2; v++) {
      for (let a = 1; a <= 2; a++) {
        for (let b = 0; b <= 2; b++) {
          tests++;
          const result = checkCase(len, q, v, a, b);
          if (!result.ok) failures.push(result);
        }
      }
    }
  }
}

const report = { tests, failures: failures.length, examples: failures.slice(0, 10) };
console.log(JSON.stringify(report, null, 2));
if (failures.length !== 0) process.exitCode = 1;
