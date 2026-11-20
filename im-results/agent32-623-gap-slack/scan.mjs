#!/usr/bin/env node
"use strict";

/*
 * Reproducible BigInt diagnostic for the #623 accelerated root orbit.
 *
 * Source equations are transcribed from:
 *   google-deepmind/cryptids
 *   commit c86f15861709b76042998c5211c7b2f83991621b
 *   BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean
 *
 * This is an experiment, not a proof. In particular, the observed root
 * gap-slack bound is not a state-local forward invariant: D(2,12) satisfies
 * six-slack but halts after two high-level transitions.
 *
 * Run with Node.js:
 *   node im-results/agent32-623-gap-slack/scan.mjs
 */

function evalA(a, k, m) {
  while (true) {
    const r = k % 3n;
    const q = k / 3n;

    if (r === 2n) return { a: a + 1n, k: q, m };

    if (a === 0n) {
      if (r === 0n) return null;
      return { a: 0n, k: q, m };
    }

    if (r === 0n) return { a: a - 1n, k: q, m: m + 2n };

    // Lean's r=1,a>0 clause is recursive. Do not return the intermediate
    // state here: continue evaluating A(a-1, floor(k/3), m+2*floor(k/3)+3).
    a -= 1n;
    k = q;
    m += 2n * k + 3n;
  }
}

function drainB(a, b, d) {
  let iterations = 0;
  while (b > 0n) {
    if (++iterations > 100000) {
      throw new Error("drainB iteration guard exceeded");
    }
    const p = evalA(a, b - 1n, d + 2n * b + 3n);
    if (p === null || p.k >= b) return null;
    a = p.a;
    b = p.k;
    d = p.m;
  }
  return { a, d };
}

function highLevelNext(a, d) {
  if (a === 0n) {
    return d % 2n === 1n ? drainB(d + 1n, 2n, 2n) : { a: d, d: 7n };
  }
  if (d % 2n === 1n && a >= d + 5n) {
    return drainB(a - d - 5n, d + 3n, 5n);
  }
  if (d % 2n === 0n && a >= d + 3n) {
    return drainB(a - d - 2n, d + 2n, 2n);
  }
  if (a % 2n === 1n) return null;
  if (a === d + 2n) return drainB(0n, a, 2n);
  if (d % 2n === 1n) return drainB(d + 4n - a, a - 1n, 3n);

  const p = evalA(d + 1n - a, a, 2n * a + 5n);
  return p === null ? null : drainB(p.a, p.k, p.m);
}

function pow3AtLeast(k, threshold) {
  let value = 1n;
  for (let i = 0n; i < k; i++) {
    if (value >= threshold) return true;
    value *= 3n;
  }
  return value >= threshold;
}

function newAffineCone(a, d) {
  if (a === 0n || a % 2n !== 0n) return false;

  const leftOdd =
    d % 2n === 1n &&
    a >= d + 5n &&
    pow3AtLeast(a - d - 5n, 2n * (d + 3n) + 1n);

  const leftEven =
    d % 2n === 0n &&
    a >= d + 3n &&
    pow3AtLeast(a - d - 2n, 2n * (d + 2n) + 1n);

  const rightOdd =
    a <= d &&
    d % 2n === 1n &&
    pow3AtLeast(d + 4n - a, 2n * (a - 1n) + 1n);

  const rightEven =
    a <= d &&
    d % 2n === 0n &&
    pow3AtLeast(d + 1n - a, 2n * a + 3n);

  return leftOdd || leftEven || rightOdd || rightEven;
}

function ceilLog3(threshold) {
  let value = 1n;
  let exponent = 0n;
  while (value < threshold) {
    value *= 3n;
    exponent += 1n;
  }
  return exponent;
}

function uniformGapSlack(a, d) {
  const h = a >= d ? a - d : d - a;
  const m = a <= d ? a : d;
  return h - ceilLog3(2n * m + 1n);
}

function sameState(actual, expected) {
  return actual !== null &&
    actual.a === BigInt(expected[0]) &&
    actual.d === BigInt(expected[1]);
}

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

const evalARegression = evalA(8n, 1n, 9n);
assert(
  evalARegression !== null &&
    evalARegression.a === 6n &&
    evalARegression.k === 0n &&
    evalARegression.m === 14n,
  "Lean evalA r=1 recursive branch regression"
);

const expectedPrefix = [
  ["0", "7"],
  ["6", "14"],
  ["6", "31"],
  ["26", "26"],
  ["2", "83"],
  ["84", "10"],
  ["74", "38"],
  ["30", "138"],
  ["108", "101"],
  ["2", "321"],
  ["322", "10"],
  ["312", "38"],
  ["268", "138"],
  ["122", "438"],
  ["314", "385"],
  ["74", "950"],
  ["876", "235"]
];

let a = 0n;
let d = 7n;
const prefix = [];
let firstHalt = null;
let outOfConeAfterNine = [];
let minSlack = null;
let minSlackAt = null;
let maxBitLength = 0;

for (let n = 0; n < 10000; n++) {
  if (n < expectedPrefix.length) {
    prefix.push([a.toString(), d.toString()]);
  }

  if (n >= 9) {
    if (!newAffineCone(a, d)) {
      outOfConeAfterNine.push({
        n,
        a: a.toString(),
        d: d.toString()
      });
    }

    const slack = uniformGapSlack(a, d);
    if (minSlack === null || slack < minSlack) {
      minSlack = slack;
      const h = a >= d ? a - d : d - a;
      const m = a <= d ? a : d;
      minSlackAt = {
        n,
        a: a.toString(),
        d: d.toString(),
        h: h.toString(),
        m: m.toString(),
        ceilLog3: ceilLog3(2n * m + 1n).toString()
      };
    }
  }

  const bits = (a + d).toString(2).length;
  if (bits > maxBitLength) maxBitLength = bits;

  const next = highLevelNext(a, d);
  if (next === null) {
    firstHalt = n;
    break;
  }
  a = next.a;
  d = next.d;
}

assert(
  JSON.stringify(prefix) === JSON.stringify(expectedPrefix),
  "source recurrence prefix mismatch"
);
assert(firstHalt === null, "root halted within the scan window");
assert(outOfConeAfterNine.length === 0, "root left newAffineCone after n=9");
assert(minSlack === 65n, "unexpected minimum uniform gap slack");
assert(
  minSlackAt !== null &&
    minSlackAt.n === 14 &&
    minSlackAt.a === "314" &&
    minSlackAt.d === "385",
  "unexpected minimum-slack witness"
);

// Guard against mistaking the observed root property for a generic invariant.
const d210 = highLevelNext(2n, 10n);
assert(sameState(d210, ["10", "9"]), "D(2,10) counterexample mismatch");
const d212 = highLevelNext(2n, 12n);
assert(sameState(d212, ["12", "9"]), "D(2,12) first transition mismatch");
assert(highLevelNext(d212.a, d212.d) === null, "D(2,12) should halt in two steps");

console.log(JSON.stringify({
  sourceCommit: "c86f15861709b76042998c5211c7b2f83991621b",
  transitionsAttempted: 10000,
  firstHalt,
  sourcePrefix: prefix,
  outOfConeAfterNineCount: outOfConeAfterNine.length,
  minUniformGapSlack: minSlack.toString(),
  minSlackAt,
  maxStateBitLength: maxBitLength,
  genericCounterexamples: {
    d210: ["D(2,10)", "D(10,9)"],
    d212: ["D(2,12)", "D(12,9)", "none"]
  }
}, null, 2));
