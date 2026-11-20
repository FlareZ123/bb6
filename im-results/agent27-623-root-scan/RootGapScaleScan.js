#!/usr/bin/env node
"use strict";

// Source-faithful BigInt replay of the pinned Cryptids BB6 section map
// for M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA.
// Upstream pin: google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b
// File: BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean
// No external dependencies. Run: node RootGapScaleScan.js [transition-count].
//
// Crucial source equation:
//   A(a, 3*j+1, m) = A(a-1, j, m+2*j+3)  (a >= 1)
// so this branch must continue the A recursion; returning the intermediate
// tuple as a completed D3 state is incorrect.

const steps = Number(process.argv[2] ?? 20000);
if (!Number.isSafeInteger(steps) || steps < 1) {
  throw new Error("transition-count must be a positive safe integer");
}

const odd = x => (x & 1n) === 1n;
const abs = x => x < 0n ? -x : x;

function evalA(a, k, m) {
  for (;;) {
    const q = k / 3n;
    const r = k % 3n;

    if (r === 2n) return [true, a + 1n, q, m];

    if (a === 0n) {
      if (r === 0n) return [false];
      return [true, 0n, q, m];
    }

    if (r === 0n) return [true, a - 1n, q, m + 2n];

    // r === 1 and a > 0: recurse on A(a-1,q,m+2q+3).
    a -= 1n;
    m += 2n * q + 3n;
    k = q;
  }
}

function drainB(a, b, d) {
  while (b > 0n) {
    const oldB = b;
    const result = evalA(a, b - 1n, d + 2n * b + 3n);
    if (!result[0]) return null;
    [a, b, d] = [result[1], result[2], result[3]];
    if (b >= oldB) return null;
  }
  return [a, d];
}

function highLevelNext(a, d) {
  if (a === 0n) {
    if (odd(d)) return drainB(d + 1n, 2n, 2n);
    return [d, 7n];
  }

  if (odd(d) && a >= d + 5n) {
    return drainB(a - d - 5n, d + 3n, 5n);
  }

  if (!odd(d) && a >= d + 3n) {
    return drainB(a - d - 2n, d + 2n, 2n);
  }

  if (odd(a)) return null;
  if (a === d + 2n) return drainB(0n, a, 2n);
  if (odd(d)) return drainB(d + 4n - a, a - 1n, 3n);

  const result = evalA(d + 1n - a, a, 2n * a + 5n);
  if (!result[0]) return null;
  return drainB(result[1], result[2], result[3]);
}

function log2BigInt(n) {
  if (n === 0n) return -Infinity;
  const bits = n.toString(2).length;
  const take = Math.min(53, bits);
  const top = Number(n >> BigInt(bits - take));
  return bits - take + Math.log2(top);
}

function log2Ratio(numerator, denominator) {
  return log2BigInt(numerator) - log2BigInt(denominator);
}

const trace = [];
let a = 0n;
let d = 7n;
let mismatch = 0;
let zero = 0;

let minSlack = null;
let minSlackAt = null;
let minRelativeGap = null;
let minRelativeGapAt = null;
let minSquareGap = null;
let minSquareGapAt = null;
let maxGapError = null;
let maxGapErrorAt = null;
let maxScaleError = null;
let maxScaleErrorAt = null;

for (let i = 0; i < steps; i++) {
  if (i < 20) trace.push({index: i, a: a.toString(), d: d.toString()});

  const oldA = a;
  const oldD = d;
  const next = highLevelNext(a, d);
  if (next === null) {
    throw new Error(`halt/failed section step at index ${i}, D(${a},${d})`);
  }
  [a, d] = next;

  if (i < 9) continue;

  const m = oldA >= oldD ? oldD : oldA;
  const g = oldA >= oldD ? oldA - 4n * oldD : oldD - 4n * oldA;
  const nextM = a >= d ? d : a;
  const nextG = a >= d ? a - 4n * d : d - 4n * a;

  if (g === 0n) zero += 1;
  const predictedG = g > 0n ? g - 9n * m : -4n * g - 9n * m;
  const predictedM = g > 0n ? 3n * m : 3n * m + g;
  const gapError = nextG - predictedG;
  const scaleError = nextM - predictedM;

  if ((g > 0n) !== (a >= d)) mismatch += 1;

  const h = abs(oldA - oldD);
  // For m > 0, ceil(log_3(2*m+1)) is exactly the number of base-3
  // digits of 2*m. Thus this slack computation is integer-exact.
  const slack = h - BigInt((2n * m).toString(3).length);
  if (minSlack === null || slack < minSlack) {
    minSlack = slack;
    minSlackAt = {
      index: i,
      a: oldA.toString(),
      d: oldD.toString(),
      gap: h.toString(),
      scale: m.toString()
    };
  }

  if (m > 0n) {
    const rel = {numerator: abs(g), denominator: m};
    if (
      minRelativeGap === null ||
      rel.numerator * minRelativeGap.denominator <
        minRelativeGap.numerator * rel.denominator
    ) {
      minRelativeGap = rel;
      minRelativeGapAt = {index: i};
    }

    const square = {numerator: g * g, denominator: m};
    if (
      minSquareGap === null ||
      square.numerator * minSquareGap.denominator <
        minSquareGap.numerator * square.denominator
    ) {
      minSquareGap = square;
      minSquareGapAt = {index: i};
    }
  }

  const digits = BigInt(m === 0n ? 1 : m.toString(3).length);
  const gapErr = {numerator: abs(gapError), denominator: digits};
  if (
    maxGapError === null ||
    gapErr.numerator * maxGapError.denominator >
      maxGapError.numerator * gapErr.denominator
  ) {
    maxGapError = gapErr;
    maxGapErrorAt = {index: i, error: gapError.toString(), scale: m.toString(), ternaryDigits: digits.toString()};
  }

  const scaleErr = {numerator: abs(scaleError), denominator: digits};
  if (
    maxScaleError === null ||
    scaleErr.numerator * maxScaleError.denominator >
      maxScaleError.numerator * scaleErr.denominator
  ) {
    maxScaleError = scaleErr;
    maxScaleErrorAt = {index: i, error: scaleError.toString(), scale: m.toString(), ternaryDigits: digits.toString()};
  }
}

const output = {
  source: "pinned Lean evalA/drainB/highLevelNext equations",
  transitions: steps,
  checkedIndices: `9..${steps - 1}`,
  rootTraceFirst20: trace,
  mismatch,
  zero,
  minSlack: {
    value: minSlack.toString(),
    state: minSlackAt
  },
  minRelativeGap: {
    log2: log2Ratio(minRelativeGap.numerator, minRelativeGap.denominator),
    index: minRelativeGapAt.index
  },
  minSquareGap: {
    exact: `${minSquareGap.numerator}/${minSquareGap.denominator}`,
    log2: log2Ratio(minSquareGap.numerator, minSquareGap.denominator),
    index: minSquareGapAt.index
  },
  maxGapErrorPerTernaryDigit: {
    exact: `${maxGapError.numerator}/${maxGapError.denominator}`,
    log2: log2Ratio(maxGapError.numerator, maxGapError.denominator),
    at: maxGapErrorAt
  },
  maxScaleErrorPerTernaryDigit: {
    exact: `${maxScaleError.numerator}/${maxScaleError.denominator}`,
    log2: log2Ratio(maxScaleError.numerator, maxScaleError.denominator),
    at: maxScaleErrorAt
  }
};

console.log(JSON.stringify(output, null, 2));
