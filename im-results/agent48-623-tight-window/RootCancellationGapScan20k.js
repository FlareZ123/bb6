#!/usr/bin/env node
"use strict";

// Exact finite scan of the branch-specific cancellation terms in the
// authentic D(0,7) high-level recurrence. This is diagnostic, not a proof.

function evalA(a, k, m) {
  for (;;) {
    const q = k / 3n;
    const r = k % 3n;
    if (r === 2n) return [a + 1n, q, m];
    if (a === 0n) return r === 0n ? null : [0n, q, m];
    if (r === 0n) return [a - 1n, q, m + 2n];
    a -= 1n;
    m += 2n * q + 3n;
    k = q;
  }
}
function drainB(a, b, d) {
  while (b !== 0n) {
    const z = evalA(a, b - 1n, d + 2n * b + 3n);
    if (z === null || z[1] >= b) return null;
    [a, b, d] = z;
  }
  return [a, d];
}
function next(a, d) {
  if (a === 0n) return d % 2n === 1n ? drainB(d + 1n, 2n, 2n) : [d, 7n];
  if (d % 2n === 1n && a >= d + 5n) return drainB(a - d - 5n, d + 3n, 5n);
  if (d % 2n === 0n && a >= d + 3n) return drainB(a - d - 2n, d + 2n, 2n);
  if (a % 2n === 1n) return null;
  if (a === d + 2n) return drainB(0n, a, 2n);
  if (d % 2n === 1n) return drainB(d + 4n - a, a - 1n, 3n);
  const z = evalA(d + 1n - a, a, 2n * a + 5n);
  return z === null ? null : drainB(...z);
}
function ell3(v) {
  let ell = 0;
  let p = 1n;
  while (p <= v) { p *= 3n; ell += 1; }
  return ell;
}
function abs(x) { return x < 0n ? -x : x; }
function lessRatio(aNum, aDen, bNum, bDen) {
  return aNum * bDen < bNum * aDen;
}

function scan(steps = 20000, startIndex = 16) {
  let a = 0n;
  let d = 7n;
  const minPreGapSquareOverM = { L: null, R: null };
  const maxCorrectionPerEll = { L: null, R: null };
  const minGuaranteedNextGapSquareOverM = { L: null, R: null };
  const minPreGapPerEll = { L: null, R: null };
  let minActualGapSquareOverM = null;

  for (let i = 0; i < steps; i += 1) {
    const m = a < d ? a : d;
    const g = a >= d ? a - 4n * d : d - 4n * a;
    const branch = g > 0n ? "L" : "R";
    const z = next(a, d);
    if (z === null) throw new Error("unexpected halt at index " + i);
    const [a2, d2] = z;
    const m2 = a2 < d2 ? a2 : d2;
    const g2 = a2 >= d2 ? a2 - 4n * d2 : d2 - 4n * a2;
    const base = branch === "L" ? g - 9n * m : -4n * g - 9n * m;
    const correction = g2 - base;
    const absBase = abs(base);
    const absCorrection = abs(correction);
    const ell = ell3(2n * m + 1n);

    if (m > 0n && i >= startIndex) {
      const preNum = absBase * absBase;
      const preDen = m;
      const oldPre = minPreGapSquareOverM[branch];
      if (oldPre === null || lessRatio(preNum, preDen, oldPre.num, oldPre.den)) {
        minPreGapSquareOverM[branch] = {
          index: i, a: a.toString(), d: d.toString(), m: m.toString(),
          g: g.toString(), base: base.toString(), correction: correction.toString(),
          mNext: m2.toString(), gNext: g2.toString(), ell,
          num: preNum.toString(), den: preDen.toString(),
          floor: (preNum / preDen).toString(),
        };
      }

      const corrNum = absCorrection;
      const corrDen = BigInt(ell);
      const oldCorr = maxCorrectionPerEll[branch];
      if (oldCorr === null || lessRatio(oldCorr.num, oldCorr.den, corrNum, corrDen)) {
        maxCorrectionPerEll[branch] = {
          index: i, absCorrection: absCorrection.toString(), ell,
          num: corrNum.toString(), den: corrDen.toString(),
        };
      }

      const lowerGap = absBase > absCorrection ? absBase - absCorrection : 0n;
      const nextNum = lowerGap * lowerGap;
      const nextDen = m2;
      const oldNext = minGuaranteedNextGapSquareOverM[branch];
      if (oldNext === null || lessRatio(nextNum, nextDen, oldNext.num, oldNext.den)) {
        minGuaranteedNextGapSquareOverM[branch] = {
          index: i, lowerGap: lowerGap.toString(), mNext: m2.toString(),
          base: base.toString(), correction: correction.toString(), ell,
          num: nextNum.toString(), den: nextDen.toString(),
          floor: (nextNum / nextDen).toString(),
        };
      }

      const perNum = absBase;
      const perDen = BigInt(ell);
      const oldPer = minPreGapPerEll[branch];
      if (oldPer === null || lessRatio(perNum, perDen, oldPer.num, oldPer.den)) {
        minPreGapPerEll[branch] = {
          index: i, absBase: absBase.toString(), ell,
          num: perNum.toString(), den: perDen.toString(),
          floor: (perNum / perDen).toString(),
        };
      }

      const actualNum = g * g;
      const actualDen = m;
      if (minActualGapSquareOverM === null ||
          lessRatio(actualNum, actualDen, minActualGapSquareOverM.num, minActualGapSquareOverM.den)) {
        minActualGapSquareOverM = {
          index: i, g: g.toString(), m: m.toString(),
          num: actualNum.toString(), den: actualDen.toString(),
          floor: (actualNum / actualDen).toString(),
        };
      }
    }

    [a, d] = z;
  }

  return {
    scope: { initialState: [0, 7], transitions: steps, measuredFromIndex: startIndex },
    definitions: {
      m: "min(a,d)",
      g: "a-4d if a>=d, otherwise d-4a",
      branch: "L if g>0, otherwise R",
      leadingGap: "g-9m on L; -4g-9m on R",
      correction: "exact next g minus the branch-specific leadingGap",
      ell: "least ell with 3^ell > 2m+1",
      guaranteedNextGap: "max(0, |leadingGap|-|correction|)",
    },
    minPreGapSquareOverM,
    maxCorrectionPerEll,
    minGuaranteedNextGapSquareOverM,
    minPreGapPerEll,
    minActualGapSquareOverM,
  };
}

console.log(JSON.stringify(scan(), null, 2));
