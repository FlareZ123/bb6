#!/usr/bin/env node
"use strict";

/*
  Exact arithmetic necessary condition for repeated #429 signed E/S-plus-F
  macro words. No floating-point arithmetic enters the certificate.

  This is a computational presentation of a paper-level general theorem:
  GitHub/Lean source certification of the arbitrary-repeat theorem is pending.
  The certificates do not decide the blank-start machine.
*/

function parseWord(s) {
  const tokens = s.trim().split(/[\s,;]+/).filter(Boolean);
  if (!tokens.length) throw new Error("word must contain an E or S macro");
  return tokens.map(t => {
    const m = /^(E|S)([1-9][0-9]*)$/i.exec(t);
    if (!m) throw new Error("invalid macro " + t + " (use e.g. E2,S1)");
    const j = Number(m[2]);
    if (!Number.isSafeInteger(j) || j > 4096)
      throw new Error("exponent outside exact supported range: " + m[2]);
    return { isE: m[1].toUpperCase() === "E", j };
  });
}
function coefficient(word) {
  let M = 1n, A = 0n, B = 0n, T = 0n;
  for (let i = word.length-1; i >= 0; --i) {
    const x = word[i];
    const scale = 4n ** BigInt(x.j);
    const cost = x.isE ? 4n : 10n;
    const rankCost = BigInt(3*x.j + (x.isE ? 2 : 4));
    const oldA = A, oldB = B;
    M = scale*M;
    A = 1n+scale*oldA;
    B = cost+scale*(oldA*rankCost+oldB);
    T += rankCost;
  }
  return {M,A,B,T};
}
function primitiveTypedWord(word) {
  for (let n = 1; n <= word.length; ++n) {
    if (word.length % n !== 0) continue;
    if (word.every((x,i) => x.j === word[i%n].j &&
                              x.isE === word[i%n].isE))
      return word.slice(0,n);
  }
  return word;
}
function exceedsPower(base, exponent, threshold) {
  if (exponent < 0n || base < 1n || threshold < 0n)
    throw new Error("invalid nonnegative power comparison");
  const cap = threshold + 1n;
  let prod = 1n, b = base > cap ? cap : base, n = exponent;
  while (n > 0n) {
    if (n % 2n) {
      prod *= b;
      if (prod > threshold) return true;
    }
    n /= 2n;
    if (n > 0n) {
      b *= b;
      if (b > cap) b = cap;
    }
  }
  return prod > threshold;
}
function certificate(word, halfRank, repetitions) {
  if (repetitions < 3n) throw new Error("at least 3 repetitions required");
  if (halfRank < 0n) throw new Error("half-rank must be nonnegative");
  const core = primitiveTypedWord(word);
  const copies = repetitions*BigInt(word.length/core.length);
  const {M,A,B,T} = coefficient(core);
  const H = (halfRank+2n*T)/3n;
  const heightThreshold = 2n*H;
  const denominator = M-1n;
  const numerator = A*T;
  const scaleCondition = exceedsPower(M,copies-2n,heightThreshold);
  const affineSlopeInteger = numerator % denominator === 0n;
  const affineSlopeEven = numerator % (2n*denominator) === 0n;
  return {
    originalWord: word.map(x => (x.isE ? "E" : "S")+x.j).join(","),
    primitiveTypedWord: core.map(x => (x.isE ? "E" : "S")+x.j).join(","),
    repetitionsAfterReduction: copies.toString(),
    inputHalfRank: halfRank.toString(),
    M: M.toString(), A: A.toString(), B: B.toString(),
    T: T.toString(), heightBound: H.toString(),
    scaleCondition,
    affineSlopeInteger,
    affineSlopeEven,
    excludedByExactNecessaryCondition: scaleCondition && !affineSlopeEven,
    reason: scaleCondition && !affineSlopeEven ?
      "A legal repeat would force an even integer s with (M-1)*s=A*T, impossible." :
      "The necessary-condition test is inconclusive; this does NOT certify a repeat or an infinite path."
  };
}
if (require.main === module) {
  try {
    if (process.argv.length !== 5)
      throw new Error("usage: node FinitePowerPruner.cjs E2,S1 <half-rank> <repetitions>");
    const word = parseWord(process.argv[2]);
    const halfRank = BigInt(process.argv[3]);
    const repetitions = BigInt(process.argv[4]);
    console.log(JSON.stringify(certificate(word,halfRank,repetitions),null,2));
  } catch(e) {
    console.error(e.message);
    process.exitCode = 1;
  }
}
module.exports = {parseWord,coefficient,primitiveTypedWord,exceedsPower,certificate};
