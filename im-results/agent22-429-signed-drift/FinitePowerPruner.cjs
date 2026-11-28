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
// For a legal signed pair with exponent j, the next pair type flips
// iff j is odd. The rank increment is 2*(3*j+2) or 2*(3*j+4),
// and the two pair types have disjoint combined-rank classes mod 4.
function typedGuardCompatible(word) {
  let expected = word[0].isE;
  for (const x of word) {
    if (x.isE !== expected) return false;
    if (x.j % 2) expected = !expected;
  }
  // The word is repeated at least twice, so its exit must admit the
  // identical first type again.
  return expected === word[0].isE;
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
  if (repetitions < 2n) throw new Error("at least 2 repetitions required");
  if (halfRank < 0n) throw new Error("half-rank must be nonnegative");
  const typeCompatible = typedGuardCompatible(word);
  const core = primitiveTypedWord(word);
  const copies = repetitions*BigInt(word.length/core.length);
  const {M,A,B,T} = coefficient(core);
  const H0 = halfRank/3n, H1 = (halfRank+T)/3n;
  const H2 = (halfRank+2n*T)/3n;
  const numerator = A*T, denominator = M-1n;
  // For W W: AT = M*(u2-u1)+(u0-u1), so its residue modulo M
  // must come from the interval [-H1,H0].
  const squareResidue = numerator % M;
  const squareExcluded = squareResidue > H0 && M-squareResidue > H1;
  // For W W W: the third W's initial symbol fixes parity of u2 as
  // well, so (u2-u1) is even and the modulus strengthens to 2M.
  const tripleModulus = 2n*M;
  const tripleResidue = numerator % tripleModulus;
  const tripleResidueExcluded =
    copies >= 3n && tripleResidue > H0 && tripleModulus-tripleResidue > H1;
  const scaleCondition = copies >= 3n &&
    exceedsPower(M,copies-2n,2n*H2);
  const affineSlopeInteger = numerator % denominator === 0n;
  const affineSlopeEven = numerator % (2n*denominator) === 0n;
  const powerExcluded = scaleCondition && !affineSlopeEven;
  const excluded = !typeCompatible || squareExcluded || tripleResidueExcluded || powerExcluded;
  return {
    originalWord: word.map(x => (x.isE ? "E" : "S")+x.j).join(","),
    primitiveTypedWord: core.map(x => (x.isE ? "E" : "S")+x.j).join(","),
    repetitionsAfterReduction: copies.toString(),
    inputHalfRank: halfRank.toString(),
    M: M.toString(), A: A.toString(), B: B.toString(),
    T: T.toString(), heightBound: H2.toString(),
    sourceTypeCycleCompatible: typeCompatible,
    squareResidue: squareResidue.toString(),
    squareModuloExclusion: squareExcluded,
    tripleResidue: tripleResidue.toString(),
    tripleModuloExclusion: tripleResidueExcluded,
    scaleCondition, affineSlopeInteger, affineSlopeEven,
    finitePowerExclusion: powerExcluded,
    excludedByExactNecessaryCondition: excluded,
    reason: excluded ?
      "At least one exact signed type or arithmetic condition fails; the specified repeated word cannot occur." :
      "All necessary-condition tests are inconclusive; this does NOT certify a repeat or an infinite path."
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
module.exports = {parseWord,coefficient,primitiveTypedWord,typedGuardCompatible,exceedsPower,certificate};
