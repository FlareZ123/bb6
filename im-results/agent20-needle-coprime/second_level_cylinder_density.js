// Exact CRT count for the second-level seven-prime valuation sieve.
// Run with Node.js; only integer arithmetic is used.
"use strict";

const c7 = [6, 3, 1]; // j mod 3 -> forced w mod 7
const BASE = 1260;
const EXPECTED = 166957950n;

function survivingResidues(j) {
  let total = 0n;
  let baseResidues = 0;

  for (let w = 0; w < BASE; w++) {
    // p=5 and p=13 cylinders are wholly impossible.
    if (w % 4 === 0 || w % 12 === 9) continue;

    // If 7 divides D_w, the target-specific residue is forced.
    if (w % 3 === 1 && w % 7 !== c7[j % 3]) continue;

    baseResidues++;

    // For each remaining prime, an active divisibility cylinder
    // leaves one residue; otherwise all residues remain available.
    const n11 = w % 10 === 2 ? 1n : 11n;
    const n19 = w % 18 === 3 ? 1n : 19n;
    const n29 = w % 28 === 18 ? 1n : 29n;
    const n61 = w % 60 === 35 ? 1n : 61n;
    total += n11 * n19 * n29 * n61;
  }

  return { total, baseResidues };
}

const fullModulus = BigInt(BASE) * 11n * 19n * 29n * 61n;
for (let j = 0; j < 3; j++) {
  const result = survivingResidues(j);
  if (result.total !== EXPECTED) {
    throw new Error("Unexpected CRT count for j mod 3 = " + j);
  }
  if (result.baseResidues !== 570) {
    throw new Error("Unexpected base-residue count");
  }
}

const excluded = fullModulus - EXPECTED;
console.log("modulus =", fullModulus.toString());
console.log("surviving residues =", EXPECTED.toString());
console.log("excluded residues =", excluded.toString());
console.log("surviving density = 5565265/15528282");
console.log("excluded density = 9963017/15528282");
