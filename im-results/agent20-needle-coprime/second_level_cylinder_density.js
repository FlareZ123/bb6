// Exact CRT count for the second-level eight-prime valuation sieve.
// Run with Node.js; only integer arithmetic is used.
"use strict";

const c7 = [6, 3, 1]; // j mod 3 -> forced w mod 7
const BASE = 13860;
const EXPECTED = 156230856990n;

function survivingResidues(j) {
  let total = 0n;
  let baseResidues = 0;
  const c11 = ((9 - j) % 11 + 11) % 11;

  for (let w = 0; w < BASE; w++) {
    // p=5 forces w = 4 (mod 5) on w = 0 (mod 4); p=13 forces w = 12 (mod 13) on w = 9 (mod 12).
    if (w % 4 === 0 && w % 5 !== 4) continue;

    // Apply the forced residues when p=7 or p=11 divides D_w.
    if (w % 3 === 1 && w % 7 !== c7[j % 3]) continue;
    if (w % 10 === 2 && w % 11 !== c11) continue;

    baseResidues++;

    // For each remaining prime, an active divisibility cylinder
    // leaves one residue; otherwise all residues remain available.
    const n13 = w % 12 === 9 ? 1n : 13n;
    const n19 = w % 18 === 3 ? 1n : 19n;
    const n29 = w % 28 === 18 ? 1n : 29n;
    const n61 = w % 60 === 35 ? 1n : 61n;
    const n67 = w % 66 === 5 ? 1n : 67n;
    total += n13 * n19 * n29 * n61 * n67;
  }

  return { total, baseResidues };
}

const fullModulus = BigInt(BASE) * 13n * 19n * 29n * 61n * 67n;
for (let j = 0; j < 33; j++) {
  const result = survivingResidues(j);
  if (result.total !== EXPECTED) {
    throw new Error("Unexpected CRT count for j mod 33 = " + j);
  }
  if (result.baseResidues !== 7470) {
    throw new Error("Unexpected base-residue count");
  }
}

const excluded = fullModulus - EXPECTED;
console.log("modulus =", fullModulus.toString());
console.log("surviving residues =", EXPECTED.toString());
console.log("excluded residues =", excluded.toString());
console.log("surviving density = 2189027/5685218");
console.log("excluded density = 3496191/5685218");
