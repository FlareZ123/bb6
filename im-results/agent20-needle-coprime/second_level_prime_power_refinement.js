// Conditional 11^2 refinement of the second-level valuation sieve.
// Run with Node.js; all counting is exact integer arithmetic.
"use strict";

const c7 = [6, 3, 1];
const BASE = 152460;
const FULL_MODULUS = BigInt(BASE) * 19n * 29n * 61n * 67n;
const BASELINE = 118427708850n;
const REFINED = 117544794240n;

function mod(n, m) {
  return ((n % m) + m) % m;
}

function count(j) {
  let total = 0n;
  const c11 = mod(9 - j, 11);

  for (let w = 0; w < BASE; w++) {
    if (w % 4 === 0 || w % 12 === 9) continue;
    if (w % 3 === 1 && w % 7 !== c7[j % 3]) continue;
    if (w % 10 === 2 && w % 11 !== c11) continue;

    // The 121-cylinder is w = 32 (mod 110).
    // It is already rejected by the 11-filter unless j = 10 (mod 11).
    if (w % 110 === 32) {
      if (j % 11 !== 10) continue;
      const t = (j - 10) / 11;
      const c121 = mod(76 - 11 * t, 121);
      if (w % 121 !== c121) continue;
    }

    const n19 = w % 18 === 3 ? 1n : 19n;
    const n29 = w % 28 === 18 ? 1n : 29n;
    const n61 = w % 60 === 35 ? 1n : 61n;
    const n67 = w % 66 === 5 ? 1n : 67n;
    total += n19 * n29 * n61 * n67;
  }
  return total;
}

for (let j = 0; j < 121; j++) {
  const expected = j % 11 === 10 ? REFINED : BASELINE;
  if (count(j) !== expected) {
    throw new Error("Unexpected 11^2 CRT count at j = " + j);
  }
}

console.log("modulus =", FULL_MODULUS.toString());
console.log("baseline count =", BASELINE.toString());
console.log("j = 10 (mod 11) refined count =", REFINED.toString());
console.log("baseline density = 5883145/17055654");
console.log("refined density = 32116064/93806097");
