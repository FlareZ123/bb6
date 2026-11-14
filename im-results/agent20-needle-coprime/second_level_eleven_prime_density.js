// Exact CRT count for the second-level eleven-prime valuation sieve.
"use strict";
const BASE = 900900;
const c7 = [6, 3, 1];
const EXPECTED = 195456104794503150n;
const FULL_MODULUS = BigInt(BASE) * 19n * 29n * 37n * 61n * 67n * 79n * 101n;

function count(j) {
  let total = 0n;
  const c11 = ((9 - j) % 11 + 11) % 11;
  for (let w = 0; w < BASE; w++) {
    if (w % 4 === 0 || w % 12 === 9) continue;
    if (w % 3 === 1 && w % 7 !== c7[j % 3]) continue;
    if (w % 10 === 2 && w % 11 !== c11) continue;

    const factors = [
      [w % 18 === 3, 19n],
      [w % 28 === 18, 29n],
      [w % 36 === 7, 37n],
      [w % 60 === 35, 61n],
      [w % 66 === 5, 67n],
      [w % 39 === 9, 79n],
      [w % 100 === 18, 101n],
    ];
    let ways = 1n;
    for (const [active, p] of factors) ways *= active ? 1n : p;
    total += ways;
  }
  return total;
}

for (let j = 0; j < 33; j++) {
  if (count(j) !== EXPECTED) throw new Error("CRT mismatch at j = " + j);
}
console.log("modulus =", FULL_MODULUS.toString());
console.log("surviving residues =", EXPECTED.toString());
console.log("surviving density = 1643178686797/5035221340842");
console.log("excluded density = 3392042654045/5035221340842");
