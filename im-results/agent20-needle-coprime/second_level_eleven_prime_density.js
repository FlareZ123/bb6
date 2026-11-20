// Exact CRT count for second-level cancellation parents, including the odd-block history filter.
// The base modulus 900900 already contains 13 (through the denominator cylinder mod 39).
// Therefore the p=13 forced residue is checked directly below; 13 is NOT an extra CRT factor.
"use strict";

const BASE = 900900;
const C7 = [6, 3, 1];
const EXPECTED_TOTAL = 218715580637067540n;
const EXPECTED_ODD_EXIT = 24224993268961368n;
const FULL_MODULUS = BigInt(BASE) * 19n * 29n * 37n * 61n * 67n * 79n * 101n;
const EXTRA_CYLINDERS = [
  [18, 3, 19n],
  [28, 18, 29n],
  [36, 7, 37n],
  [60, 35, 61n],
  [66, 5, 67n],
  [39, 9, 79n],
  [100, 18, 101n],
];
const ODD_EXIT_CLASSES = new Set([1, 2, 15]);
const byJ33AndW100 = Array.from({ length: 33 }, () => Array.from({ length: 100 }, () => 0n));

for (let j33 = 0; j33 < 33; j33++) {
  const c11 = ((9 - j33) % 11 + 11) % 11;
  let total = 0n;
  for (let w = 0; w < BASE; w++) {
    if (w % 4 === 0 && w % 5 !== 4) continue;
    if (w % 3 === 1 && w % 7 !== C7[j33 % 3]) continue;
    if (w % 10 === 2 && w % 11 !== c11) continue;
    // p=13: w = 9 (mod 12) forces w = 12 (mod 13).
    // Since 13 divides BASE, this is a direct base-residue filter, not an extra CRT factor.
    if (w % 12 === 9 && w % 13 !== 12) continue;

    let ways = 1n;
    for (const [modulus, residue, prime] of EXTRA_CYLINDERS) {
      if (w % modulus !== residue) ways *= prime;
    }
    total += ways;
    byJ33AndW100[j33][w % 100] += ways;
  }
  if (total !== EXPECTED_TOTAL) throw new Error(`eleven-prime CRT mismatch at j mod 33 = ${j33}: ${total}`);
}

// The odd-block condition depends on j mod 5, while the prime sieve depends on j mod 33.
// Check their full combined period lcm(5,33)=165.
for (let j = 0; j < 165; j++) {
  const special = ((64 - 40 * (j % 5)) % 100 + 100) % 100;
  let oddExit = 0n;
  for (let residue = 0; residue < 100; residue++) {
    if (ODD_EXIT_CLASSES.has(residue % 20) || residue === special) {
      oddExit += byJ33AndW100[j % 33][residue];
    }
  }
  if (oddExit !== EXPECTED_ODD_EXIT) throw new Error(`odd-block CRT mismatch at j = ${j}: ${oddExit}`);
}

console.log("full modulus =", FULL_MODULUS.toString());
console.log("eleven-prime survivors =", EXPECTED_TOTAL.toString());
console.log("eleven-prime density = 4596796566563/12588053352105");
console.log("odd-block-exit candidates =", EXPECTED_ODD_EXIT.toString());
console.log("odd-block-exit density = 25205067098/623170958025");
console.log("odd-block-exit share of eleven-prime survivors = 2545711776898/22983982832815");
