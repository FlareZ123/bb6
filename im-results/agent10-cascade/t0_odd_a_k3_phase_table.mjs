#!/usr/bin/env node
// Exact finite check of the 9x9 phase table in T0-K3-ODD-A-SEVEN-OF-NINE.md.
// This checks the modular table only; the infinite interval and ResetParent
// arguments are proved separately in that note.

const mod = (x, m) => ((x % m) + m) % m;

function pow2Mod(exponent, modulus) {
  let e = BigInt(exponent);
  const m = BigInt(modulus);
  let base = 2n % m;
  let value = 1n;
  while (e > 0n) {
    if (e & 1n) value = (value * base) % m;
    base = (base * base) % m;
    e >>= 1n;
  }
  return Number(value);
}

const aResidues = Array.from({ length: 9 }, (_, i) => 2 * i + 1);
const kResidues = Array.from({ length: 9 }, (_, i) => 3 + 6 * i);
const rows = [];

for (const a of aResidues) {
  const values = [];
  for (const K of kResidues) {
    const p27 = pow2Mod(mod(K, 18), 27);
    const b27 = mod(
      (2 * K + 7) * pow2Mod(mod(K + 4 - a, 18), 27),
      27
    );
    const numerator27 = mod(80 * p27 + 2 * K + 13 - 2 * b27, 27);
    if (numerator27 % 3 !== 0) {
      throw new Error("The numerator in (7) was not divisible by 3.");
    }
    values.push(numerator27 / 3);
  }

  const sorted = [...values].sort((x, y) => x - y);
  if (sorted.some((x, i) => x !== i)) {
    throw new Error("A row is not a permutation of 0,...,8.");
  }

  const exceptional = [
    [0, mod(12 - 3 * a, 54)],
    [3, mod(48 - 3 * a, 54)],
    [6, mod(30 - 3 * a, 54)]
  ];
  for (const [x, K] of exceptional) {
    const index = kResidues.indexOf(K);
    if (index < 0 || values[index] !== x) {
      throw new Error("An exceptional congruence in (8) failed.");
    }
  }

  rows.push({ a, values });
}

console.log("K mod 54: " + kResidues.join(" "));
for (const row of rows) {
  console.log(String(row.a).padStart(2) + "         " + row.values.join(" "));
}
console.log("PASS: all 81 residues, divisibility, row permutations, and exceptional classes.");
