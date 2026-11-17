#!/usr/bin/env node
// Exact Hensel selector for the one-same-level-even-reset Q branch.
// This is a reproducibility aid; the proof is in ONE-EVEN-Q-ENTRY-SELECTOR.md.

function mod(x, m) {
  return ((x % m) + m) % m;
}

function powMod(a, e, m) {
  let x = 1n;
  a %= m;
  while (e > 0n) {
    if (e & 1n) x = (x * a) % m;
    a = (a * a) % m;
    e >>= 1n;
  }
  return x;
}

function entryDepthResidue(K, k) {
  if (!Number.isSafeInteger(K) || K < 0 ||
      !Number.isSafeInteger(k) || k < 1) {
    throw new Error("Require K >= 0 and k >= 1.");
  }

  const bK = BigInt(K);
  const p = 2n ** bK;
  const A = 80n * p - 22n * bK - 23n;
  const C = 32n * (2n * bK + 7n);
  if (mod(A, 3n) !== mod(C, 3n) || mod(C, 3n) === 0n) {
    throw new Error("K must satisfy K mod 6 = 2 or 3.");
  }

  const invC = mod(C, 3n) === 1n ? 1n : 2n;
  let r = 0n;

  // Lift r_m modulo 3^m to r_(m+1) modulo 3^(m+1).
  for (let m = 0; m < k; m++) {
    const modulus = 3n ** BigInt(m + 2);
    const scale = 3n ** BigInt(m + 1);
    const residual = mod(A - C * powMod(4n, r, modulus), modulus);
    if (residual % scale !== 0n) {
      throw new Error("Hensel invariant failed.");
    }
    const digit = mod((residual / scale) * invC, 3n);
    r += digit * (3n ** BigInt(m));
    if (mod(A - C * powMod(4n, r, modulus), modulus) !== 0n) {
      throw new Error("Hensel lift failed.");
    }
  }

  return 2n * r; // the unique even j modulo 2*3^k
}

function bruteSolutions(K, k) {
  const bK = BigInt(K);
  const p = 2n ** bK;
  const A = 80n * p - 22n * bK - 23n;
  const C = 32n * (2n * bK + 7n);
  const modulus = 3n ** BigInt(k + 1);
  const count = 3n ** BigInt(k);
  const hits = [];
  for (let r = 0n; r < count; r++) {
    if (mod(A - C * powMod(4n, r, modulus), modulus) === 0n) {
      hits.push(2n * r);
    }
  }
  return hits;
}

const sampleK = [
  2, 3, 8, 9, 14, 15, 20, 21, 26,
  27, 32, 33, 38, 39, 44, 45, 50, 51
];

let checked = 0;
for (const K of sampleK) {
  for (let k = 1; k <= 5; k++) {
    const selected = entryDepthResidue(K, k);
    const hits = bruteSolutions(K, k);
    if (hits.length !== 1 || hits[0] !== selected) {
      throw new Error(`Selector mismatch at K=${K}, k=${k}.`);
    }
    checked++;
  }
}

console.log("K  j(mod 18)  j(mod 54)");
for (const K of sampleK) {
  console.log(
    String(K).padStart(2),
    String(entryDepthResidue(K, 2)).padStart(9),
    String(entryDepthResidue(K, 3)).padStart(9)
  );
}
console.log(`Exact brute-force uniqueness checks: ${checked}.`);
