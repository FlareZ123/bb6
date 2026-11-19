#!/usr/bin/env node
"use strict";

// Exact finite modular reproduction of the rho=20 q=0 residue table.
// No astronomical 2^K is constructed: all exponentiations are reduced
// modulo 54 or 81, which is sufficient for X mod 27 and X1 mod 9.

function mod(n, m) {
  return ((n % m) + m) % m;
}

function powMod(base, exponent, modulus) {
  let x = mod(base, modulus);
  let e = exponent;
  let out = 1n % modulus;
  while (e > 0n) {
    if (e & 1n) out = (out * x) % modulus;
    x = (x * x) % modulus;
    e >>= 1n;
  }
  return out;
}

const expected = new Map([
  [0, [54n, 27n]],
  [2, [54n, 0n]],
  [4, [54n, 54n]],
  [6, [54n, 27n]],
  [8, [27n, 54n]],
  [10, [0n, 0n]],
  [12, [54n, 27n]],
  [14, [0n, 27n]],
  [16, [27n, 27n]],
]);

const rows = [];
for (let aMod18 = 0; aMod18 < 18; aMod18 += 2) {
  let representative = null;
  for (let lift = 0; lift < 3; lift++) {
    const a = 18 + aMod18 + 18 * lift;
    const aBig = BigInt(a);
    const k0mod54 = mod(97n * powMod(2n, BigInt(a - 7), 54n) - 3n, 54n);
    const target = mod(20n - 6n * aBig, 54n);
    const delta = Number(mod(target - k0mod54, 54n));
    const expectedDelta = a % 6 === 0 ? 33 : 51;
    if (delta !== expectedDelta) {
      throw new Error(`rho=20 offset mismatch at a=${a}: ${delta}`);
    }

    const kmod54 = mod(k0mod54 + BigInt(delta), 54n);
    if (mod(kmod54 + 6n * aBig, 54n) !== 20n) {
      throw new Error(`rho=20 congruence failed at a=${a}`);
    }

    const q = BigInt(2 * delta + 1);
    const A = powMod(2n, BigInt(a - 7), 81n);
    const Cexp = mod(24n - 7n * aBig, 54n);
    const C = powMod(2n, Cexp, 81n);
    const threeX = mod(51n + 32n * A + q - 2n * q * C, 81n);
    const nineX1 = mod(33n + 2n * A - q * (8n * C + 5n), 81n);
    const want = expected.get(aMod18);
    if (threeX !== want[0] || nineX1 !== want[1]) {
      throw new Error(`modular table mismatch at a=${a}`);
    }
    const row = {
      aMod18,
      delta,
      q: q.toString(),
      threeXmod81: threeX.toString(),
      Xmod27: (threeX / 3n).toString(),
      nineX1mod81: nineX1.toString(),
      X1mod9: (nineX1 / 9n).toString(),
    };
    if (lift === 0) representative = row;
  }
  rows.push(representative);
}

const good = [0, 4, 6, 8, 12, 16];
const bad = [2, 10, 14];
console.log(JSON.stringify({ rows, goodResiduesMod18: good, excludedResiduesMod18: bad }, null, 2));
