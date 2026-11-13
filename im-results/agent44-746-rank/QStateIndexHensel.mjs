#!/usr/bin/env node
"use strict";

// Exact modular specialization of QStateIndexHensel at s=5, j=3402.
// It checks that qIndexResidue(5,3402,7+s), converted through
// h=147+2187*r, reproduces Agent 7's fixed-depth U-index Hensel roots.

function mod(a, m) {
  const r = a % m;
  return r < 0n ? r + m : r;
}

function powMod(a, e, m) {
  let x = mod(a, m);
  let y = 1n;
  while (e > 0n) {
    if ((e & 1n) !== 0n) y = y * x % m;
    x = x * x % m;
    e >>= 1n;
  }
  return y;
}

function qMod(n, j, precision) {
  const m = 3n ** BigInt(precision);
  return mod(
    28n * powMod(2n, n, m) - 2n * n + 15n
      - powMod(2n, j + 4n, m) * (2n * n + 3n),
    m
  );
}

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

const expectedRho = [
  0n, 1n, 4n, 4n, 4n, 85n, 328n,
  328n, 2515n, 15637n, 35320n, 94369n
];

const s = 5n;
const j = 3402n;
let h = 0n;
const hRoots = [{ precision: 0, residue: "0", modulus: "1" }];
const familyRoots = [{ s: 0, rho: "0", modulus: "1" }];

for (let k = 1; k <= 18; k++) {
  const step = 3n ** BigInt(k - 1);
  const modulus = 3n ** BigInt(k);
  const targetModulus = 3n ** BigInt(k + 1);
  const hits = [];

  for (let digit = 0n; digit < 3n; digit++) {
    const candidate = h + digit * step;
    const n = s + 6n * candidate;
    if (qMod(n, j, k + 1) === 0n) hits.push(candidate);
  }

  assert(hits.length === 1,
    `precision ${k}: expected one lift, found ${hits.length}`);
  h = hits[0];
  hRoots.push({
    precision: k,
    residue: h.toString(),
    modulus: modulus.toString()
  });

  if (k >= 7) {
    const familyPrecision = k - 7;
    assert(h >= 147n && (h - 147n) % 2187n === 0n,
      `precision ${k}: h residue does not descend to r`);
    const rho = mod((h - 147n) / 2187n,
      3n ** BigInt(familyPrecision));
    familyRoots.push({
      s: familyPrecision,
      rho: rho.toString(),
      modulus: (3n ** BigInt(familyPrecision)).toString()
    });
  }
}

assert(familyRoots.length === expectedRho.length,
  "unexpected number of family residues");
for (let i = 0; i < expectedRho.length; i++) {
  assert(BigInt(familyRoots[i].rho) === expectedRho[i],
    `rho_${i}: expected ${expectedRho[i]}, got ${familyRoots[i].rho}`);
}

const coefficientDirect = 4n * (1n + 2n ** (j + 4n));
const coefficientSigned = 32n * (2n ** (j + 1n) - 1n);
assert(coefficientDirect - coefficientSigned === 36n,
  "direct and signedZ coefficients should differ by 36");
assert(coefficientDirect % 3n === 2n && coefficientSigned % 3n === 2n,
  "both coefficients should be units congruent to 2 modulo 3");

console.log(JSON.stringify({
  sector: 5,
  depth: 3402,
  family: "n=887+13122*r=5+6*(147+2187*r)",
  hRoots,
  familyRoots,
  coefficientDirect: coefficientDirect.toString(),
  coefficientSigned: coefficientSigned.toString()
}, null, 2));
