#!/usr/bin/env node
import assert from "node:assert/strict";

const mod = (x, m) => ((x % m) + m) % m;

function powMod(base, exponent, modulus) {
  let b = mod(base, modulus);
  let e = exponent;
  let out = 1n;
  while (e > 0n) {
    if (e & 1n) out = (out * b) % modulus;
    b = (b * b) % modulus;
    e >>= 1n;
  }
  return out;
}

function invMod(a, m) {
  for (let x = 1n; x < m; x++) {
    if (mod(a * x, m) === 1n) return x;
  }
  throw new Error("inverse not found");
}

function valuation3(x, precision) {
  if (x === 0n) return ">=" + precision;
  let v = 0;
  while (x % 3n === 0n) {
    v++;
    x /= 3n;
  }
  return v;
}

const P = 2n * (3n ** 13n);
const M = 3n ** 14n;
const M10 = 3n ** 10n;
const M8 = 3n ** 8n;
const M6 = 3n ** 6n;
const M5 = 3n ** 5n;
const M4 = 3n ** 4n;
const M3 = 3n ** 3n;
const M2 = 3n ** 2n;

assert.equal(P, 3188646n);
assert.equal(M, 4782969n);
assert.equal(P % 486n, 0n);
assert.equal(P / 486n, 6561n);
assert.equal(powMod(2n, P, M), 1n);

function certificate(a) {
  const kM = mod(97n * powMod(2n, a - 7n, M) + 48n, M);
  const kP = mod(97n * powMod(2n, a - 7n, P) + 48n, P);
  const rP = mod(kP - a + 4n, P);
  const p = powMod(2n, kP, M);
  const q243 = powMod(2n, mod(kP - a, 162n), 243n);
  const T = powMod(2n, rP, M);
  const B = mod((2n * kM + 7n) * T, M);

  const threeX = mod(80n * p + 2n * kM + 13n - 2n * B, M);
  assert.equal(threeX % 3n, 0n);
  const X = threeX / 3n; // X mod 3^13

  const nineX1 = mod(248n * p - 8n * B - 10n * kM + 25n, M);
  assert.equal(nineX1 % 9n, 0n);
  const X1 = nineX1 / 9n; // X1 mod 3^12

  const X2 = mod(
    16n * (X / 27n) - 4n * (p % M10) - 2n * (kM % M10) - 1n,
    M10
  ); // X2 mod 3^10

  const X3 = mod(
    8n * (X2 / 9n) - (p % M8) - 2n * (kM % M8) + 3n,
    M8
  ); // X3 mod 3^8

  const A1 = mod(p + 2n * kM - 3n, M8);
  const G1 = mod(A1 - 4n * (X2 / 9n), M8);
  const X4 = mod(A1 - 4n * G1, M8);
  const Z = [];
  for (let j = 0; j <= 4; j++) {
    Z.push(mod(A1 - powMod(2n, BigInt(j + 1), 81n) * G1, 81n));
  }
  assert.equal(X4 % 81n, Z[1]);

  const X5 = mod(
    8n * (X4 / 9n) - (p * invMod(2n, M6)) % M6 - 2n * (kM % M6) + 5n,
    M6
  ); // X5 mod 3^6

  const X6 = mod(
    4n * (X5 / 3n) - (p * invMod(4n, M5)) % M5 - 2n * (kM % M5) + 7n,
    M5
  ); // X6 mod 3^5

  const X7 = mod(
    8n * (X5 / 3n) - (3n * p * invMod(4n, M4)) % M4 - 6n * (kM % M4) + 21n,
    M4
  ); // X7 mod 3^4

  const X8 = mod(
    4n * (X7 / 3n) - (p * invMod(8n, M3)) % M3 - 2n * (kM % M3) + 9n,
    M3
  ); // X8 mod 3^3

  const X9 = mod(
    2n * X8 - (p * invMod(8n, M2)) % M2 - 2n * (kM % M2) + 9n,
    M2
  ); // X9 mod 3^2

  const X10 = mod(
    4n * (X9 / 3n) - (p * invMod(16n, 3n)) % 3n - 2n * (kM % 3n) + 11n,
    3n
  ); // X10 mod 3

  const G0Numerator = mod(
    26368n * q243 + 74n * (kM % 243n) - 23n,
    243n
  );
  assert.equal(G0Numerator % 27n, 0n);
  const G0 = G0Numerator / 27n;

  const k54 = mod(97n * powMod(2n, a - 7n, 54n) + 48n, 54n);
  const rho = mod(k54 + 6n * a, 54n);

  return {
    Kmod54: Number(k54),
    rho: Number(rho),
    X: Number(X),
    v3X: valuation3(X, 13),
    X1mod27: Number(X1 % 27n),
    X2: Number(X2),
    v3X2: valuation3(X2, 10),
    X3: Number(X3),
    v3X3: valuation3(X3, 8),
    G1: Number(G1),
    X4: Number(X4),
    v3X4: valuation3(X4, 8),
    Zmod81: Z.map(Number),
    Zvaluations: Z.map(z => valuation3(z, 4)),
    X5: Number(X5),
    v3X5: valuation3(X5, 6),
    X6: Number(X6),
    v3X6: valuation3(X6, 5),
    X7: Number(X7),
    v3X7: valuation3(X7, 4),
    X8: Number(X8),
    v3X8: valuation3(X8, 3),
    X9: Number(X9),
    v3X9: valuation3(X9, 2),
    X10: Number(X10),
    v3X10: valuation3(X10, 1),
    G0mod9: Number(G0 % 9n),
    A0mod3: Number(mod(4n * (p % 3n) + 2n * (kM % 3n) + 1n, 3n))
  };
}

const base = certificate(158n);
assert.equal(base.Kmod54, 44);
assert.equal(base.rho, 20);
assert.equal(base.X, 207684);
assert.equal(base.v3X, 4);
assert.equal(base.X1mod27, 21);
assert.equal(base.X2, 45981);
assert.equal(base.v3X2, 3);
assert.equal(base.X3, 679);
assert.equal(base.v3X3, 0);
assert.equal(base.G1, 74);
assert.equal(base.X4, 531);
assert.equal(base.v3X4, 2);
assert.deepEqual(base.Zmod81, [31, 45, 73, 48, 79]);
assert.deepEqual(base.Zvaluations, [0, 2, 0, 1, 0]);
assert.equal(base.X5, 693);
assert.equal(base.v3X5, 2);
assert.equal(base.X6, 212);
assert.equal(base.v3X6, 0);
assert.equal(base.X7, 36);
assert.equal(base.v3X7, 2);
assert.equal(base.X8, 18);
assert.equal(base.v3X8, 2);
assert.equal(base.X9, 6);
assert.equal(base.v3X9, 1);
assert.equal(base.X10, 2);
assert.equal(base.v3X10, 0);
assert.equal(base.G0mod9, 1);
assert.equal(base.A0mod3, 0);

for (let n = 1n; n <= 2n; n++) {
  assert.deepEqual(certificate(158n + n * P), base);
}

console.log(JSON.stringify({
  period: Number(P),
  modulus: Number(M),
  representative: 158,
  residues: base
}, null, 2));
