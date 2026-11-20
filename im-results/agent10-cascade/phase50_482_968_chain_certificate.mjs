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

  const X = mod(80n * p + 2n * kM + 13n - 2n * B, M) / 3n;
  const X1 = mod(248n * p - 8n * B - 10n * kM + 25n, M) / 9n;
  const X2 = mod(
    16n * (X / 27n) - 4n * (p % M10) - 2n * (kM % M10) - 1n,
    M10
  );
  const X3 = mod(
    8n * (X2 / 9n) - (p % M8) - 2n * (kM % M8) + 3n,
    M8
  );

  const A1 = mod(p + 2n * kM - 3n, M8);
  const G1 = mod(A1 - 4n * (X2 / 9n), M8);
  const Z = [];
  for (let j = 0; j <= 4; j++) {
    Z.push(mod(A1 - powMod(2n, BigInt(j + 1), M8) * G1, M8));
  }

  const W0 = mod(
    8n * (X3 / 9n) - (p * invMod(2n, M6)) % M6 - 2n * (kM % M6) + 5n,
    M6
  );
  const W1 = mod(
    4n * (W0 / 3n) - (p * invMod(4n, M5)) % M5 - 2n * (kM % M5) + 7n,
    M5
  );
  const W2 = mod(
    8n * (W0 / 3n) - (3n * p * invMod(4n, M4)) % M4 - 6n * (kM % M4) + 21n,
    M4
  );
  const W3 = mod(
    16n * (W0 / 3n) - (7n * p * invMod(4n, M3)) % M3 - 14n * (kM % M3) + 49n,
    M3
  );
  const W4 = mod(
    32n * (W0 / 3n) - (15n * p * invMod(4n, M2)) % M2 - 30n * (kM % M2) + 105n,
    M2
  );
  const W5 = mod(
    8n * (W1 / 9n) - (p * invMod(8n, 3n)) % 3n - 2n * (kM % 3n) + 9n,
    3n
  );
  const V4 = mod(
    4n * (Z[4] / 3n) - (p * invMod(2n, M6)) % M6 - 2n * (kM % M6) + 5n,
    M6
  );

  const G0Numerator = mod(
    26368n * q243 + 74n * (kM % 243n) - 23n,
    243n
  );
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
    A1: Number(A1),
    G1: Number(G1),
    Zmod3_8: Z.map(Number),
    Zvaluations: Z.map(z => valuation3(z, 8)),
    W0: Number(W0),
    v3W0: valuation3(W0, 6),
    W1: Number(W1),
    v3W1: valuation3(W1, 5),
    W2: Number(W2),
    v3W2: valuation3(W2, 4),
    W3: Number(W3),
    v3W3: valuation3(W3, 3),
    W4: Number(W4),
    v3W4: valuation3(W4, 2),
    W5: Number(W5),
    v3W5: valuation3(W5, 1),
    V4: Number(V4),
    v3V4: valuation3(V4, 6),
    G0mod9: Number(G0 % 9n),
    A0mod3: Number(mod(4n * (p % 3n) + 2n * (kM % 3n) + 1n, 3n))
  };
}

const base = certificate(968n);
assert.equal(base.Kmod54, 44);
assert.equal(base.rho, 20);
assert.equal(base.X, 141588);
assert.equal(base.v3X, 4);
assert.equal(base.X1mod27, 21);
assert.equal(base.X2, 18720);
assert.equal(base.v3X2, 2);
assert.equal(base.X3, 5850);
assert.equal(base.v3X3, 2);
assert.equal(base.A1, 4229);
assert.equal(base.G1, 2470);
assert.deepEqual(base.Zmod3_8, [5850, 910, 4152, 4075, 3921]);
assert.deepEqual(base.Zvaluations, [2, 0, 1, 0, 1]);
assert.equal(base.W0, 561);
assert.equal(base.v3W0, 1);
assert.equal(base.W1, 36);
assert.equal(base.v3W1, 2);
assert.equal(base.W2, 8);
assert.equal(base.v3W2, 0);
assert.equal(base.W3, 6);
assert.equal(base.v3W3, 1);
assert.equal(base.W4, 2);
assert.equal(base.v3W4, 0);
assert.equal(base.W5, 2);
assert.equal(base.v3W5, 0);
assert.equal(base.V4, 589);
assert.equal(base.v3V4, 0);
assert.equal(base.G0mod9, 1);
assert.equal(base.A0mod3, 0);

for (let n = 1n; n <= 2n; n++) {
  assert.deepEqual(certificate(968n + n * P), base);
}

console.log(JSON.stringify({
  period: Number(P),
  modulus: Number(M),
  representative: 968,
  residues: base
}, null, 2));
