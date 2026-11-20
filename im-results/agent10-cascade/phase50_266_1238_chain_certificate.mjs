#!/usr/bin/env node
import assert from "node:assert/strict";

const mod = (x, m) => ((x % m) + m) % m;
function powMod(b, e, m) {
  let r = 1n;
  b = mod(b, m);
  while (e > 0n) {
    if (e & 1n) r = r * b % m;
    b = b * b % m;
    e >>= 1n;
  }
  return r;
}
function inv(a, m) {
  for (let x = 1n; x < m; x++) if (mod(a * x, m) === 1n) return x;
  throw new Error("inverse not found");
}
function v3(x, n) {
  if (x === 0n) return ">=" + n;
  let v = 0;
  while (x % 3n === 0n) { v++; x /= 3n; }
  return v;
}

const P = 2n * 3n ** 13n;
const M = 3n ** 14n;
const M13 = 3n ** 13n;
const M10 = 3n ** 10n;
const M7 = 3n ** 7n;
const M6 = 3n ** 6n;
assert.equal(P, 3188646n);
assert.equal(M, 4782969n);
assert.equal(P % 486n, 0n);
assert.equal(P / 486n, 6561n);
assert.equal(powMod(2n, P, M), 1n);

function certificate(a) {
  const kM = mod(97n * powMod(2n, a - 7n, M) + 48n, M);
  const kP = mod(97n * powMod(2n, a - 7n, P) + 48n, P);
  const p = powMod(2n, kP, M);
  const r = mod(kP - a + 4n, P);
  const B = mod((2n * kM + 7n) * powMod(2n, r, M), M);
  const X = mod(80n * p + 2n * kM + 13n - 2n * B, M) / 3n;
  const X1 = mod(248n * p - 8n * B - 10n * kM + 25n, M) / 9n;
  const X2 = mod(16n * (X / 27n) - 4n * (p % M10) - 2n * (kM % M10) - 1n, M10);
  const X5 = mod(128n * (X / 729n) - p % M7 - 2n * (kM % M7) + 3n, M7);
  const X6 = mod(256n * (X / 729n) - 3n * (p % M6) - 6n * (kM % M6) + 9n, M6);
  const q243 = powMod(2n, mod(kP - a, 162n), 243n);
  const G0num = mod(26368n * q243 + 74n * (kM % 243n) - 23n, 243n);
  const k54 = mod(97n * powMod(2n, a - 7n, 54n) + 48n, 54n);
  return {
    Kmod54: Number(k54),
    rho: Number(mod(k54 + 6n * a, 54n)),
    X: Number(X), v3X: v3(X, 13),
    X1mod27: Number(X1 % 27n),
    X2: Number(X2), v3X2: v3(X2, 10),
    X5: Number(X5), v3X5: v3(X5, 7),
    X6: Number(X6), v3X6: v3(X6, 6),
    G0mod9: Number((G0num / 27n) % 9n),
    A0mod3: Number(mod(4n * (p % 3n) + 2n * (kM % 3n) + 1n, 3n))
  };
}

const base = certificate(1238n);
assert.deepEqual(base, {
  Kmod54: 44, rho: 20,
  X: 712233, v3X: 6,
  X1mod27: 21,
  X2: 32799, v3X2: 1,
  X5: 1595, v3X5: 0,
  X6: 14, v3X6: 0,
  G0mod9: 1, A0mod3: 0
});
for (let n = 1n; n <= 2n; n++) {
  assert.deepEqual(certificate(1238n + n * P), base);
}
console.log(JSON.stringify({period:Number(P), modulus:Number(M), representative:1238, residues:base}, null, 2));
