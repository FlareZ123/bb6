#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");

function mod(n, m) {
  return ((n % m) + m) % m;
}

function powMod(a, e, m) {
  let r = 1n;
  a %= m;
  while (e > 0n) {
    if (e & 1n) r = (r * a) % m;
    a = (a * a) % m;
    e >>= 1n;
  }
  return r;
}

function ceilDiv(n, d) {
  return (n + d - 1n) / d;
}

const phases = [2n, 8n, 14n, 20n, 26n, 32n, 38n, 44n, 50n];
const phaseValues = new Map(phases.map(rho => [rho, new Set()]));

// Exact finite modular table: a mod 18 is even and K+6a = rho mod 54.
for (let a = 0n; a < 18n; a += 2n) {
  for (const rho of phases) {
    const kResidue = mod(rho - 6n * a, 54n);
    const n27 = mod(
      (2n * kResidue + 7n - powMod(2n, a, 27n)) *
        powMod(2n, mod(kResidue + 4n - a, 18n), 27n) +
        2n * kResidue + 1n,
      27n
    );
    assert.equal(n27 % 3n, 0n);
    const d9 = n27 / 3n;
    const x9 = Number(mod(
      16n * powMod(2n, kResidue, 9n) +
        2n * kResidue + 5n - 2n * d9,
      9n
    ));
    phaseValues.get(rho).add(x9);
  }
}

const expected = new Map([
  [2n, [3]], [8n, [2, 5, 8]], [14n, [1, 4, 7]],
  [20n, [0]], [26n, [2, 5, 8]], [32n, [1, 4, 7]],
  [38n, [6]], [44n, [2, 5, 8]], [50n, [1, 4, 7]]
]);

for (const rho of phases) {
  const actual = [...phaseValues.get(rho)].sort((x, y) => x - y);
  assert.deepEqual(actual, expected.get(rho));
}

// Exact large-integer witnesses for all nine phases at a=10.
const a = 10n;
const twoA = 1n << a;
const lower = ceilDiv(97n * twoA - 448n, 128n);
const upper = (13n * twoA - 56n) / 16n;
const witnesses = [];

for (const rho of phases) {
  const kResidue = mod(rho - 6n * a, 54n);
  const K = lower + mod(kResidue - lower, 54n);
  assert(K <= upper);
  assert(K >= 266n);
  assert(K % 6n === 2n);

  const p = 1n << K;
  const c = 2n * K + 7n;
  const r = K + 1n - a;
  assert(r % 2n === 1n);

  const B = c * (1n << (r + 3n));
  const numerator = B - 16n * p + 2n * K + 1n;
  assert.equal(numerator % 3n, 0n);
  const D = numerator / 3n;
  const E = 8n * p + K - D;
  const X = 2n * E + 5n;

  assert(E > 4n * p && E < 6n * p - 1n);
  assert.equal((E + K + 5n) % 2n, 0n);
  const d0 = 4n * p + (E + K + 5n) / 2n;
  assert(d0 % 2n === 1n && d0 > 6n * p && d0 < 8n * p);
  assert.equal(B, 40n * p + K - 1n - 3n * E);
  assert.equal(3n * d0 + B / 2n, 32n * p + 2n * K + 7n);

  let classification;
  if (X % 3n !== 0n) {
    classification = "E parentless";
  } else if (X % 9n !== 0n) {
    const d = X / 3n;
    const h = 2n * d - 4n * p - K - 4n;
    assert(d > 3n * p && d < 4n * p);
    assert(h > 2n * p && h < 3n * p - 1n);
    assert(h % 3n !== 2n);
    classification = "unique odd parent; parentless";
  } else {
    classification = "exceptional phase";
  }

  assert.equal(rho === 20n, X % 9n === 0n);
  witnesses.push({
    rho: Number(rho),
    K: String(K),
    Xmod9: Number(X % 9n),
    classification
  });
}

console.log(JSON.stringify({
  modularPhaseValues: Object.fromEntries(
    phases.map(rho => [String(rho), [...phaseValues.get(rho)].sort((x, y) => x - y)])
  ),
  a: Number(a),
  KInterval: [String(lower), String(upper)],
  witnesses
}, null, 2));
