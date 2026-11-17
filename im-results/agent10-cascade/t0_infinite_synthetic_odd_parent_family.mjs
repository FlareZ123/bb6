#!/usr/bin/env node
// Exact BigInt witness for the infinite root-unreachable t=0 family.
// The infinitude and all-time inverse-tree argument are in the companion note.

import assert from "node:assert/strict";

const a = 18n;
const K = 202538n;
const c = 2n * K + 7n;
const two = n => 1n << n;
const mod = (x, m) => ((x % m) + m) % m;

assert.equal(K % 54n, 38n);
assert.equal(K % 6n, 2n);
assert(K >= 266n);
assert(25n * c >= 38n * two(a));
assert(20n * c <= 31n * two(a));

const p = two(K);
const r = K + 1n - a;
const L = K - 1n;
const pL = two(L);
assert.equal(r % 2n, 1n);

const B0 = c * two(r + 3n);
const numerator = B0 - 16n * p + 2n * K + 1n;
assert.equal(numerator % 3n, 0n);
const D0 = numerator / 3n;
const E = 8n * p + K - D0;
assert.equal(B0, 40n * p + K - 1n - 3n * E);

// Fatal source and first-failure certificate.
const d0Numerator = 8n * p + E + K + 5n;
assert.equal(d0Numerator % 2n, 0n);
const d0 = d0Numerator / 2n;
assert.equal(d0 % 2n, 1n);
assert(6n * p + 1n <= d0 && d0 <= 8n * p - 1n);
assert(4n * p <= E + K + 4n);
assert(E + K + 5n < 8n * p);

// Exact unique odd parent of E: v3(2E+5)=1, t=0.
const A = 16n * p + 2n * K + 5n;
const X = 2n * E + 5n;
assert.equal(X, A - 2n * D0);
assert.equal(mod(D0, 9n), 2n);
assert.equal(mod(A, 9n), 1n);
assert.equal(mod(X, 9n), 6n);
assert.equal(X % 3n, 0n);
assert.notEqual(X % 9n, 0n);
const P = X / 3n;
assert.equal(P % 2n, 1n);
assert(6n * pL + 1n <= P && P <= 8n * pL - 1n);

const parent = 2n * P - 8n * pL - L - 5n;
assert.equal(2n * P, 8n * pL + parent + L + 5n);
assert.equal(2n * E + 5n, 3n * P);
assert(4n * pL <= parent + L + 4n);
assert(parent + L + 5n < 8n * pL);

// E lies in the gap between every even-parent target band.
assert(5n * p < E);
assert(2n * E < 11n * p);
assert(4n * p - 3n < E);
assert(E < 6n * p - 1n);

// The unique odd parent is itself parentless.
assert.equal(mod(parent, 3n), 0n);
assert(2n * p < parent);
assert(parent < 3n * p - 1n);
assert(2n * p - 3n < parent);
assert(7n * p > 225n);

assert(parent > 2n);
assert(E > 2n);
assert(two(K - 2n) < 3n ** L);

console.log(JSON.stringify({
  familyParameters: {
    a: String(a), K: String(K), r: String(r), L: String(L),
    xNumerator: String(c), xDenominator: String(two(a))
  },
  exactResidues: {
    D0mod9: String(mod(D0, 9n)),
    Amod9: String(mod(A, 9n)),
    Xmod9: String(mod(X, 9n)),
    parentMod3: String(mod(parent, 3n)),
    v3X: 1
  },
  E: {
    noEvenParentGap: true,
    uniqueOddParentAtLevel: String(L),
    firstFailureEndpoints: true
  },
  uniqueParent: {
    sourceEquation: true,
    outputEquation: true,
    oddSourceBand: true
  },
  parent: {
    noOddParentByMod3: true,
    noEvenParentByDyadicGap: true,
    parentless: true
  },
  conclusion: "E is outside the ResetParent-chain component of root 2"
}, null, 2));
