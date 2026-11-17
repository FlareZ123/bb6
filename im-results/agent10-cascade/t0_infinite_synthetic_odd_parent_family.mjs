#!/usr/bin/env node
// Exact BigInt check of the first member of the infinite t=0 synthetic
// odd-parent family. The infinitude argument is in the accompanying note.

import assert from "node:assert/strict";

const a = 18n;
const K = 190064n;
const c = 2n * K + 7n;
const two = n => 1n << n;
const mod = (x, m) => ((x % m) + m) % m;

assert.equal(K % 54n, 38n);
assert.equal(K % 6n, 2n);
assert(K >= 266n);
assert(20n * c >= 29n * two(a));
assert(20n * c <= 31n * two(a));

const p = two(K);
const r = K + 1n - a;
const L = K - 1n;
assert.equal(r % 2n, 1n);
assert(r > 3n);

const B0 = c * two(r + 3n);
const numerator = B0 - 16n * p + 2n * K + 1n;
assert.equal(numerator % 3n, 0n);
const D0 = numerator / 3n;
const h = 8n * p + K - D0;
assert.equal(B0, 40n * p + K - 1n - 3n * h);

// The t=0 fatal source band and first-failure certificate.
const d0Numerator = 8n * p + h + K + 5n;
assert.equal(d0Numerator % 2n, 0n);
const d0 = d0Numerator / 2n;
assert(6n * p + 1n <= d0 && d0 <= 8n * p - 1n);
assert(4n * p <= h + K + 4n);
assert(h + K + 5n < 8n * p);

// The incoming q=0 parent has exact valuation v3(2E+5)=1.
const A = 16n * p + 2n * K + 5n;
const X = 2n * h + 5n;
assert.equal(X, A - 2n * D0);
assert.equal(mod(D0, 9n), 2n);
assert.equal(mod(A, 9n), 1n);
assert.equal(mod(X, 9n), 6n);
assert.equal(X % 3n, 0n);
assert.notEqual(X % 9n, 0n);
const P = X / 3n;
assert.equal(P % 2n, 1n);
assert(3n * p < P && P < 4n * p);

// Exact odd ResetParent from level L=K-1 to E=h.
const pL = two(L);
assert(6n * pL + 1n <= P && P <= 8n * pL - 1n);
const parent = 2n * P - 8n * pL - L - 5n;
assert.equal(2n * P, 8n * pL + parent + L + 5n);
assert.equal(2n * h + 5n, 3n * P);
assert(4n * pL <= parent + L + 4n);
assert(parent + L + 5n < 8n * pL);
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
    v3X: 1
  },
  incomingParent: {
    q: 0, t: 0, sourceLevel: String(L),
    sourceBand: true, firstFailureEndpoints: true,
    sourceEquation: true, outputEquation: true,
    scaleCondition: true
  },
  fatalSource: {
    oddTailDepth: String(r),
    rawOddParameterBand: true,
    firstFailureEndpoints: true,
    fatalEquation: true
  },
  boundary: "synthetic ResetParent only; no blank-root reachability claim"
}, null, 2));
