#!/usr/bin/env node
// Exact BigInt witness for the q=0, D0 == 0 (mod 3) t=0 root-exclusion phase.

import assert from "node:assert/strict";

const a = 20n;
const K = 786440n;
const q = 0n;
const c = 2n * K + 7n;
const two = n => 1n << n;
const mod = (x, m) => ((x % m) + m) % m;

assert.equal(q, 0n);
assert.equal(a % 18n, 2n);
assert.equal(K % 18n, 2n);
assert(K >= 266n);
assert(2n * c >= 3n * two(a));
assert(4n * c <= 7n * two(a));

const p = two(K);
const r = K + 1n - a;
assert.equal(r % 6n, 1n);
assert.equal(r % 2n, 1n);

const B0 = c * two(r + 3n);
const numerator = B0 - 16n * p + 2n * K + 1n;
assert.equal(numerator % 3n, 0n);
const D0 = numerator / 3n;
const E = 8n * p + K - D0;
assert.equal(B0, 40n * p + K - 1n - 3n * E);

// D0 == 0 (mod 3) and every odd parent is excluded.
const A = 16n * p + 2n * K + 5n;
const X = 2n * E + 5n;
assert.equal(mod(D0, 3n), 0n);
assert.equal(mod(A, 3n), 1n);
assert.equal(mod(X, 3n), 1n);

// The q=0 t=0 fatal source band and first-failure endpoints.
const d0Numerator = 8n * p + E + K + 5n;
assert.equal(d0Numerator % 2n, 0n);
const d0 = d0Numerator / 2n;
assert.equal(d0 % 2n, 1n);
assert(6n * p + 1n <= d0 && d0 <= 8n * p - 1n);
assert(2n * D0 > 4n * p + 2n * K + 4n); // q>=1 violates the first-entry guard
assert(4n * p <= E + K + 4n);
assert(E + K + 5n < 8n * p);

// E is in the gap between all even-parent target bands.
assert(4n * p < E);
assert(12n * E < 65n * p);
assert(4n * p - 3n < E);
assert(E < 6n * p - 1n);
assert(E > 2n);

console.log(JSON.stringify({
  parameters: {
    a: String(a), K: String(K), r: String(r), q: String(q),
    xNumerator: String(c), xDenominator: String(two(a))
  },
  residues: {
    D0mod3: String(mod(D0, 3n)),
    Amod3: String(mod(A, 3n)),
    Xmod3: String(mod(X, 3n))
  },
  sourceBand: true,
  firstFailure: true,
  noOddParent: true,
  noEvenParent: true,
  conclusion: "q=0 first level-K entry E has no ResetParent and is not root-reachable"
}, null, 2));
