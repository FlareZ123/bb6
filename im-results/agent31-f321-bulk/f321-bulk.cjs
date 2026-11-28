#!/usr/bin/env node
// Exact BigInt accelerator for the upstream F321 two-counter map.
// Source: google-deepmind/cryptids @ c86f15861709b76042998c5211c7b2f83991621b
// BusyBeaver/BB6/M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD.lean
// This is a simulator for that published counter map, NOT a physical TM proof.
"use strict";

const assert = require("node:assert/strict");

function mapOnce(a, d) {
  assert(a >= 0n && d >= 0n);
  if (a >= d + 2n) return { a: a - d - 2n, d: 2n*d + 3n, kind: "high" };
  if (a === d + 1n) return { halt: true, kind: "halt" };
  if (a === d) return { a: 2n*a + 4n, d: 1n, kind: "equal" };
  if (d >= 3n*a + 1n) return { a: 4n*a + 6n, d: d - 3n*a, kind: "far" };
  return { a: 4n*a + 6n, d: (d-a)%2n === 0n ? 2n : 1n, kind: "middle" };
}

// Difference a_k-d_k after k consecutive high-branch steps:
// a+d+6+k - 2^(k+1)*(d+3). Strictly decreasing in k.
function deltaAt(a, d, k) {
  return a + d + 6n + k - ((d+3n) << (k+1n));
}

// Return the first state NOT satisfying a >= d+2.
// Search requires only O(log(k)) exact BigInt shifts/comparisons.
function bulkHigh(a, d) {
  assert(a >= 0n && d >= 0n);
  if (a <= d + 1n) return { a, d, k: 0n };
  let hi = 1n;
  while (deltaAt(a, d, hi) >= 2n) hi <<= 1n;
  let lo = hi >> 1n;
  while (hi - lo > 1n) {
    const mid = (lo + hi) >> 1n;
    if (deltaAt(a, d, mid) >= 2n) lo = mid;
    else hi = mid;
  }
  const dNext = ((d + 3n) << hi) - 3n;
  const aNext = dNext + deltaAt(a, d, hi);
  assert(aNext >= 0n && dNext >= 0n && aNext - dNext <= 1n);
  return { a: aNext, d: dNext, k: hi };
}

function slowHigh(a, d) {
  let k = 0n;
  while (a >= d + 2n) {
    a -= d + 2n; d = 2n*d + 3n; k++;
  }
  return { a, d, k };
}

function test() {
  for (let x = 0; x < 100; ++x) for (let y = 0; y < 40; ++y) {
    const a = BigInt(x), d = BigInt(y);
    assert.deepEqual(bulkHigh(a, d), slowHigh(a, d));
  }
  for (const [a,d] of [
    [(1n<<128n) + 1024n, 1n],
    [(1n<<2048n) + 100n, 2n],
    [(1n<<8000n) + 150n, 17n]
  ]) assert.deepEqual(bulkHigh(a, d), slowHigh(a, d));
  let a = 1n, d = 1n, total = 0n;
  for (let i = 0; i < 200000; ++i) {
    const slow = mapOnce(a,d), high = bulkHigh(a,d);
    if (high.k === 0n) assert.equal(high.a, a);
    if (slow.kind !== "high") {
      assert.equal(high.k, 0n);
    } else {
      assert(high.k > 0n);
    }
    // Sample a full 10^4-step ordinary prefix against the bulk epoch route.
    const next = mapOnce(a,d);
    if (next.halt) break;
    a = next.a; d = next.d; total++;
    if (total >= 10000n) break;
  }
}

function run(epochs, sampleEvery) {
  let a = 1n, d = 1n, steps = 0n, done = 0;
  const count = { equal: 0, far: 0, middle: 0 };
  let longestHigh = 0n, halt = false;
  let report = [];
  for (let i = 0; i < epochs; i++) {
    const b = bulkHigh(a, d);
    a = b.a; d = b.d; steps += b.k;
    if (b.k > longestHigh) longestHigh = b.k;
    if (a === d + 1n) { halt = true; break; }
    const next = mapOnce(a, d);
    assert(!next.halt && next.kind !== "high");
    a = next.a; d = next.d; steps++; done++;
    count[next.kind]++;
    if (done % sampleEvery === 0)
      report.push({ epochs: done, counterTransitions: steps.toString(),
        bitLength: Math.max(a.toString(2).length,d.toString(2).length) });
  }
  return { epochs: done, nonhaltingCounterTransitions: steps.toString(),
    haltingGateReached: halt, last: { aBits: a.toString(2).length, dBits: d.toString(2).length },
    longestHigh: longestHigh.toString(), count, report };
}

if (require.main === module) {
  test();
  const n = Number(process.argv[2] ?? "100000");
  assert(Number.isSafeInteger(n) && n >= 1 && n <= 1_000_000);
  process.stdout.write(JSON.stringify(run(n, 10000), null, 2) + "\n");
}
module.exports = { mapOnce, deltaAt, bulkHigh, slowHigh, run, test };
