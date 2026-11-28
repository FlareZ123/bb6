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

// ALL exact antecedents of a post-high pair (r,D), including k=0.
// Because D+3=2^k(d+3), k ranges over a finite 2-adic divisor chain.
// For each admissible k, the unique predecessor is
// d=(D+3)/2^k -3, a=D-d-k+r.
function inverseBulkHigh(r, D) {
  if (r < 0n || D < 0n || r > D+1n) return [];
  let q = D+3n, k = 0n, res = [];
  while (q >= 3n) {
    const d = q-3n;
    const a = D-d-k+r;
    res.push({ a, d, k });
    if ((q & 1n) !== 0n) break;
    q >>= 1n;
    ++k;
  }
  return res;
}

// For the far branch (d >= 3a+1), k consecutive steps satisfy
// A_k = (a+2)*4^k-2, D_k=d-(a+2)*(4^k-1)+6k.
// The far guard gap D_k-(3*A_k+1) strictly decreases in k.
function farGap(a, d, k) {
  return d+a+7n+6n*k-((a+2n)<<(2n*k+2n));
}

function bulkFar(a, d) {
  assert(a >= 0n && d >= 0n);
  if (d < 3n*a+1n) return { a, d, k: 0n };
  let hi = 1n;
  while (farGap(a,d,hi) >= 0n) hi <<= 1n;
  let lo = hi >> 1n;
  while (hi-lo>1n) {
    const mid = (hi+lo)>>1n;
    if (farGap(a,d,mid) >= 0n) lo=mid; else hi=mid;
  }
  const pow = 1n << (2n*hi);
  const A = (a+2n)*pow-2n;
  const D = d-(a+2n)*(pow-1n)+6n*hi;
  assert(D>=0n && D<=3n*A);
  return {a:A,d:D,k:hi};
}

function slowFar(a,d) {
  let k=0n;
  while(d>=3n*a+1n) { d-=3n*a; a=4n*a+6n; k++; }
  return {a,d,k};
}

// Complete finite inverse of the maximal far-run map.
// For k>=1, the exit also has D>=1. The invariant A+2=(a+2)*4^k
// restricts k to a finite 4-adic divisor chain.
function inverseBulkFar(A,D) {
  if(A<0n||D<0n||D>3n*A)return [];
  let q=A+2n,k=0n,res=[];
  while(q>=2n) {
    const a=q-2n,d=D+A-a-6n*k;
    if((k===0n||D>=1n)&&d>=0n) res.push({a,d,k});
    if(q%4n!==0n)break;
    q/=4n;k++;
  }
  return res;
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
    const z = bulkHigh(a, d);
    assert.deepEqual(z, slowHigh(a, d));
    const inverses = inverseBulkHigh(z.a, z.d);
    assert(inverses.some(v => v.a === a && v.d === d && v.k === z.k));
    for (const v of inverses)
      assert.deepEqual(bulkHigh(v.a, v.d), {a:z.a, d:z.d, k:v.k});
    const far = bulkFar(a,d);
    assert.deepEqual(far,slowFar(a,d));
    const finv=inverseBulkFar(far.a,far.d);
    assert(finv.some(v=>v.a===a&&v.d===d&&v.k===far.k));
    for(const v of finv)
      assert.deepEqual(bulkFar(v.a,v.d), {a:far.a,d:far.d,k:v.k});
  }
  for (const [a,d] of [
    [(1n<<128n) + 1024n, 1n],
    [(1n<<2048n) + 100n, 2n],
    [(1n<<8000n) + 150n, 17n]
  ]) assert.deepEqual(bulkHigh(a, d), slowHigh(a, d));
  // Cross-check an authentic 500-epoch prefix, including each exact exit state,
  // against direct unaccelerated application of the published counter map.
  let a = 1n, d = 1n;
  for (let epoch = 0; epoch < 500; ++epoch) {
    const fast = bulkHigh(a,d), slow = slowHigh(a,d);
    assert.deepEqual(fast, slow);
    if (fast.a === fast.d + 1n) break;
    const f = mapOnce(fast.a,fast.d);
    assert(!f.halt && f.kind !== "high");
    a = f.a; d = f.d;
  }
  // The counter sum increases on every nonhalting map step.
  for (let x = 0; x < 100; ++x) for (let y = 0; y < 40; ++y) {
    const a = BigInt(x), d = BigInt(y), z = mapOnce(a,d);
    if (!z.halt) assert(z.a + z.d >= a+d+1n);
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
module.exports = { mapOnce, deltaAt, bulkHigh, inverseBulkHigh, slowHigh, farGap, bulkFar, inverseBulkFar, slowFar, run, test };
