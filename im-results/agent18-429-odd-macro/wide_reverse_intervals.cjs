#!/usr/bin/env node
'use strict';

// Exact backward search for BB429Q0Macro.HalfStep.Trace at a fixed rank.
// All arithmetic is BigInt. No sampling, floating point, or height cutoff.
//
// A node (p,A,B,lo,hi,d) represents all original center heights h in
// [lo,hi] and their unique d-step inverse word, where current height=A*h+B.
// Node intervals include every strict positive predecessor for that word.
// Distinct words can overlap; this does not affect completeness.

const assert = require('node:assert/strict');

function floorDiv(x, m) {
  assert(m > 0n);
  return x >= 0n ? x / m : -((-x + m - 1n) / m);
}
function ceilDiv(x, m) { return -floorDiv(-x, m); }

function reverseDepth(P, cutoff = 64) {
  P = BigInt(P);
  assert(P >= 4n && Number.isSafeInteger(cutoff) && cutoff > 0);
  const stack = [[P, 1n, 0n, 1n, (P - 1n) / 3n, 0]];
  let maxDepth = 0;
  let nodes = 0;
  let unresolved = false;
  while (stack.length > 0) {
    const [p, A, B, lo, hi, depth] = stack.pop();
    nodes++;
    assert(lo <= hi && A > 0n && p >= 4n);
    if (depth > maxDepth) maxDepth = depth;
    if (depth === cutoff) {
      unresolved = true;
      continue;
    }
    // The previous state has the opposite rank parity: every cost is odd.
    const previousOdd = p % 2n === 0n;
    const nextA = 4n * A;
    for (let digit = 0; digit < 2; digit++) {
      const cost = BigInt(digit
        ? (previousOdd ? 3 : 9) : (previousOdd ? 1 : 5));
      const q = p - cost;
      if (q < 4n) continue; // no positive integer h with 3h < q
      const offset = BigInt(previousOdd ? 4 : 12);
      // Exact inverse of 4*h_current=h_previous+digit*q+offset*digit
      const nextB = 4n * B - (digit ? q + offset : 0n);
      const lower = ceilDiv(1n - nextB, nextA);
      const upper = floorDiv((q - 1n) / 3n - nextB, nextA);
      const L = lower > lo ? lower : lo;
      const H = upper < hi ? upper : hi;
      if (L <= H) stack.push([q, nextA, nextB, L, H, depth + 1]);
    }
  }
  return { maxDepth, nodes, unresolved };
}

// Independent tiny-universe height-by-height reference implementation.
function naiveMaxDepth(P) {
  let best = 0;
  for (let initial = 1; 3 * initial < P; initial++) {
    let p = P, y = initial, depth = 0;
    for (;;) {
      const odd = p % 2 === 0;
      let q = p - (odd ? 1 : 5);
      let z = 4 * y;
      if (q >= 4 && z > 0 && 3 * z < q) {
        p = q; y = z; depth++; continue;
      }
      q = p - (odd ? 3 : 9);
      z = 4 * y - q - (odd ? 4 : 12);
      if (q >= 4 && z > 0 && 3 * z < q) {
        p = q; y = z; depth++; continue;
      }
      break;
    }
    if (depth > best) best = depth;
  }
  return best;
}

function selfTest() {
  for (let P = 4; P <= 500; P++) {
    const s = reverseDepth(BigInt(P));
    assert(!s.unresolved);
    assert.equal(s.maxDepth, naiveMaxDepth(P), 'rank ' + P);
  }
  assert.equal(reverseDepth(4n ** 12n).maxDepth, 40);
  console.log('SELFTEST: 497 ranks and k=12,b=0 passed.');
}

function scan(kLo = 11, kHi = 20, cutoff = 64) {
  assert(Number.isSafeInteger(kLo) && Number.isSafeInteger(kHi));
  assert(kLo >= 1 && kHi >= kLo && kHi <= 64);
  for (let k = kLo; k <= kHi; k++) {
    const T = 4n ** BigInt(k);
    const radius = T / (128n * BigInt(k + 1));
    let maximum = 0, at = '', checked = 0, count = 0;
    for (let a = 1; a <= 2; a++) {
      for (let b = 0; b < 9; b++) {
        const r = reverseDepth(BigInt(a) * T + BigInt(b), cutoff);
        if (r.unresolved) {
          throw Error('Unresolved at k=' + k + ',a=' + a + ',b=' + b
            + ' (cutoff=' + cutoff + ')');
        }
        if (r.maxDepth > maximum) {
          maximum = r.maxDepth;
          at = a + ',' + b;
        }
        checked++;
        count += r.nodes;
      }
    }
    assert(checked === 18);
    const verifiedNoCrossing = BigInt(maximum) < radius;
    console.log(JSON.stringify({k, radius: radius.toString(),
      maxReverseDepth: maximum, at, nodes: count, checked,
      noFullWidePast: verifiedNoCrossing}));
    if (!verifiedNoCrossing) throw Error('No certificate at k=' + k);
  }
}

if (require.main === module) {
  const args = process.argv.slice(2);
  if (args[0] === '--selftest') selfTest();
  else scan(args[0] === undefined ? 11 : Number(args[0]),
            args[1] === undefined ? 20 : Number(args[1]),
            args[2] === undefined ? 64 : Number(args[2]));
}
module.exports = { reverseDepth, naiveMaxDepth, scan };
