#!/usr/bin/env node
"use strict";

// Exact, standalone regression of the canonical #746 terminal-spine theorem.
// This checks the *full* two-arm ResetParent relation, including every
// 3-adic odd valuation t whose output equation is divisible by 3^(t+1).
// No truncation by a guessed "maximal" valuation.
//
// Usage: node terminal_spine_parent_census.mjs [min_n=257] [max_n=2048]

const lo = Number(process.argv[2] ?? "257");
const hi = Number(process.argv[3] ?? "2048");
if (!Number.isSafeInteger(lo) || !Number.isSafeInteger(hi) ||
    lo < 257 || hi < lo || hi > 200000) {
  throw new Error("Require safe integer range 257 <= min_n <= max_n <= 200000");
}
const b2 = k => 1n << BigInt(k);

function hasCompleteResetParent(u) {
  const uBitLength = u.toString(2).length;
  // In the even arm, u must be in [6*2^k-1, 8*2^k-3].
  // k=uBitLength-3 is the unique possible scale except for the
  // low edge u=2^(k+3)-1, which can only satisfy the previous scale
  // if it is <=8*2^k-3 (it isn't). Check two neighboring scales
  // explicitly to make this regression robust at all endpoints.
  for (let k = Math.max(0, uBitLength - 4); k <= uBitLength - 2; k++) {
    const p = b2(k), h = 2n * u - 8n * p - BigInt(k);
    if (6n * p - 1n <= u && u <= 8n * p - 3n && h >= 0n) return true;
  }

  const X = 2n * u + 5n;
  let z = X;
  let t = 0;
  while (z % 3n === 0n) {
    z /= 3n; // d = X/3^(t+1); it may still be divisible by 3!
    const w = b2(t) * z;
    const bitLength = w.toString(2).length;
    // w is in [6*2^k+1, 8*2^k-1] for at most one k.
    for (let k = Math.max(0, bitLength - 4); k <= bitLength - 2; k++) {
      const p = b2(k), h = 2n * w - 8n * p - BigInt(k) - 5n;
      if ((z & 1n) === 1n &&
          6n * p + 1n <= w && w <= 8n * p - 1n &&
          h >= 0n) return true;
    }
    t++;
  }
  return false;
}

function terminal(n) {
  const N = BigInt(n), c = 2n * N + 3n;
  const a = c.toString(2).length - 1, J = n - a;
  const p = b2(n), s = b2(J), u = 4n * p + N - 1n - c * s;
  const X = 2n * u + 5n;
  const predictedHasParent =
    J % 2 === 0 && (4n * c <= 7n * b2(a) || X % 9n === 0n);
  return {n, a, J, u, X, predictedHasParent};
}

let checked = 0, leafCount = 0, discrepancyCount = 0;
for (let n = lo; n <= hi; n++) {
  if (n % 6 !== 4 && n % 6 !== 5) continue;
  const t = terminal(n);
  const actual = hasCompleteResetParent(t.u);
  checked++;
  if (!actual) leafCount++;
  if (actual !== t.predictedHasParent) {
    console.error("MISMATCH", {
      n, a: t.a, J: t.J,
      Xmod9: String(t.X % 9n), predicted: t.predictedHasParent,
      actual
    });
    discrepancyCount++;
  }
}
console.log(JSON.stringify({
  range: [lo, hi], gateIndicesChecked: checked,
  predecessorFreeTerminals: leafCount, discrepancies: discrepancyCount
}));
if (discrepancyCount !== 0) process.exitCode = 1;

// Each complete dyadic block has ~7/12 predecessor-free terminals.
// With prefixes ending at the high-c threshold, the ratio tends to
// 23/42; at complete block ends, it tends to 7/12.
// This loop uses modular arithmetic, not gigantic 2^n integers.
const pow2mod9 = [1, 2, 4, 8, 7, 5];
function fastLeaf(n) {
  const c = 2 * n + 3, a = Math.floor(Math.log2(c)), J = n - a;
  const xmod9 = ((8 * pow2mod9[n % 6] + 2 * n + 3 -
    2 * c * pow2mod9[((J % 6) + 6) % 6]) % 9 + 9) % 9;
  return J % 2 === 1 || (4 * c > 7 * (2 ** a) && xmod9 !== 0);
}
const blockRows = [];
for (let a = 10; a <= 16; a++) {
  const start = 2 ** (a - 1) - 1, end = 2 ** a - 2;
  let G = 0, L = 0;
  for (let n = start; n <= end; n++) {
    if (n % 6 !== 4 && n % 6 !== 5) continue;
    G++;
    if (fastLeaf(n)) L++;
  }
  blockRows.push({a, gateIndices: G, exactLeafCount: L,
    ratio: Number((L / G).toFixed(8))});
}
console.log("complete_dyadic_blocks", JSON.stringify(blockRows));


// Full inverse-cone check for the paper-level low-valuation unique-chain
// theorem. Unlike a finite-step forward simulation, this enumerates *all*
// parent options at every visited node under ResetParent's exact two arms.
function allResetParents(u) {
  const out = [];
  const uBits = u.toString(2).length;
  for (let k = Math.max(0, uBits - 4); k <= uBits - 2; k++) {
    const p = b2(k), h = 2n * u - 8n * p - BigInt(k);
    if (6n * p - 1n <= u && u <= 8n * p - 3n && h >= 0n) {
      out.push({kind:"even", k, h});
    }
  }
  let x = 2n * u + 5n, t = 0;
  while (x % 3n === 0n) {
    x /= 3n;
    const w = b2(t) * x;
    const bits = w.toString(2).length;
    for (let k = Math.max(0, bits - 4); k <= bits - 2; k++) {
      const p = b2(k), h = 2n * w - 8n * p - BigInt(k) - 5n;
      if ((x & 1n) === 1n && 6n * p + 1n <= w && w <= 8n * p - 1n
          && h >= 0n) out.push({kind:"odd", t, k, h});
    }
    t++;
  }
  return out;
}
let lowValCases = 0, lowValDecided = 0, badConeCases = 0, maxDepth = 0;
for (let n = lo; n <= hi; n++) {
  if (n % 6 !== 4 && n % 6 !== 5) continue;
  const t = terminal(n);
  const high = 4n * BigInt(2 * n + 3) > 7n * b2(t.a);
  if (!high || t.J % 2 !== 0 ||
      !((n % 6 === 4 && [9n,18n].includes(t.X % 27n)) ||
        (n % 6 === 5 && t.X % 27n === 9n))) continue;
  lowValCases++;
  let u = t.u, depth = 0, valid = true;
  while (true) {
    if (u === 2n) { valid = false; break; }
    const ps = allResetParents(u);
    if (ps.length === 0) break;
    if (ps.length !== 1 || depth > t.a + 10) { valid = false; break; }
    u = ps[0].h;
    depth++;
  }
  if (valid) lowValDecided++;
  else { badConeCases++; console.error("CONE MISMATCH", n, depth); }
  maxDepth = Math.max(maxDepth, depth);
}
console.log("low_valuation_unique_chain", JSON.stringify({
  gateRange: [lo,hi], cases: lowValCases,
  conesEndedAtNonrootLeaves: lowValDecided,
  discrepancies: badConeCases, maximumParentDepth: maxDepth
}));
if (badConeCases) process.exitCode = 1;


// Uniform 2-edge theorem in the previously residual n%6=5, X%27=18
// phase. The full grammar must give exactly [odd t=1, even], then no
// predecessors of the last state, for the stated large-q subwindow.
let twoEdgeCases = 0, twoEdgeFailures = 0;
for (let n = lo; n <= hi; n++) {
  if (n % 6 !== 5) continue;
  const t = terminal(n);
  const c = BigInt(2*n+3);
  if (t.J % 2 !== 0 || 64n*c < 121n*b2(t.a) ||
      t.X % 27n !== 18n) continue;
  const p = b2(n);
  const b0 = 4n * (t.X / 9n) - p - BigInt(n) - 2n;
  const Y = 2n*b0 + 5n;
  if (Y % 9n === 0n) continue;
  twoEdgeCases++;
  const pb = allResetParents(t.u);
  const pc = allResetParents(b0);
  const b1 = 2n*b0-p-BigInt(n-3);
  const pd = allResetParents(b1);
  if (pb.length!==1 || pb[0].h!==b0 ||
      pb[0].kind!=="odd" || pb[0].t!==1 ||
      pc.length!==1 || pc[0].h!==b1 ||
      pc[0].kind!=="even" || b1===2n || pd.length!==0) {
    console.error("TWO-EDGE MISMATCH",n);
    twoEdgeFailures++;
  }
}
console.log("two_edge_terminal_exclusion", JSON.stringify({
  gateRange:[lo,hi], cases:twoEdgeCases, discrepancies:twoEdgeFailures
}));
if (twoEdgeFailures) process.exitCode=1;
