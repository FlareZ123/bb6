#!/usr/bin/env node
"use strict";

// Exact BigInt audit of the rho=20 t=0,q=0 candidate family.
// Usage: node rho20_parent_census.mjs [even-a>=18]
// Includes every odd exponent t with 3^(t+1) | (2u+5).

function pow2(n) { return 1n << BigInt(n); }
function pow3(n) { return 3n ** BigInt(n); }
function bitLength(n) { return n <= 0n ? 0 : n.toString(2).length; }

function valuation3(n) {
  let v = 0;
  while (n !== 0n && n % 3n === 0n) {
    n /= 3n;
    v++;
  }
  return v;
}

function allResetParents(u) {
  if (u < 0n) throw new Error("negative target");
  if (u === 0n) return [];
  const out = [];

  // An even-parent target in [6*2^k-1, 8*2^k-3] has bit length k+3.
  const kEven = bitLength(u) - 3;
  if (kEven >= 0) {
    const scale = pow2(kEven);
    if (6n * scale - 1n <= u && u <= 8n * scale - 3n) {
      const h = 2n * u - 8n * scale - BigInt(kEven);
      if (h < 0n || h >= u) throw new Error("invalid even parent");
      out.push({ h, kind: "even", k: kEven, t: null });
    }
  }

  const X = 2n * u + 5n;
  const vmax = valuation3(X);
  for (let t = 0; t < vmax; t++) {
    const d = X / pow3(t + 1);
    if (d % 2n !== 1n) throw new Error("odd quotient invariant failed");
    const P = pow2(t) * d;
    // An odd-source value in [6*2^k+1, 8*2^k-1] has bit length k+3.
    const k = bitLength(P) - 3;
    if (k < 0) continue;
    const scale = pow2(k);
    if (6n * scale + 1n <= P && P <= 8n * scale - 1n) {
      const h = 2n * P - 8n * scale - BigInt(k) - 5n;
      if (h < 0n || h >= u) throw new Error("invalid odd parent");
      out.push({ h, kind: "odd", k, t });
    }
  }
  return out;
}

function rootCandidate(K, a) {
  const p = pow2(K);
  const c = 2n * BigInt(K) + 7n;
  const r = K + 4 - a;
  const B = c * pow2(r);
  const numerator = B - 16n * p + 2n * BigInt(K) + 1n;
  if (numerator % 3n !== 0n) throw new Error("D is not integral");
  const D = numerator / 3n;
  const E = 8n * p + BigInt(K) - D;
  const X = 2n * E + 5n;
  if (X % 9n !== 0n) throw new Error("rho=20 phase did not give 9|X");
  return { E, X };
}

function parentGraph(root) {
  const rootKey = root.toString();
  const nodes = new Map([[rootKey, { u: root, parents: [] }]]);
  const queue = [rootKey];
  let edgeCount = 0;

  while (queue.length > 0) {
    const key = queue.pop();
    const node = nodes.get(key);
    for (const p of allResetParents(node.u)) {
      const parentKey = p.h.toString();
      node.parents.push({ key: parentKey, kind: p.kind, k: p.k, t: p.t });
      edgeCount++;
      if (!nodes.has(parentKey)) {
        nodes.set(parentKey, { u: p.h, parents: [] });
        queue.push(parentKey);
      }
    }
  }

  const memo = new Map();
  const leaves = [];
  function longestPath(key) {
    if (memo.has(key)) return memo.get(key);
    const node = nodes.get(key);
    if (node.parents.length === 0) {
      leaves.push(key);
      memo.set(key, 0);
      return 0;
    }
    let best = 0;
    for (const p of node.parents) {
      best = Math.max(best, 1 + longestPath(p.key));
    }
    memo.set(key, best);
    return best;
  }

  const maxDepth = longestPath(rootKey);
  const rootHit = Array.from(nodes.values()).some(n => n.u === 2n);
  const branchingNodes = Array.from(nodes.values()).filter(n => n.parents.length > 1).length;
  return {
    nodes: nodes.size,
    edges: edgeCount,
    leaves: leaves.length,
    maxDepth,
    rootHit,
    branchingNodes
  };
}

function census(a) {
  const cMin = 97n * pow2(a - 6);
  const cMax = 13n * pow2(a - 3);
  const KMin = (cMin - 6n) / 2n;
  const KMax = (cMax - 8n) / 2n;
  const residue = BigInt(((20 - 6 * a) % 54 + 54) % 54);
  const delta = (residue - KMin % 54n + 54n) % 54n;
  const firstK = KMin + delta;

  const rows = [];
  for (let K = firstK; K <= KMax; K += 54n) {
    const { E, X } = rootCandidate(Number(K), a);
    const graph = parentGraph(E);
    rows.push({
      K: K.toString(),
      v3X: valuation3(X),
      ...graph
    });
  }

  const v3Histogram = {};
  const depthHistogram = {};
  for (const row of rows) {
    v3Histogram[row.v3X] = (v3Histogram[row.v3X] || 0) + 1;
    depthHistogram[row.maxDepth] = (depthHistogram[row.maxDepth] || 0) + 1;
  }
  return {
    a,
    count: rows.length,
    firstK: rows[0].K,
    lastK: rows[rows.length - 1].K,
    v3Histogram,
    depthHistogram,
    rootHits: rows.filter(r => r.rootHit).length,
    maxDepth: Math.max(...rows.map(r => r.maxDepth)),
    maxNodes: Math.max(...rows.map(r => r.nodes)),
    maxEdges: Math.max(...rows.map(r => r.edges)),
    branchingGraphs: rows.filter(r => r.branchingNodes > 0).length
  };
}

function deepEvenChainWitness(a) {
  const KMin = (97n * pow2(a - 6) - 6n) / 2n;
  const residue = BigInt(((20 - 6 * a) % 54 + 54) % 54);
  const delta = Number((residue - KMin % 54n + 54n) % 54n);
  const K = KMin + BigInt(delta);
  const p = pow2(K);
  const c = 2n * K + 7n;
  const B = c * pow2(K + 4n - BigInt(a));
  const D = (B - 16n * p + 2n * K + 1n) / 3n;
  const E = 8n * p + K - D;
  const X0 = 2n * E + 5n;
  const P0 = X0 / 3n;
  const E1 = 2n * P0 - 4n * p - K - 4n;
  const X1 = 2n * E1 + 5n;
  const P1 = X1 / 3n;
  const L = K - 2n;
  let y = 2n * P1 - 2n * p - K - 3n;
  const scale = pow2(L);
  let edges = 0;
  while (6n * scale - 1n <= y && y <= 8n * scale - 3n) {
    edges++;
    y = 2n * y - 2n * scale - L;
  }
  return {
    a,
    K: K.toString(),
    delta,
    cOffsetFromLower: (c - 97n * pow2(a - 6)).toString(),
    t0ParentAtKminus1: 3n * p + 1n <= P0 && P0 <= 4n * p - 1n,
    secondT0ParentAtKminus2: 6n * scale + 1n <= P1 && P1 <= 8n * scale - 1n,
    sameLevelEvenEdges: edges,
    provenLowerBound: a - 10
  };
}

const a = Number(process.argv[2] || 18);
if (!Number.isInteger(a) || a < 18 || a % 2 !== 0) {
  throw new Error("a must be an even integer >=18");
}
console.log(JSON.stringify({
  census: census(a),
  deepEvenChainWitness: deepEvenChainWitness(a)
}, null, 2));
