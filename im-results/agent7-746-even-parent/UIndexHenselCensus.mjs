#!/usr/bin/env node
"use strict";

// Exact BigInt census for the fixed-depth U/Q ray j=3402 and
// n = 887 + 13122*r. The inverse formulas are transcribed from
// CascadeResetInverse.ResetParent / ParentsFast.lean.

const N0 = 887n;
const STEP = 13122n;
const J = 3402n;

function powMod(a, e, m) {
  let r = 1n, b = a % m;
  while (e > 0n) {
    if (e & 1n) r = (r * b) % m;
    b = (b * b) % m;
    e >>= 1n;
  }
  return r;
}

function modNorm(x, m) {
  const r = x % m;
  return r < 0n ? r + m : r;
}

function selector(K) {
  if (K < 8) throw new Error("K must be at least 8");
  const mod = 3n ** BigInt(K);
  const period = 3 ** (K - 8);
  const p0 = powMod(2n, N0, mod);
  const stepPow = powMod(2n, STEP, mod);
  const jPow = powMod(2n, J + 4n, mod);
  let p = p0;
  const roots = [];
  for (let r = 0; r < period; r++) {
    const n = N0 + STEP * BigInt(r);
    const q = modNorm(28n * p - 2n * n + 15n - jPow * (2n * n + 3n), mod);
    if (q === 0n) roots.push(r);
    p = (p * stepPow) % mod;
  }
  return { K, period, roots };
}

function valuation3(x) {
  if (x <= 0n) throw new Error("valuation3 expects a positive integer");
  let v = 0;
  while (x % 3n === 0n) {
    x /= 3n;
    v++;
  }
  return v;
}

function bitLength(x) {
  if (x <= 0n) throw new Error("bitLength expects a positive integer");
  return x.toString(2).length;
}

function exactParents(u) {
  const out = [];

  // Even ResetParent arm: unique scale k = floor(log2(u)) - 2.
  if (u > 0n) {
    const k = bitLength(u) - 3;
    if (k >= 0) {
      const p = 1n << BigInt(k);
      if (6n * p - 1n <= u && u <= 8n * p - 3n) {
        const h = 2n * u - 8n * p - BigInt(k);
        if (h >= 0n) out.push({ kind: "even", t: null, k, h });
      }
    }
  }

  // Odd ResetParent arm: enumerate every exact 3-adic exponent.
  const w = 2n * u + 5n;
  const v = valuation3(w);
  let pow3 = 3n;
  for (let t = 0; t < v; t++) {
    const d = w / pow3;
    const x = (1n << BigInt(t)) * d;
    const k = bitLength(x) - 3;
    if (k >= 0 && d % 2n === 1n) {
      const p = 1n << BigInt(k);
      if (6n * p + 1n <= x && x <= 8n * p - 1n) {
        const h = 2n * x - 8n * p - BigInt(k) - 5n;
        if (h >= 0n) out.push({ kind: "odd", t, k, h });
      }
    }
    pow3 *= 3n;
  }

  for (const p of out) {
    if (p.h >= u) throw new Error("parent is not strictly smaller");
  }
  return out;
}

function reverseCone(target) {
  const nodes = [{ value: target, depth: 0 }];
  const index = new Map([[target.toString(), 0]]);
  let edges = 0;
  let root2 = false;
  let maxDepth = 0;
  for (let i = 0; i < nodes.length; i++) {
    const u = nodes[i].value;
    for (const p of exactParents(u)) {
      edges++;
      if (p.h === 2n) root2 = true;
      const key = p.h.toString();
      if (!index.has(key)) {
        index.set(key, nodes.length);
        nodes.push({ value: p.h, depth: nodes[i].depth + 1 });
        maxDepth = Math.max(maxDepth, nodes[i].depth + 1);
      }
    }
  }
  return { nodes: nodes.length, edges, maxDepth, root2 };
}

function qValue(n) {
  return 28n * (1n << BigInt(n)) - 2n * BigInt(n) + 15n
    - (1n << (J + 4n)) * (2n * BigInt(n) + 3n);
}

function sample(r) {
  const n = Number(N0 + STEP * BigInt(r));
  const Q = qValue(n);
  if (Q <= 0n || Q % 9n !== 0n) throw new Error("invalid Q candidate");
  const v = valuation3(Q);
  const zNumerator = Q / 9n - 5n;
  if (zNumerator % 2n !== 0n) throw new Error("candidate z is not integral");
  const z = zNumerator / 2n;
  const ps = exactParents(z);
  const maximalT = v - 3;
  const hasMaximalT = ps.some(p => p.kind === "odd" && p.t === maximalT);
  return {
    r, n, v3Q: v, maximalT, hasMaximalT,
    rootParentTypes: ps.map(p => p.kind === "even" ? "E" : "O" + p.t),
    reverseCone: reverseCone(z)
  };
}

const residues = [];
for (let K = 8; K <= 19; K++) residues.push(selector(K));
const examples = [4, 13, 1057].map(sample);
console.log(JSON.stringify({ residues, examples }, null, 2));
