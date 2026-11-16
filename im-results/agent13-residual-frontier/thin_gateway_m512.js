#!/usr/bin/env node
"use strict";

// M=512, c-modulus=256 over-approximation of the exact Machine C CLine map.
// This is the same quotient graph and transition function used by
// agent19-c-odd-dyadic/QuotientRectCensus.cpp, with an added thin-gateway scan.

const M = 512;
const MC = 256;
const NC = MC + 2;
const VERTICES = M * M * NC;

function projectC(c) {
  return c < 2 ? c : 2 + ((c - 2) % MC);
}

function index(a, k, c) {
  return ((a % M) * M + (k % M)) * NC + projectC(c);
}

function nextC(a, k, c) {
  if (c === 1) return [a, k + 1, 0];
  if (c === 2) return null;
  if (c === 3) return [a, k + 2, 1];

  if (c === 0) {
    if (a === 0) return [1, 0, 2 * k + 2];
    if (a === 1 && k === 0) return [5, 0, 1];
    if (a === 1) return [2, 2, 2 * k - 1];
    return [a - 2, 1, 2 * k + 1];
  }

  if (a === 0) {
    if (k % 2 === 0) return [2 * k + 2, 2, c - 3];
    return [2 * k + 3, 0, c];
  }

  return [a - 1, k + 1, c - 1];
}

const seen = new Uint8Array(VERTICES);
const queue = new Uint32Array(32_000_000);
let head = 0;
let tail = 0;
let representativeEdges = 0;

const start = index(5, 0, 1);
seen[start] = 1;
queue[tail++] = start;

while (head < tail) {
  const id = queue[head++];
  const c = id % NC;
  const k = Math.floor(id / NC) % M;
  const a = Math.floor(id / (NC * M));

  const aReps = [a, a + M];
  const kReps = [k, k + M];
  const cReps = c < 2 ? [c] : [c, c + MC];

  for (const ar of aReps) {
    for (const kr of kReps) {
      for (const cr of cReps) {
        const out = nextC(ar, kr, cr);
        if (out === null) continue;
        representativeEdges++;

        const target = index(out[0], out[1], out[2]);
        if (!seen[target]) {
          if (tail >= queue.length) {
            throw new Error("queue capacity exceeded");
          }
          seen[target] = 1;
          queue[tail++] = target;
        }
      }
    }
  }
}

if (VERTICES !== 67633152 || tail !== 27858704 ||
    representativeEdges !== 221572376) {
  throw new Error("M512 quotient census mismatch: " +
    JSON.stringify({ VERTICES, reached: tail, representativeEdges }));
}

const allowed = [];
const excluded = [];
for (let j = 0; j < 256; j++) {
  const target = index(0, 2 * j, 4 * j + 10);
  (seen[target] ? allowed : excluded).push(j);
}

if (allowed.length !== 116 || excluded.length !== 140) {
  throw new Error("thin-gateway residue census mismatch");
}

console.log(JSON.stringify({
  quotient: "a,k mod 512; c exact for 0,1 and mod 256 for c>=2",
  vertices: VERTICES,
  reachableStates: tail,
  representativeEdges,
  thinGatewayPeriod: 256,
  thinGatewayAllowedResidues: allowed,
  thinGatewayExcludedResidues: excluded,
  allowedCount: allowed.length,
  excludedCount: excluded.length
}, null, 2));
