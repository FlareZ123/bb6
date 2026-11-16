#!/usr/bin/env node
"use strict";

// M512 source-parameter sieve for the authentic Machine C CLine map.
// The quotient and representative transition relation match
// im-results/agent19-c-odd-dyadic/QuotientRectCensus.cpp.

const fs = require("fs");
const crypto = require("crypto");

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

  const cReps = c < 2 ? [c] : [c, c + MC];
  for (const ar of [a, a + M]) {
    for (const kr of [k, k + M]) {
      for (const cr of cReps) {
        const out = nextC(ar, kr, cr);
        if (out === null) continue;
        representativeEdges++;

        const target = index(out[0], out[1], out[2]);
        if (!seen[target]) {
          if (tail >= queue.length) throw new Error("queue capacity exceeded");
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

// Low stopping family: CReach(1, 2^(2m+3) - (3m+4)).
// For m>=5, the first term vanishes modulo 512; use one m>=5
// representative for each residue class m mod 512.
const lowAllowed = [];
const lowExcluded = [];
for (let r = 0; r < M; r++) {
  const m = r < 5 ? r + M : r;
  const k = ((-(3 * m + 4)) % M + M) % M;
  (seen[index(1, k, 0)] ? lowAllowed : lowExcluded).push(r);
}

// The five small low parameters are checked with their exact, un-reduced k.
const lowSmall = [];
for (let m = 0; m < 5; m++) {
  const k = 2 ** (2 * m + 3) - (3 * m + 4);
  lowSmall.push({ m, k, quotientAdmitted: !!seen[index(1, k, 0)] });
}

// High stopping family:
// CReach(2j+3, 2^(2m+2)(j+3) - (j+3m+5)).
// For m>=4, 2^(2m+2) is 0 mod 512, so the complete residue
// period is (j mod 512, m mod 512).
const highMask = Buffer.alloc((M * M) / 8);
const highRowCounts = [];
let highAllowedCount = 0;
for (let mr = 0; mr < M; mr++) {
  const m = mr < 4 ? mr + M : mr;
  let rowCount = 0;
  for (let jr = 0; jr < M; jr++) {
    const k = ((-(jr + 3 * m + 5)) % M + M) % M;
    const admitted = !!seen[index(2 * jr + 3, k, 0)];
    if (admitted) {
      const bit = mr * M + jr;
      highMask[bit >> 3] |= 1 << (bit & 7);
      rowCount++;
      highAllowedCount++;
    }
  }
  highRowCounts.push(rowCount);
}
const highMaskPath = "M512HighAdmittedMask.bin";
fs.writeFileSync(highMaskPath, highMask);
const highMaskSha256 = crypto.createHash("sha256").update(highMask).digest("hex");

// The four small high parameters m=0,1,2,3 have a separate exact scan.
const highSmall = [];
for (let m = 0; m < 4; m++) {
  let admitted = 0;
  for (let j = 0; j < M; j++) {
    const k = 2 ** (2 * m + 2) * (j + 3) - (j + 3 * m + 5);
    if (seen[index(2 * j + 3, k, 0)]) admitted++;
  }
  highSmall.push({ m, admitted, excluded: M - admitted });
}

// Direct thin-gateway target T_j=(0,2j,4j+10), period 256.
const thinAllowed = [];
const thinExcluded = [];
for (let j = 0; j < 256; j++) {
  (seen[index(0, 2 * j, 4 * j + 10)] ? thinAllowed : thinExcluded).push(j);
}

if (lowAllowed.length !== 190 || lowExcluded.length !== 322 ||
    highAllowedCount !== 107446 || thinAllowed.length !== 116 ||
    thinExcluded.length !== 140) {
  throw new Error("parameter-sieve census mismatch");
}

console.log(JSON.stringify({
  quotient: {
    vertices: VERTICES,
    reachableStates: tail,
    representativeEdges,
    transitionSource: "BB6CLine.nextC",
    overApproximation: true
  },
  lowFamily: {
    period: 512,
    allowedCount: lowAllowed.length,
    excludedCount: lowExcluded.length,
    allowedResidues: lowAllowed,
    excludedResidues: lowExcluded,
    exactSmallParameters: lowSmall
  },
  highFamily: {
    period: [512, 512],
    totalResiduePairs: M * M,
    allowedPairs: highAllowedCount,
    excludedPairs: M * M - highAllowedCount,
    rowCountsByMResidue: highRowCounts,
    maskFile: highMaskPath,
    maskEncoding: "bit (mResidue*512 + jResidue); 1=quotient-admitted",
    maskSha256: highMaskSha256,
    exactSmallMParameters: highSmall
  },
  thinGateway: {
    period: 256,
    allowedCount: thinAllowed.length,
    excludedCount: thinExcluded.length,
    allowedResidues: thinAllowed,
    excludedResidues: thinExcluded
  }
}, null, 2));
