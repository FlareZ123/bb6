#!/usr/bin/env node
"use strict";

// Exact CLine boundary-macro simulation from (5,0,1).
// The only skipped transitions are repetitions of
//   (a,k,c) -> (a-1,k+1,c-1), valid for a>=1 and c>=4.
// A maximal run has length min(a,c-3), so its endpoint has a=0 or c=3.
// Thin gateways require a=0; no skipped interior state can be thin.

const targetJ = 1_000_000;
const targetRank = 8 * targetJ + 10;

let a = 5, k = 0, c = 1;
let ordinarySteps = 0;
let macroSteps = 0;
let highSkipped = 0;
let zeroEndpoints = 0;
let maxRank = 0;
const thinHits = [];
let hash = 2166136261 >>> 0;

for (;;) {
  const rank = a + 2 * k + c;
  if (rank > maxRank) maxRank = rank;

  if (a === 0) {
    zeroEndpoints++;
    if (k % 2 === 0 && c === 2 * k + 10) {
      thinHits.push({ ordinaryStep: ordinarySteps, j: k / 2, state: [a, k, c] });
    }
  }

  // FNV-1a over each boundary endpoint, in coordinate order.
  hash = Math.imul(hash ^ (a >>> 0), 16777619) >>> 0;
  hash = Math.imul(hash ^ (k >>> 0), 16777619) >>> 0;
  hash = Math.imul(hash ^ (c >>> 0), 16777619) >>> 0;

  if (rank > targetRank || c === 2) break;

  // Macro endpoints satisfy a=0 or c<=3.
  let na, nk, nc;
  if (c === 1) {
    na = a; nk = k + 1; nc = 0;
  } else if (c === 3) {
    na = a; nk = k + 2; nc = 1;
  } else if (c === 0) {
    const oldK = k;
    if (a === 0) {
      na = 1; nk = 0; nc = 2 * oldK + 2;
    } else if (a === 1) {
      if (oldK === 0) {
        na = 5; nk = 0; nc = 1;
      } else {
        na = 2; nk = 2; nc = 2 * oldK - 1;
      }
    } else {
      na = a - 2; nk = 1; nc = 2 * oldK + 1;
    }
  } else if (a === 0) {
    const oldK = k;
    if (oldK % 2 === 0) {
      na = 2 * oldK + 2; nk = 2; nc = c - 3;
    } else {
      na = 2 * oldK + 3; nk = 0; nc = c;
    }
  } else {
    throw new Error(`non-boundary macro endpoint: ${[a, k, c]}`);
  }

  // Count the one ordinary transition just taken.
  ordinarySteps++;

  // Collapse the maximal high branch following that transition.
  if (na >= 1 && nc >= 4) {
    const n = Math.min(na, nc - 3);
    na -= n;
    nk += n;
    nc -= n;
    ordinarySteps += n;
    highSkipped += n;
  }

  a = na; k = nk; c = nc;
  macroSteps++;

  if (!(a === 0 || c <= 3)) {
    throw new Error(`macro failed to land on boundary: ${[a, k, c]}`);
  }
}

const result = {
  targetJ,
  targetRank,
  ordinarySteps,
  macroSteps,
  highSkipped,
  singleSteps: ordinarySteps - highSkipped,
  zeroEndpoints,
  thinHits,
  finalState: [a, k, c],
  finalRank: a + 2 * k + c,
  maxRank,
  endpointChecksumFNV1a32: hash.toString(16).padStart(8, "0"),
  halted: c === 2,
};

if (result.ordinarySteps !== 2285059257097 ||
    result.macroSteps !== 4571232 ||
    result.highSkipped !== 2285054685865 ||
    result.zeroEndpoints !== 1143020 ||
    result.finalState.join(",") !== "5079022,1460493,3" ||
    result.finalRank !== 8000011 ||
    result.thinHits.length !== 0 ||
    result.endpointChecksumFNV1a32 !== "a11c234b") {
  throw new Error("reproduction check failed: " + JSON.stringify(result));
}

console.log(JSON.stringify(result, null, 2));
