#!/usr/bin/env node
"use strict";

// Small M16 finite over-approximation of BB6CLine.nextC.
// The quotient is a=mod16, k=mod16, c exact for 0,1 and mod16 thereafter.

const M = 16;
const MC = 16;
const NC = MC + 2;
const V = M * M * NC;

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

const seen = new Uint8Array(V);
const queue = new Uint16Array(V);
let head = 0;
let tail = 0;
let edges = 0;

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
        edges++;
        const t = index(out[0], out[1], out[2]);
        if (!seen[t]) {
          seen[t] = 1;
          queue[tail++] = t;
        }
      }
    }
  }
}

const words = [];
for (let w = 0; w < V / 64; w++) {
  let value = 0n;
  for (let b = 0; b < 64; b++) {
    if (seen[w * 64 + b]) value |= 1n << BigInt(b);
  }
  words.push("0x" + value.toString(16).padStart(16, "0"));
}

const c0ExcludedMasks = Array(16).fill(0);
for (let a = 0; a < 16; a++) {
  for (let k = 0; k < 16; k++) {
    if (!seen[index(a, k, 0)]) c0ExcludedMasks[a] |= 1 << k;
  }
}

function baselineJointHighAllowed(j, m) {
  return !(
    (m >= 2 && j % 4 === 3 && (j + 3 * m + 7) % 16 === 0) ||
    (m >= 2 && j % 4 === 1 && (j + 3 * m + 11) % 32 === 0) ||
    (m >= 4 && (
      (m % 4 === 0 && (j + m) % 32 === 26) ||
      (m % 4 === 1 && (j + m) % 32 === 2)
    )) ||
    (m === 1 && j % 32 === 1) ||
    (m >= 2 && j % 2 === 1 && (j + 3 * m + 5) % 8 === 0) ||
    (m % 32 === 5 && j % 32 === 12)
  );
}

// A 1-bit at (j mod16,m mod16) means the M16 quotient excludes
// the high-family CReach target, while every corresponding mod32
// lift passes the baseline jointHighAllowed predicate.
const highNewMasks = Array(16).fill(0);
for (let jr = 0; jr < 16; jr++) {
  for (let mr = 0; mr < 16; mr++) {
    const a = (2 * jr + 3) % 16;
    const k = ((-(jr + 3 * mr + 5)) % 16 + 16) % 16;
    const quotientExcludes =
      ((c0ExcludedMasks[a] >> k) & 1) === 1;

    let allBaselineLiftsPass = true;
    for (const j of [jr, jr + 16]) {
      for (const rawM of [mr, mr + 16]) {
        const m = rawM < 4 ? rawM + 32 : rawM;
        if (!baselineJointHighAllowed(j, m)) allBaselineLiftsPass = false;
      }
    }
    if (quotientExcludes && allBaselineLiftsPass) {
      highNewMasks[jr] |= 1 << mr;
    }
  }
}

const lowExcluded = [];
for (let m = 1; m < 16; m++) {
  const k = ((-(3 * m + 4)) % 16 + 16) % 16;
  if (((c0ExcludedMasks[1] >> k) & 1) === 1) lowExcluded.push(m);
}

const popcount = n => {
  let x = n, count = 0;
  while (x) { count += x & 1; x >>>= 1; }
  return count;
};

const badCount = c0ExcludedMasks.reduce((s, x) => s + popcount(x), 0);
const highNewCount = highNewMasks.reduce((s, x) => s + popcount(x), 0);

if (V !== 4608 || tail !== 2820 || edges !== 20640 ||
    badCount !== 94 || highNewCount !== 82) {
  throw new Error("M16 quotient census mismatch");
}

console.log(JSON.stringify({
  vertices: V,
  reachableStates: tail,
  representativeEdges: edges,
  reachableBitsetWords64: words,
  c0ExcludedKMaskByAMod16: c0ExcludedMasks.map(x => "0x" + x.toString(16).padStart(4, "0")),
  c0ExcludedPairCount: badCount,
  lowFamilyExcludedMResiduesMod16: lowExcluded,
  highFamilyNewExcludedMMaskByJMod16: highNewMasks.map(x => "0x" + x.toString(16).padStart(4, "0")),
  highFamilyNewExcludedCellCount: highNewCount
}, null, 2));
