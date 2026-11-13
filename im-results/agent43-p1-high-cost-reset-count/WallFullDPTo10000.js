#!/usr/bin/env node
// Exact finite all-depth shifted-wall exclusion for 14 <= n <= 10000.
// Run with: node WallFullDPTo10000.js
//
// Phase 1 reuses the exact modular carry/minimum-short-gap recurrence from
// im-results/agent50-p1-dyadic-width/wall_modular_obstruction.md.
// Phase 2 checks the full wall equation for every n surviving Phase 1.

const assert = require("node:assert/strict");

function minimumShortGaps(n) {
  if (n % 2 !== 0) return null;

  // After the forced bit x_0=1, c=(n+2)/2 and a=0.
  // Here a is the distance from the previous selected position minus one,
  // capped at 2. A selected bit adds one short gap iff a<=1.
  let states = new Map([[String((n + 2) / 2) + ",0", 0]]);

  const putMin = (map, key, value) => {
    const old = map.get(key);
    if (old === undefined || value < old) map.set(key, value);
  };

  for (let j = 1; j < n; j++) {
    const C = n + 3 + j;
    const next = new Map();

    for (const [key, cost] of states) {
      const comma = key.indexOf(",");
      const c = Number(key.slice(0, comma));
      const a = Number(key.slice(comma + 1));

      // The carry invariant gives 0 <= c <= 2n+2, so Number is exact
      // throughout this n<=10000 phase.
      assert.ok(Number.isSafeInteger(c) && c >= 0 && c <= 2 * n + 2);
      assert.ok(Number.isSafeInteger(C) && C <= 2 * n + 2);

      if (c % 2 === 0) {
        putMin(next, String(c / 2) + "," + String(Math.min(2, a + 1)), cost);
      }
      if ((c + C) % 2 === 0) {
        putMin(next, String((c + C) / 2) + ",0", cost + (a <= 1 ? 1 : 0));
      }
    }

    states = next;
    if (states.size === 0) return null;
  }

  return Math.min(...states.values());
}

const modularHits = [];
for (let n = 14; n <= 10000; n++) {
  const minimum = minimumShortGaps(n);
  if (minimum !== null) modularHits.push({ n, minimum });
}

assert.deepEqual(modularHits, [
  { n: 30, minimum: 8 },
  { n: 286, minimum: 88 },
  { n: 350, minimum: 112 },
  { n: 1614, minimum: 563 },
  { n: 2990, minimum: 1068 },
  { n: 3342, minimum: 1145 },
]);

function fullWallScan(n, maxM = 20000) {
  const P = 1n << BigInt(n);
  const Q = 7n * P - BigInt(n + 3);

  // After processing m bits, states contains every possible carry c_m
  // for a subset A of {0,...,m-1} containing 0, with the low m bits
  // of sum_{s in A}(Q-s)2^s all equal to 1.
  let states = new Set([0n]);
  let peakStates = 1;
  let lastNonemptyM = 0;
  const exactHits = [];

  for (let j = 0; j < maxM; j++) {
    const C = Q - BigInt(j);
    const next = new Set();

    for (const c of states) {
      // Omit j, or select j. The target bit of -1 is 1 at every position.
      if ((c & 1n) === 1n) next.add((c - 1n) / 2n);
      const v = c + C;
      if ((v & 1n) === 1n) next.add((v - 1n) / 2n);
    }

    states = next;
    const m = j + 1;
    const targetCarry = P + BigInt(m + n + 2);

    if (states.has(targetCarry)) exactHits.push(m);
    peakStates = Math.max(peakStates, states.size);

    if (states.size !== 0) lastNonemptyM = m;
    else {
      return {
        n,
        lastNonemptyM,
        emptyAt: m,
        peakStates,
        exactHits,
        finalStateCount: 0,
      };
    }
  }

  return {
    n,
    lastNonemptyM,
    emptyAt: null,
    peakStates,
    exactHits,
    finalStateCount: states.size,
  };
}

const fullWall = modularHits.map(({ n }) => fullWallScan(n));
assert.deepEqual(fullWall, [
  { n: 30, lastNonemptyM: 81, emptyAt: 82, peakStates: 44, exactHits: [], finalStateCount: 0 },
  { n: 286, lastNonemptyM: 1441, emptyAt: 1442, peakStates: 504, exactHits: [], finalStateCount: 0 },
  { n: 350, lastNonemptyM: 585, emptyAt: 586, peakStates: 152, exactHits: [], finalStateCount: 0 },
  { n: 1614, lastNonemptyM: 5823, emptyAt: 5824, peakStates: 1544, exactHits: [], finalStateCount: 0 },
  { n: 2990, lastNonemptyM: 6153, emptyAt: 6154, peakStates: 3040, exactHits: [], finalStateCount: 0 },
  { n: 3342, lastNonemptyM: 13729, emptyAt: 13730, peakStates: 7488, exactHits: [], finalStateCount: 0 },
]);

console.log(JSON.stringify({ modularHits, fullWall }, null, 2));
