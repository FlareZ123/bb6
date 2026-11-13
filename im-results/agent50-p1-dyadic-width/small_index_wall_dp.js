#!/usr/bin/env node
// Exact carry-DP certificate for the finite wall exclusion 14 <= n <= 147.
// Run with: node small_index_wall_dp.js

const assert = require("node:assert/strict");

function modularSubsetCarries(n) {
  // Enumerate all A subset {0,...,n-1} containing 0 such that
  // sum_{s in A} (n+3+s) 2^s == 1 (mod 2^n).
  // BigInt keeps the computation exact throughout.
  let states = new Set([0n]);
  for (let j = 0; j < n; j++) {
    const C = BigInt(n + 3 + j);
    const targetBit = j === 0 ? 1n : 0n;
    const next = new Set();
    for (const c of states) {
      for (let x = 0n; x <= 1n; x++) {
        if (j === 0 && x === 0n) continue;
        const v = c + x * C;
        if (v % 2n === targetBit) next.add((v - targetBit) / 2n);
      }
    }
    states = next;
    if (states.size === 0) break;
  }
  return states;
}

const viable = [];
for (let n = 14; n <= 147; n++) {
  const states = modularSubsetCarries(n);
  if (states.size !== 0) {
    viable.push({
      n,
      terminalCarries: [...states]
        .sort((a, b) => (a < b ? -1 : a > b ? 1 : 0))
        .map(String),
    });
  }
}
assert.deepEqual(viable, [{
  n: 30,
  terminalCarries: ["1", "4", "14", "16", "26", "29", "32", "35", "45", "47", "57", "60"],
}]);

function fullWallCarriesAtN30() {
  // W_30 is sum_{s in A} (Q-s)2^s = 2^m(P+m+33)-1,
  // with P=2^30 and Q=7P-33. The carry c_m must equal P+m+32.
  const P = 1n << 30n;
  const Q = 7n * P - 33n;
  const mod = 1n << 15n;
  let states = new Set([0n]);
  let peakStates = 1;
  let lastNonemptyM = 0;
  const exactHits = [];
  const mod15Hits = [];
  let statesAt81 = [];

  for (let j = 0; j < 1000; j++) {
    const C = Q - BigInt(j);
    const next = new Set();
    for (const c of states) {
      for (let x = 0n; x <= 1n; x++) {
        if (j === 0 && x === 0n) continue;
        const v = c + x * C;
        // Target bits of -1 are all 1.
        if ((v & 1n) === 1n) next.add((v - 1n) / 2n);
      }
    }
    states = next;
    peakStates = Math.max(peakStates, states.size);
    const m = j + 1;
    const target = P + BigInt(m + 32);
    if (states.has(target)) exactHits.push(m);
    if ([...states].some(c => c % mod === target % mod)) mod15Hits.push(m);
    if (states.size !== 0) lastNonemptyM = m;
    if (m === 81) {
      statesAt81 = [...states]
        .sort((a, b) => (a < b ? -1 : a > b ? 1 : 0))
        .map(String);
    }
    if (states.size === 0) break;
  }

  return {
    P: String(P),
    Q: String(Q),
    lastNonemptyM,
    finalStateCount: states.size,
    peakStates,
    exactHits,
    mod15Hits,
    statesAt81,
  };
}

const n30 = fullWallCarriesAtN30();
assert.equal(n30.lastNonemptyM, 81);
assert.equal(n30.finalStateCount, 0);
assert.equal(n30.peakStates, 44);
assert.deepEqual(n30.exactHits, []);
assert.deepEqual(n30.mod15Hits, []);
assert.deepEqual(n30.statesAt81, [
  "174940530",
  "2053988694",
  "5462203960",
  "7341252124",
]);

console.log(JSON.stringify({ prefixRange: [14, 147], viable, n30 }, null, 2));
