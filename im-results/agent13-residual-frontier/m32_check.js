#!/usr/bin/env node
"use strict";

// Reproduce the B8/M32 quotient graph for BB6CLine.nextC.
// This is a finite over-approximation: absence of a projected state excludes
// the exact source state, while presence is only inconclusive.

const N = 40;
const TOTAL = N * N * N;

function q(x) {
  return x < 8 ? x : 8 + ((x - 8) % 32);
}

function representatives(u) {
  return u < 8 ? [u] : [u, u + 32];
}

// Exact cases from BB6CLine.nextC, with k denoting the input coordinate.
function nextC(a, k, c) {
  if (c === 1) return [a, k + 1, 0];
  if (c === 2) return null;
  if (c === 3) return [a, k + 2, 1];

  if (c === 0) {
    if (a === 0) return [1, 0, 2 * k + 2];
    if (a === 1) {
      if (k === 0) return [5, 0, 1];
      return [2, 2, 2 * k - 1];
    }
    return [a - 2, 1, 2 * k + 1];
  }

  if (a === 0) {
    if (k % 2 === 0) return [2 * k + 2, 2, c - 3];
    return [2 * k + 3, 0, c];
  }

  return [a - 1, k + 1, c - 1];
}

function index(a, k, c) {
  return (a * N + k) * N + c;
}

const seen = new Uint8Array(TOTAL);
const queue = new Int32Array(TOTAL);
let head = 0;
let tail = 0;
let representativeEdges = 0;

const start = index(q(5), q(0), q(1));
seen[start] = 1;
queue[tail++] = start;

while (head < tail) {
  const id = queue[head++];
  const c = id % N;
  const k = Math.floor(id / N) % N;
  const a = Math.floor(id / (N * N));

  for (const ar of representatives(a)) {
    for (const kr of representatives(k)) {
      for (const cr of representatives(c)) {
        const out = nextC(ar, kr, cr);
        if (out === null) continue;
        representativeEdges++;

        const target = index(q(out[0]), q(out[1]), q(out[2]));
        if (!seen[target]) {
          seen[target] = 1;
          queue[tail++] = target;
        }
      }
    }
  }
}

function reachable(state) {
  return seen[index(q(state[0]), q(state[1]), q(state[2]))] === 1;
}

const thin = [];
const firstStop = [];
const secondStop = [];

for (let j = 0; j < 64; j++) {
  if (reachable([0, 2 * j, 4 * j + 10])) thin.push(j);
  if (reachable([2 * j + 1, 3 * j + 4, 0])) firstStop.push(j);
}

for (let m = 1; m <= 5; m++) {
  for (let jPrime = 0; jPrime < 32; jPrime++) {
    const j = (2 ** (2 * m)) * (jPrime + 3) - 2;
    const k = (2 ** (2 * m + 2) - 1) * (jPrime + 3) - 3 * m - 2;
    if (reachable([2 * jPrime + 3, k, 0])) {
      secondStop.push({ m, jPrime, j, k });
    }
  }
}

if (reachable([3, 7, 0])) {
  throw new Error("q(3,7,0) unexpectedly belongs to the B8/M32 reachable closure");
}

const result = {
  quotient: "q(x)=x for x<8; otherwise 8+(x-8) mod 32",
  reachableStates: tail,
  representativeEdges,
  q_3_7_0_reachable: reachable([3, 7, 0]),
  thin_j_mod_64_reachable: thin,
  first_stop_j_mod_64_reachable: firstStop,
  second_stop_reachable_examples: secondStop.slice(0, 40),
  second_stop_reachable_count: secondStop.length,
};

if (tail !== 31570 || representativeEdges !== 189834) {
  throw new Error("quotient census mismatch: " + JSON.stringify(result));
}

console.log(JSON.stringify(result, null, 2));
