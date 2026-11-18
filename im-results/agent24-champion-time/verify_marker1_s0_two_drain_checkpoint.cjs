#!/usr/bin/env node
"use strict";

/*
 * Full raw-step splice test for the marker-1 S0 -> first q4 checkpoint.
 *
 * Run:
 *   node verify_marker1_s0_two_drain_checkpoint.cjs
 *
 * Tested factorization:
 *
 *   S0(l, A, z, 0, 0)
 *     -- D(z) -->
 *   S0(l, A, 0, z, 0)
 *     -- 12(A+L)+3z+97 -->
 *   S0(l2, z, 2^z-1, 0, 3z+5)
 *     -- D(2^z-1) -->
 *   S0(l2, z, 0, 2^z-1, 3z+5)
 *     -- 9z+10 -->
 *   first q4 checkpoint (state 4, head 1).
 *
 * Here
 *   l  = markerWord(1) ++ d0 ++ d1pow(L) ++ LH
 *   l2 = 110 ++ (100)^(A+1) ++ 111 ++ (100)^(L+1) ++ 1110111
 * and D(n)=drainCost(n,0) from CountedReset.
 *
 * Every phase is simulated using primitive TM2 transitions. At each
 * intermediate S0 endpoint, the entire finite one-support is compared
 * against the canonical encoder, not merely a local window. At the final
 * checkpoint, the entire left and right finite-support tape is compared,
 * and the q4/read-0 event count is checked.
 *
 * Executed in the authoring invocation's JavaScript runtime:
 *   30 parameter cases, 8,970,870 raw transitions, zero failures.
 *
 * This is computational evidence only. The intermediate-frame identities
 * and the parameterized macros still require Lean proofs and axiom audits.
 */

const TM2 = [
  [[1, 1, 1], null],
  [[1, -1, 2], [0, 1, 5]],
  [[1, 1, 4], [0, -1, 3]],
  [[0, -1, 2], [1, 1, 1]],
  [[1, 1, 0], [1, 1, 4]],
  [[1, 1, 4], [0, 1, 3]],
];

const D0 = [0, 0, 1];
const D1 = [1, 1, 1];
const LH = [1, 1, 0, 1, 1, 1];
const MARKER1 = [1, 0, 1];
const S0_RIGHT0 = [0, 1, 1, 1, 0, 0, 1, 1, 1];

function binDec(width, value) {
  let p = 2 ** (width + 1) - 1 - value;
  const out = [];
  for (let i = 0; i < width; i++) {
    if (p <= 1) break;
    out.push(...(p % 2 === 0 ? D0 : D1));
    p = Math.floor(p / 2);
  }
  return out;
}

function v2(n) {
  if (n <= 0) throw new RangeError("v2 requires a positive integer");
  let r = 0;
  while (n % 2 === 0) {
    n /= 2;
    r++;
  }
  return r;
}

function drainCost(n, c = 0) {
  let total = 0;
  for (let k = 1; k <= n; k++) {
    total += 48 + 12 * v2(k) + 12 * (c + n - k);
  }
  return total;
}

function supportFromWords(left, right, head) {
  const ones = new Set();
  left.forEach((bit, i) => {
    if (bit) ones.add(head - i);
  });
  right.forEach((bit, i) => {
    if (bit) ones.add(head + 1 + i);
  });
  return ones;
}

function s0Support(leftContext, width, value, rightUnary, head) {
  const left = binDec(width, value).concat(leftContext);
  const right = [0, 1, 1, 1, 0, 0].concat(
    Array(3 * (rightUnary + 1)).fill(1)
  );
  return supportFromWords(left, right, head);
}

function sameSupport(actual, expected) {
  return actual.size === expected.size &&
    [...actual].every((position) => expected.has(position));
}

function secondLeftContext(A, L) {
  return [
    1, 1, 0,
    ...Array(A + 1).fill([1, 0, 0]).flat(),
    1, 1, 1,
    ...Array(L + 1).fill([1, 0, 0]).flat(),
    1, 1, 1, 0, 1, 1, 1,
  ];
}

function runCase(A, L, z) {
  if (!(A >= 1 && L >= 0 && z >= 0 && z < 2 ** A)) {
    throw new RangeError(`invalid parameters A=${A}, L=${L}, z=${z}`);
  }

  const leftContext = [
    ...MARKER1,
    ...D0,
    ...Array(3 * L).fill(1),
    ...LH,
  ];
  let ones = s0Support(leftContext, A, z, 0, 0);
  let state = 3;
  let head = 0;
  let q4Events = 0;
  let transitions = 0;

  const firstDrain = drainCost(z);
  const preBridge = 12 * (A + L) + 3 * z + 97;
  const secondValue = 2 ** z - 1;
  const secondDrain = drainCost(secondValue);
  const postSweep = 9 * z;
  const postBridge = 10;
  const postlude = postSweep + postBridge;

  function runSteps(count) {
    for (let i = 0; i < count; i++) {
      const bit = ones.has(head) ? 1 : 0;
      if (state === 4 && bit === 0) q4Events++;
      const transition = TM2[state][bit];
      if (transition === null) return false;
      const [write, move, nextState] = transition;
      if (write) ones.add(head);
      else ones.delete(head);
      head += move;
      state = nextState;
      transitions++;
    }
    return true;
  }

  const checks = [];

  if (!runSteps(firstDrain)) {
    return { ok: false, A, L, z, failedPhase: "first drain" };
  }
  checks.push({
    phase: "first drain",
    ok: state === 3 && head === 0 &&
      sameSupport(ones, s0Support(leftContext, A, 0, z, 0)),
  });

  if (!runSteps(preBridge)) {
    return { ok: false, A, L, z, failedPhase: "pre-bridge" };
  }
  const secondHead = 3 * z + 5;
  const leftContext2 = secondLeftContext(A, L);
  checks.push({
    phase: "second S0 input",
    ok: state === 3 && head === secondHead &&
      sameSupport(
        ones,
        s0Support(leftContext2, z, secondValue, 0, secondHead)
      ),
  });

  if (!runSteps(secondDrain)) {
    return { ok: false, A, L, z, failedPhase: "second drain" };
  }
  checks.push({
    phase: "second drain",
    ok: state === 3 && head === secondHead &&
      sameSupport(
        ones,
        s0Support(leftContext2, z, 0, secondValue, secondHead)
      ),
  });

  if (!runSteps(postSweep)) {
    return { ok: false, A, L, z, failedPhase: "postlude left sweep" };
  }
  const bridgeInputFrame = Array.from(
    { length: 7 }, (_, i) => ones.has(i) ? 1 : 0
  ).join("");
  checks.push({
    phase: "postlude bridge input",
    ok: state === 3 && head === 5 && bridgeInputFrame === "0010110",
  });

  if (!runSteps(postBridge)) {
    return { ok: false, A, L, z, failedPhase: "postlude fixed bridge" };
  }
  const bridgeOutputFrame = Array.from(
    { length: 7 }, (_, i) => ones.has(i) ? 1 : 0
  ).join("");
  if (state === 4 && !ones.has(head)) q4Events++;

  const M = 2 ** A * (2 ** (L + 2) - 1);
  const finalWidth = A + L + 2;
  const finalLeft = [
    0, 1, 1,
    ...binDec(finalWidth, M - 1),
    ...LH,
  ];
  const finalRight = [
    ...Array(3).fill(0),
    ...Array(3 * z + 5).fill(1),
    ...Array(2).fill(0),
    ...Array(3 * 2 ** z).fill(1),
    ...Array(4).fill(0),
  ];
  const expectedCheckpoint = supportFromWords(finalLeft, finalRight, 1);
  const expectedSteps =
    firstDrain + secondDrain + 12 * (A + L + z) + 107;
  const expectedQ4Events = 3 * 2 ** z + 3 * z + 5;

  checks.push({
    phase: "postlude bridge output",
    ok: state === 4 && head === 1 && bridgeOutputFrame === "1000011",
  });
  checks.push({
    phase: "first q4 checkpoint",
    ok: state === 4 && head === 1 && !ones.has(1) &&
      sameSupport(ones, expectedCheckpoint),
  });

  return {
    A,
    L,
    z,
    transitions,
    expectedSteps,
    q4Events,
    expectedQ4Events,
    checks,
    ok: transitions === expectedSteps &&
      q4Events === expectedQ4Events &&
      checks.every((check) => check.ok),
  };
}

const CASES = [
  [4, 2, 0], [4, 2, 1], [4, 2, 2], [4, 2, 3], [4, 2, 4],
  [4, 2, 5], [4, 2, 6], [4, 2, 7], [4, 2, 8], [4, 2, 9],
  [3, 2, 0], [3, 2, 1], [3, 2, 2], [3, 2, 3], [3, 2, 4], [3, 2, 5],
  [5, 4, 0], [5, 4, 1], [5, 4, 2], [5, 4, 3], [5, 4, 4], [5, 4, 5],
  [5, 4, 7], [6, 4, 7], [7, 4, 7], [5, 6, 7],
  [5, 4, 9], [6, 4, 9], [7, 4, 9], [5, 6, 9],
];

const results = CASES.map(([A, L, z]) => runCase(A, L, z));
const report = {
  cases: results.length,
  totalRawTransitions: results.reduce((sum, r) => sum + r.transitions, 0),
  failures: results.filter((r) => !r.ok),
  summaries: results.map(({ A, L, z, transitions, q4Events, ok }) => ({
    A, L, z, transitions, q4Events, ok,
  })),
};

console.log(JSON.stringify(report, null, 2));
if (report.failures.length !== 0) process.exitCode = 1;
