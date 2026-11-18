#!/usr/bin/env node
"use strict";

/*
 * Reproducible finite experiment for the marker-1 S0 -> first q4 checkpoint.
 *
 * Usage:
 *   node marker1_q4_checkpoint_sweep.js [A=4] [L=2] [zMax=9] [maxSteps=3000000]
 *
 * This directly transcribes the TM2 transition table and initial tape
 * convention in agent48-counted-inc0/marker1_terminal_q4_checkpoint.py.
 * It checks three intermediate S0 configurations, both counted-drain
 * costs, the linear setup/tail frames, and the final q4 checkpoint.
 * This is computational evidence, not a Lean proof.
 */

const TM2 = [
  [[1,  1, 1], null],
  [[1, -1, 2], [0,  1, 5]],
  [[1,  1, 4], [0, -1, 3]],
  [[0, -1, 2], [1,  1, 1]],
  [[1,  1, 0], [1,  1, 4]],
  [[1,  1, 4], [0,  1, 3]],
];

const LH = [1, 1, 0, 1, 1, 1];
const S0_RIGHT_0 = [0, 1, 1, 1, 0, 0, 1, 1, 1];

const repeatBlock = (n, block) =>
  Array.from({ length: n }, () => block).flat();

const d0pow = n => repeatBlock(n, [0, 0, 1]);
const d1pow = n => repeatBlock(n, [1, 1, 1]);
const d010pow = n => repeatBlock(n, [0, 1, 0]);

function binDec(width, n) {
  let p = 2 ** (width + 1) - 1 - n;
  const out = [];
  for (let i = 0; i < width; i++) {
    if (p <= 1) break;
    out.push(...(p % 2 === 0 ? [0, 0, 1] : [1, 1, 1]));
    p = Math.floor(p / 2);
  }
  return out;
}

function v2(n) {
  if (n <= 0) throw new Error("v2 is only used on positive integers");
  let r = 0;
  while (n % 2 === 0) {
    n /= 2;
    r++;
  }
  return r;
}

// Lean's drainCost n c = inc0Cost n c + drainCost (n-1) (c+1).
function drainCost(n, c = 0) {
  let total = 0;
  for (let k = 1; k <= n; k++) {
    total += 48 + 12 * v2(k) + 12 * (c + n - k);
  }
  return total;
}

function s0RightFacing(b) {
  return [0, 1, 1, 1, 0, 0, ...d1pow(b + 1)];
}

function marker1InitialContext(L) {
  return [1, 0, 1, 0, 0, 1, ...d1pow(L), ...LH];
}

// Residual context after the setup macro, independent of z.
function marker1Q4Context(A, L) {
  return [
    1, 1,
    ...d010pow(A + 1),
    0, 1, 1, 1, 1, 0,
    ...d010pow(L),
    0, 1, 1, 1, 0, 1, 1, 1,
  ];
}

function q4CheckpointRight(z) {
  return [
    0, 0, 0,
    ...Array(3 * z + 5).fill(1),
    0, 0,
    ...Array(3 * 2 ** z).fill(1),
    0, 0, 0, 0,
  ];
}

function sameSet(xs, ys) {
  const a = new Set(xs), b = new Set(ys);
  return a.size === b.size && [...a].every(x => b.has(x));
}

function matchesTape(tape, head, left, right) {
  const expectedOnes = [];
  left.forEach((bit, i) => { if (bit) expectedOnes.push(head - i); });
  right.forEach((bit, i) => { if (bit) expectedOnes.push(head + 1 + i); });
  return sameSet([...tape], expectedOnes);
}

function simulateFirstCheckpoint(A, L, z, maxSteps) {
  if (!(A >= 1 && L >= 0 && z >= 0 && z < 2 ** A)) {
    throw new Error(`invalid parameters A=${A}, L=${L}, z=${z}`);
  }

  const M = 2 ** A * (2 ** (L + 2) - 1);
  const width = A + L + 2;
  const initialLeft = [...binDec(A, z), ...marker1InitialContext(L)];
  const tape = new Set();
  initialLeft.forEach((bit, i) => { if (bit) tape.add(-i); });
  S0_RIGHT_0.forEach((bit, i) => { if (bit) tape.add(i + 1); });

  const firstDrain = drainCost(z);
  const setup = 12 * (A + L) + 3 * z + 97;
  const secondDrain = drainCost(2 ** z - 1);
  const tail = 9 * z + 10;

  const checkpoints = [
    {
      name: "after-initial-counted-drain",
      step: firstDrain,
      state: 3,
      head: 0,
      left: [...d1pow(A), ...marker1InitialContext(L)],
      right: s0RightFacing(z),
    },
    {
      name: "before-second-counted-drain",
      step: firstDrain + setup,
      state: 3,
      head: 3 * z + 5,
      left: [...d0pow(z), ...marker1Q4Context(A, L)],
      right: s0RightFacing(0),
    },
    {
      name: "after-second-counted-drain",
      step: firstDrain + setup + secondDrain,
      state: 3,
      head: 3 * z + 5,
      left: [...d1pow(z), ...marker1Q4Context(A, L)],
      right: s0RightFacing(2 ** z - 1),
    },
    {
      name: "first-q4-checkpoint",
      step: firstDrain + setup + secondDrain + tail,
      state: 4,
      head: 1,
      left: [0, 1, 1, ...binDec(width, M - 1), ...LH],
      right: q4CheckpointRight(z),
    },
  ];

  let state = 3, head = 0, q4Events = 0;
  const observed = [];
  for (let steps = 0; steps <= checkpoints[3].step; steps++) {
    if (state === 4 && (tape.has(head) ? 1 : 0) === 0) {
      q4Events++;
    }

    for (const target of checkpoints.filter(x => x.step === steps)) {
      observed.push({
        name: target.name,
        step: steps,
        state,
        head,
        stateOK: state === target.state,
        headOK: head === target.head,
        tapeOK: matchesTape(tape, head, target.left, target.right),
      });
    }

    if (steps === checkpoints[3].step) break;
    const bit = tape.has(head) ? 1 : 0;
    const transition = TM2[state][bit];
    if (transition === null) {
      return { A, L, z, status: "halted", steps, q4Events, observed };
    }
    const [write, move, nextState] = transition;
    if (write === 1) tape.add(head);
    else tape.delete(head);
    state = nextState;
    head += move;
  }

  const predictedQ4Events = 3 * 2 ** z + 3 * z + 5;
  const predictedSteps =
    firstDrain + secondDrain + 12 * (A + L + z) + 107;

  return {
    A, L, z,
    firstDrain,
    setup,
    secondDrain,
    tail,
    checkpointStep: checkpoints[3].step,
    q4Events,
    predictedQ4Events,
    predictedSteps,
    observed,
    allIntermediateConfigsMatch: observed.length === 4 &&
      observed.every(x => x.stateOK && x.headOK && x.tapeOK),
    stepFormulaOK: checkpoints[3].step === predictedSteps,
    eventFormulaOK: q4Events === predictedQ4Events,
  };
}

const [A = 4, L = 2, zMax = 9, maxSteps = 3000000] =
  process.argv.slice(2).map(Number);

for (let z = 0; z <= zMax; z++) {
  const result = simulateFirstCheckpoint(A, L, z, maxSteps);
  console.log(JSON.stringify(result));
  if (result.status || !result.allIntermediateConfigsMatch ||
      !result.stepFormulaOK || !result.eventFormulaOK) {
    process.exitCode = 1;
    break;
  }
}
