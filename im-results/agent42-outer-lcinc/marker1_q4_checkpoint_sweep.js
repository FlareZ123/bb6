#!/usr/bin/env node
"use strict";

/*
 * Reproducible finite experiment for the marker-1 S0 -> first q4 checkpoint.
 *
 * Usage:
 *   node marker1_q4_checkpoint_sweep.js [A=4] [L=2] [zMax=9] [maxSteps=3000000]
 *
 * This is a direct transcription of the TM2 transition table and initial
 * tape convention in agent48-counted-inc0/marker1_terminal_q4_checkpoint.py.
 * It is computational evidence, not a Lean proof.
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
const S0_RIGHT = [0, 1, 1, 1, 0, 0, 1, 1, 1];

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

function rle(bits) {
  if (bits.length === 0) return [];
  const out = [];
  let bit = bits[0], count = 0;
  for (const x of bits) {
    if (x === bit) count++;
    else {
      out.push([bit, count]);
      bit = x;
      count = 1;
    }
  }
  out.push([bit, count]);
  return out;
}

function expectedRight(z) {
  return [
    ...Array(3).fill(0),
    ...Array(3 * z + 5).fill(1),
    ...Array(2).fill(0),
    ...Array(3 * 2 ** z).fill(1),
    ...Array(4).fill(0),
  ];
}

function simulateFirstCheckpoint(A, L, z, maxSteps) {
  if (!(A >= 1 && L >= 0 && z >= 0 && z < 2 ** A)) {
    throw new Error(`invalid parameters A=${A}, L=${L}, z=${z}`);
  }
  const M = 2 ** A * (2 ** (L + 2) - 1);
  const width = A + L + 2;

  // Initial s0Config (markerWord 1 ++ d0 ++ d1pow L ++ lh) A z 0 0.
  const left = [
    ...binDec(A, z),
    1, 0, 1,       // markerWord 1
    0, 0, 1,       // d0
    ...Array(3 * L).fill(1),
    ...LH,
  ];
  const tape = new Set();
  left.forEach((bit, i) => { if (bit) tape.add(-i); });
  S0_RIGHT.forEach((bit, i) => { if (bit) tape.add(i + 1); });

  let state = 3, head = 0, q4Events = 0;
  for (let steps = 0; steps < maxSteps; steps++) {
    const bit = tape.has(head) ? 1 : 0;
    if (state === 4 && bit === 0) {
      q4Events++;
      if (head === 1) {
        const expectedLeft = [
          0, 1, 1,
          ...binDec(width, M - 1),
          ...LH,
        ];
        const expectedLeftSet = new Set();
        expectedLeft.forEach((v, i) => {
          if (v) expectedLeftSet.add(1 - i);
        });
        const actualLeftSet = new Set([...tape].filter(p => p <= 1));
        const leftOK =
          expectedLeftSet.size === actualLeftSet.size &&
          [...expectedLeftSet].every(p => actualLeftSet.has(p));

        const right = expectedRight(z);
        const rightOK = right.every(
          (v, i) => (tape.has(2 + i) ? 1 : 0) === v
        );
        const noFurtherOnes = [...tape].every(
          p => p < 2 || p < 2 + right.length
        );

        const K = 2 ** z - 1;
        const predictedSteps =
          drainCost(z) + drainCost(K) + 12 * (A + L + z) + 107;
        const predictedQ4Events = 3 * 2 ** z + 3 * z + 5;

        return {
          A, L, z, checkpointStep: steps, q4Events,
          leftOK, rightOK, noFurtherOnes,
          rightRLE: rle(right),
          predictedSteps, predictedQ4Events,
          stepFormulaOK: steps === predictedSteps,
          eventFormulaOK: q4Events === predictedQ4Events,
        };
      }
    }

    const transition = TM2[state][bit];
    if (transition === null) {
      return { A, L, z, status: "halted", steps, q4Events };
    }
    const [write, move, nextState] = transition;
    if (write === 1) tape.add(head);
    else tape.delete(head);
    state = nextState;
    head += move;
  }
  return { A, L, z, status: "step-limit", maxSteps, q4Events };
}

const [A = 4, L = 2, zMax = 9, maxSteps = 3000000] =
  process.argv.slice(2).map(Number);

for (let z = 0; z <= zMax; z++) {
  const result = simulateFirstCheckpoint(A, L, z, maxSteps);
  console.log(JSON.stringify(result));
  if (result.status || !result.leftOK || !result.rightOK ||
      !result.noFurtherOnes || !result.stepFormulaOK ||
      !result.eventFormulaOK) {
    process.exitCode = 1;
    break;
  }
}
