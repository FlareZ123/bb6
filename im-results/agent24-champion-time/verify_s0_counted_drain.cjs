#!/usr/bin/env node
"use strict";

/*
 * Independent raw-step regression for the arbitrary-left all-ones S0 drain
 * in ../agent42-q4-s0-drain/S0CountedDrain.lean.
 *
 * Run:
 *   node verify_s0_counted_drain.cjs
 *
 * For each width k, the source counter is 2^k-1, the initial right unary
 * count is zero, and the target is the same S0 configuration with binary
 * counter zero and right unary count 2^k-1. The simulator executes every
 * primitive TM2 transition and compares the complete finite support of the
 * tape, not merely a bounded window.
 *
 * Executed in the authoring invocation's JavaScript runtime:
 *   widths k=0..10, two distinct arbitrary left contexts per width;
 *   22 cases, 16,946,784 raw transitions, zero failures.
 *
 * This is computational evidence only, not a Lean proof or axiom audit.
 */

const D0 = [0, 0, 1];
const D1 = [1, 1, 1];
const TRANSITIONS = [
  [[1, 1, 1], null],
  [[1, -1, 2], [0, 1, 5]],
  [[1, 1, 4], [0, -1, 3]],
  [[0, -1, 2], [1, 1, 1]],
  [[1, 1, 0], [1, 1, 4]],
  [[1, 1, 4], [0, 1, 3]],
];

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

function s0Support(leftContext, width, value, rightUnary, head) {
  const ones = new Set();
  const left = binDec(width, value).concat(leftContext);
  const right = [0, 1, 1, 1, 0, 0].concat(
    Array(3 * (rightUnary + 1)).fill(1)
  );
  left.forEach((bit, i) => {
    if (bit) ones.add(head - i);
  });
  right.forEach((bit, i) => {
    if (bit) ones.add(head + 1 + i);
  });
  return ones;
}

function simulateAllOnesDrain(leftContext, width, head) {
  const value = 2 ** width - 1;
  const steps =
    6 * 4 ** width + 42 * 2 ** width - 12 * width - 48;
  let ones = s0Support(leftContext, width, value, 0, head);
  let state = 3;
  let position = head;

  for (let k = 0; k < steps; k++) {
    const transition = TRANSITIONS[state][ones.has(position) ? 1 : 0];
    if (transition === null) {
      return { ok: false, haltedAt: k, state, head: position };
    }
    const [write, move, nextState] = transition;
    if (write) ones.add(position);
    else ones.delete(position);
    position += move;
    state = nextState;
  }

  const expected = s0Support(
    leftContext, width, 0, value, head
  );
  const sameTape =
    ones.size === expected.size && [...ones].every((x) => expected.has(x));

  return {
    ok: sameTape && state === 3 && position === head,
    steps,
    state,
    head: position,
    actualOnes: ones.size,
    expectedOnes: expected.size,
  };
}

let cases = 0;
let totalSteps = 0;
const failures = [];

for (let width = 0; width <= 10; width++) {
  for (let variant = 0; variant < 2; variant++) {
    const contextLength = (width * 7 + variant * 13) % 47;
    const leftContext = Array.from(
      { length: contextLength },
      (_, i) => (
        (i * 17 + width * 11 + variant * 5 + i * width) % 7 < 3
          ? 1
          : 0
      )
    );
    const head = variant === 0 ? 0 : -37;
    const result = simulateAllOnesDrain(leftContext, width, head);
    cases++;
    totalSteps += result.steps;
    if (!result.ok) {
      failures.push({
        width,
        variant,
        contextLength,
        head,
        ...result,
      });
    }
  }
}

const report = {
  widths: "0..10",
  contextsPerWidth: 2,
  cases,
  totalRawSteps: totalSteps,
  failures: failures.length,
  examples: failures.slice(0, 10),
};

console.log(JSON.stringify(report, null, 2));
if (failures.length !== 0) process.exitCode = 1;
