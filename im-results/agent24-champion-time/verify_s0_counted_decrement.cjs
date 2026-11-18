#!/usr/bin/env node
"use strict";

/*
 * Independent raw-step regression for the arbitrary-left S0 Inc0 candidate
 * in ../agent42-q4-s0-drain/S0CountedDrain.lean.
 *
 * Run:
 *   node verify_s0_counted_decrement.cjs
 *
 * The simulator executes the six-state TM2 transition table one raw step at
 * a time. It compares the complete finite support of the resulting tape with
 * the canonical s0Config(l,a,z-1,b+1,h) support, as well as state and head.
 * The tested step count is exactly 48 + 12*v2(z) + 12*b.
 *
 * Executed in the authoring invocation's JavaScript runtime:
 *   exhaustive small cases: 228 / 228 passed
 *   seeded arbitrary-context cases: 1200 / 1200 passed
 *   total: 1428 / 1428 passed, zero failures
 *
 * This is computational evidence only, not a Lean proof or axiom audit.
 */

const D0 = [0, 0, 1];
const D1 = [1, 1, 1];

// Indexed by [state][read bit]; each transition is [write, move, nextState].
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

function v2(n) {
  if (!(n > 0)) throw new RangeError("v2 requires a positive integer");
  let r = 0;
  while (n % 2 === 0) {
    n /= 2;
    r++;
  }
  return r;
}

function simulateInc0(leftContext, width, value, rightUnary, head) {
  let ones = s0Support(leftContext, width, value, rightUnary, head);
  let state = 3;
  let position = head;
  const steps = 48 + 12 * v2(value) + 12 * rightUnary;

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
    leftContext, width, value - 1, rightUnary + 1, head
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

// Exhaustive small parameter grid with a nontrivial arbitrary left tail.
let exhaustiveCases = 0;
const failures = [];
for (let width = 1; width <= 5; width++) {
  for (let value = 1; value < 2 ** width; value++) {
    for (let rightUnary = 0; rightUnary <= 3; rightUnary++) {
      const leftContext = [
        1, 0, 1, 1, (value + width + rightUnary) % 2, 0, 1,
      ];
      const result = simulateInc0(
        leftContext, width, value, rightUnary, 0
      );
      exhaustiveCases++;
      if (!result.ok) {
        failures.push({
          family: "exhaustive",
          width,
          value,
          rightUnary,
          ...result,
        });
      }
    }
  }
}

// Deterministic LCG, seed fixed for reproducibility. Contexts include the
// empty list, long lists, arbitrary bit patterns, and translated head sites.
let seed = 0x0bb6;
function rand(n) {
  seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0;
  return seed % n;
}

let seededCases = 0;
for (let t = 0; t < 1200; t++) {
  const width = 1 + rand(8);
  const value = 1 + rand(2 ** width - 1);
  const rightUnary = rand(6);
  const contextLength = rand(50);
  const leftContext = Array.from(
    { length: contextLength },
    () => rand(2)
  );
  const head = rand(201) - 100;
  const result = simulateInc0(
    leftContext, width, value, rightUnary, head
  );
  seededCases++;
  if (!result.ok) {
    failures.push({
      family: "seeded",
      width,
      value,
      rightUnary,
      contextLength,
      head,
      ...result,
    });
  }
}

const report = {
  exhaustiveCases,
  seededCases,
  totalCases: exhaustiveCases + seededCases,
  failures: failures.length,
  finalSeed: seed,
  examples: failures.slice(0, 10),
};

console.log(JSON.stringify(report, null, 2));
if (failures.length !== 0) process.exitCode = 1;
