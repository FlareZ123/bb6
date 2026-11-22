#!/usr/bin/env node
"use strict";

// Exact finite closure for the 94-state paired carry transducer used in
// PairedCarry94Exploration.md.
//
// State: [px, py, leftA, leftB, rightA, rightB].
// Inputs: (x,y) in {0,1,2}^2.
// All quotients are Euclidean floor division by 3.

const assert = require("node:assert/strict");

const key = (s) => s.join(",");
const floor3 = (n) => Math.floor(n / 3);

function step([px, py, la, lb, ra, rb], x, y) {
  return [
    x,
    y,
    floor3(x - py + la),
    floor3(py + lb),
    floor3(-x - px - py + ra),
    floor3(px + py + rb),
  ];
}

const base66 = [];
for (let px = 0; px < 3; px++) {
  for (let py = 0; py < 3; py++) {
    for (const [la, lb] of [[-1, 0], [0, 0]]) {
      for (const [ra, rb] of [[-1, 0], [-2, 0], [-2, 1], [-3, 1]]) {
        const excluded =
          (px === 0 && la === 0 && ra === -3 && rb === 1) ||
          (px === 2 && la === -1 && ra === -1 && rb === 0);
        if (!excluded) base66.push([px, py, la, lb, ra, rb]);
      }
    }
  }
}
assert.equal(base66.length, 66);

const extraSeeds = [
  [0, 2, -2, 1, -1, 0],
  [0, 1, -1, 0, 0, 0],
];

const initial = new Map();
for (const s of [...base66, ...extraSeeds]) initial.set(key(s), s);
assert.equal(initial.size, 68);

const states = [...initial.values()];
const seen = new Set(states.map(key));
let frontier = states.slice();

while (frontier.length > 0) {
  const nextFrontier = [];
  for (const s of frontier) {
    for (let x = 0; x < 3; x++) {
      for (let y = 0; y < 3; y++) {
        const t = step(s, x, y);
        const k = key(t);
        if (!seen.has(k)) {
          seen.add(k);
          states.push(t);
          nextFrontier.push(t);
        }
      }
    }
  }
  frontier = nextFrontier;
}

assert.equal(states.length, 94);
for (const s of states) {
  for (let x = 0; x < 3; x++) {
    for (let y = 0; y < 3; y++) {
      assert(seen.has(key(step(s, x, y))));
    }
  }
}

const projections = new Map();
for (const [px, py, la, lb, ra, rb] of states) {
  const k = `L(${la},${lb}) R(${ra},${rb})`;
  if (!projections.has(k)) projections.set(k, []);
  projections.get(k).push([px, py]);
}

const result = {
  base66: base66.length,
  extraSeeds,
  initialSeeds: initial.size,
  closureStates: states.length,
  generatedAfterSeeds: states.length - initial.size,
  carryRanges: {
    leftA: [-2, 0],
    leftB: [0, 1],
    rightA: [-3, 0],
    rightB: [0, 1],
  },
  projections: [...projections.entries()].map(([carryProjection, previousPairs]) => ({
    carryProjection,
    count: previousPairs.length,
    previousPairs: previousPairs.sort((a, b) => a[0] - b[0] || a[1] - b[1]),
  })),
  states: states.sort((a, b) => key(a).localeCompare(key(b))),
};

console.log(JSON.stringify(result, null, 2));
