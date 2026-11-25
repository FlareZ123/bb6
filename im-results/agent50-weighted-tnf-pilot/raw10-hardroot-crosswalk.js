#!/usr/bin/env node
"use strict";

// Exact finite crosswalk from the 15 literal hard roots to the current
// B0=1LC residual boxes. Run from the repository root:
//   node im-results/agent50-weighted-tnf-pilot/raw10-hardroot-crosswalk.js
//
// This reproduces BoxComplement.subtractMany in ordinary JavaScript. It is
// a finite data audit, not a proof; the Lean count/mass theorems remain the
// trusted checks of the 41-box partition.

const fs = require("node:fs");
const read = p => fs.readFileSync(p, "utf8");
const rootFile = "im-results/agent19-hard-root-crosswalk/HardRootLeaves.lean";
const encodedFile = "im-results/agent49-box-complement/Raw10Encoded.lean";
const cycleFile = "im-results/agent50-weighted-tnf-pilot/Raw10Box8Cycle.lean";
const haltFile = "im-results/agent50-weighted-tnf-pilot/Raw10Box0Halt.lean";

function moveCode(write, right, next) {
  return 1 + 4 * Number(next) + 2 * (write === "true" ? 1 : 0)
    + (right === "true" ? 1 : 0);
}

function parseLiteralMachines(source) {
  const out = {};
  for (const match of source.matchAll(/def (\w+) : Machine := literal \[([\s\S]*?)\]/g)) {
    const row = [...match[2].matchAll(/some ⟨(true|false),(true|false),(\d+)⟩|none/g)]
      .map(x => x[0] === "none" ? 0 : moveCode(x[1], x[2], x[3]));
    if (row.length !== 12) throw new Error("Expected 12 slots for " + match[1] + ", got " + row.length);
    out[match[1]] = row;
  }
  return out;
}

function parseEncodedRows(source) {
  const match = source.match(/def rows : List \(List Nat\) := \[([\s\S]*?)\]\ndef slots/);
  if (!match) throw new Error("Could not find Raw10Encoded.rows");
  const rows = [...match[1].matchAll(/\[([0-9,\s]+)\]/g)]
    .map(x => x[1].split(",").map(v => Number(v.trim())));
  if (rows.length !== 66 || rows.some(r => r.length !== 12))
    throw new Error("Expected 66 twelve-slot rows (65 side witnesses + held), got " + rows.length);
  return rows;
}

// Convert a Lean PartialMachine definition into a cube. Unlike the compact
// Raw10Encoded rows, this parser retains fixed halt values as transition 0.
function parsePartialCube(source, name) {
  const start = source.indexOf("def " + name + " : PartialMachine :=");
  if (start < 0) throw new Error("Missing PartialMachine " + name);
  const end = source.indexOf("\n\ndef witness", start);
  if (end < 0) throw new Error("Missing end of PartialMachine " + name);
  const body = source.slice(start, end);
  const pairs = [];
  for (const x of body.matchAll(/s = \((\d+),(false|true)\) then some \(some ⟨(true|false),(true|false),(\d+)⟩\)/g)) {
    pairs.push([2 * Number(x[1]) + (x[2] === "true" ? 1 : 0), moveCode(x[3], x[4], x[5])]);
  }
  for (const x of body.matchAll(/s = \((\d+),(false|true)\) then some none/g)) {
    pairs.push([2 * Number(x[1]) + (x[2] === "true" ? 1 : 0), 0]);
  }
  pairs.sort((a, b) => a[0] - b[0]);
  if (pairs.length === 0) throw new Error("No assigned slots parsed for " + name);
  return pairs;
}

function rowCube(row) {
  // In Raw10Encoded, zero means wildcard, not halt.
  return row.flatMap((v, s) => v === 0 ? [] : [[s, v]]);
}

function subtract(box, cube) {
  // Exact first-mismatch decomposition from BoxComplement.subtract.
  if (cube.some(([s, v]) => !box[s].includes(v))) return [box];
  const pieces = [];
  let accepted = box.map(domain => domain.slice());
  for (const [s, v] of cube) {
    const rejected = accepted.map(domain => domain.slice());
    rejected[s] = rejected[s].filter(x => x !== v);
    if (rejected.every(domain => domain.length > 0)) pieces.push(rejected);
    accepted = accepted.map(domain => domain.slice());
    accepted[s] = [v];
  }
  return pieces;
}

function subtractMany(initial, cubes) {
  let boxes = [initial];
  for (const cube of cubes) boxes = boxes.flatMap(box => subtract(box, cube));
  return boxes;
}

function mass(boxes) {
  return boxes.reduce((sum, box) =>
    sum + box.reduce((product, domain) => product * domain.length, 1), 0);
}

function leafCube(machine) {
  const holes = machine.map((v, s) => v === 0 ? s : null).filter(x => x !== null);
  if (holes.length !== 1) throw new Error("Expected one halt row, got holes " + holes);
  // Erasing the sole halt row leaves a one-hole, 25-completion cylinder.
  return machine.flatMap((v, s) => v === 0 ? [] : [[s, v]]);
}

function boxContainsLeaf(box, machine) {
  return machine.every((v, s) => {
    if (v === 0) return box[s].length === 25;
    return box[s].includes(v);
  });
}

const machines = parseLiteralMachines(read(rootFile));
const encodedRows = parseEncodedRows(read(encodedFile));
const cycleCube = parsePartialCube(read(cycleFile), "table");
const haltCube = parsePartialCube(read(haltFile), "haltTable");
const certificates = [
  ...encodedRows.map(rowCube), // 65 side witnesses, then q_i(2800,100) held leaf
  cycleCube,
  haltCube
];
const allTransitions = Array.from({length: 25}, (_, i) => i);
const parent = Array.from({length: 12}, (_, s) =>
  s === 0 ? [8] : s === 2 ? [11] : allTransitions.slice());
const boxes = subtractMany(parent, certificates);
const residualMass = mass(boxes);
if (boxes.length !== 41 || residualMass !== 90737503713725)
  throw new Error("Partition mismatch: " + boxes.length + " boxes, mass " + residualMass);

const roots = ["C", "D0", "D2", "r1"].map(name => {
  const machine = machines[name];
  if (!machine) throw new Error("Missing root " + name);
  const cube = leafCube(machine);
  const containing = boxes.map((box, index) => ({box, index}))
    .filter(x => boxContainsLeaf(x.box, machine));
  if (containing.length !== 1)
    throw new Error(name + ": expected one containing residual box, got " + containing.length);
  return {
    name,
    hole_slot: machine.findIndex(v => v === 0),
    residual_box: containing[0].index,
    leaf_completions: 25,
    leaf_cube: cube,
    box_domain_sizes: containing[0].box.map(domain => domain.length)
  };
});

const r1Cube = leafCube(machines.r1);
const refined = subtractMany(parent, [...certificates, r1Cube]);
const refinedMass = mass(refined);
if (refinedMass !== residualMass - 25)
  throw new Error("r1 subtraction did not remove exactly 25: " + refinedMass);

console.log(JSON.stringify({
  certificates: certificates.length,
  residual_boxes: boxes.length,
  residual_mass: residualMass,
  after_r1: {
    residual_boxes: refined.length,
    residual_mass: refinedMass,
    mass_removed: residualMass - refinedMass
  },
  roots,
  box0_domains: boxes[0],
  box24_domains: boxes[24]
}, null, 2));
