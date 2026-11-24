#!/usr/bin/env node
"use strict";

// Exact finite cross-match between the 84 source queue tables, the 124
// canonical open residual tables, and the 34 existing source-safe parents.
// It also simulates the first undefined transition of the 50 remaining
// tables to generate candidate (n,h) inputs for source_hole_atb.
//
// This is reproducible data analysis, not a safety proof. The Coq checker
// source_hole_atb / source_tree_check must verify any generated first-hole data.
//
// Run from any working directory:
//   node im-results/agent50-weighted-tnf-pilot/q32-canonical-crossmatch.js
//   node im-results/agent50-weighted-tnf-pilot/q32-canonical-crossmatch.js --list

const fs = require("node:fs");
const path = require("node:path");

const queuePath = path.resolve(
  __dirname,
  "../agent8-adaptive-source-plan/Agent8PackedChunk2_32_32.v"
);
const canonicalPath = path.resolve(
  __dirname,
  "../agent13-roster-convergence/canonical-124.json"
);
const chunkPath = path.resolve(
  __dirname,
  "../agent47-rooted-tnf/Agent47SourceChunk2.v"
);
const sweepPath = path.resolve(
  __dirname,
  "../agent47-rooted-tnf/Agent47SourceSweep.v"
);

const queueSource = fs.readFileSync(queuePath, "utf8");
const canonical = JSON.parse(fs.readFileSync(canonicalPath, "utf8"));
const chunkSource = fs.readFileSync(chunkPath, "utf8");
const sweepSource = fs.readFileSync(sweepPath, "utf8");

// Agent32SourceEncoding stores each state as two adjacent 3-character rows;
// '---' is an unassigned row. Six state groups give the canonical 12 slots
// A0,A1,B0,B1,...,F0,F1.
function decodeTable(serialized) {
  const groups = serialized.split("_");
  if (groups.length !== 6 || groups.some((g) => g.length !== 6)) {
    throw new Error("Malformed table: " + serialized);
  }
  return groups.flatMap((group) =>
    [group.slice(0, 3), group.slice(3, 6)].map((row) =>
      row === "---" ? null : row
    )
  );
}

function refines(child, parent) {
  return parent.every((row, i) => row === null || child[i] === row);
}

const queueRows = [
  ...queueSource.matchAll(
    /\("([01A-FLR-]+(?:_[01A-FLR-]+){5})",\s*\d+,\s*\d+\)/g
  ),
].map((m) => m[1]);
const sideCertificateRows = [
  ...chunkSource.matchAll(
    /\("([01A-FLR-]+(?:_[01A-FLR-]+){5})",\s*SWside/g
  ),
].map((m) => m[1]);

function sweepTable(name) {
  const match = sweepSource.match(
    new RegExp("Lemma " + name + "[\\s\\S]*?TM_from_str \"([^\"]+)\"")
  );
  if (!match) throw new Error("Missing serialized sweep table " + name);
  return match[1];
}

const sweepRows = [
  sweepTable("sweep_true_table"),
  sweepTable("sweep_false_table"),
];

if (queueRows.length !== 84) {
  throw new Error("Expected 84 packed queue tables, found " + queueRows.length);
}
if (canonical.entries.length !== 124) {
  throw new Error(
    "Expected 124 canonical entries, found " + canonical.entries.length
  );
}
if (sideCertificateRows.length !== 32 || sweepRows.length !== 2) {
  throw new Error(
    "Expected 32 literal SWside tables plus 2 sweep tables; found " +
      sideCertificateRows.length + " and " + sweepRows.length
  );
}

const queueTables = queueRows.map(decodeTable);
const canonicalMatches = queueTables.map((child) =>
  canonical.entries
    .filter((entry) => refines(child, entry.table))
    .map((entry) => entry.canonical_index)
);
const sourceParents = [...sideCertificateRows, ...sweepRows].map(decodeTable);
const sourceMatches = queueTables.map((child) =>
  sourceParents
    .map((parent, i) => (refines(child, parent) ? i : null))
    .filter((i) => i !== null)
);
const remaining = queueTables.filter((_, i) => sourceMatches[i].length === 0);
const holeHistogram = {};
for (const table of remaining) {
  const holes = table.filter((row) => row === null).length;
  holeHistogram[holes] = (holeHistogram[holes] || 0) + 1;
}

// Deterministic blank-tape simulator. steps is the number of ordinary
// transitions before the first undefined row is queried, matching n in
// source_hole_atb p n h. Repeated full configurations are detected exactly.
function firstHole(table, maxSteps = 3000) {
  const tape = new Map();
  let head = 0;
  let state = 0;
  const seen = new Set();

  for (let step = 0; step <= maxSteps; step++) {
    const nonblank = [...tape.entries()]
      .filter(([, bit]) => bit !== 0)
      .sort((a, b) => a[0] - b[0])
      .map(([i, bit]) => i + ":" + bit)
      .join(",");
    const key = state + "|" + head + "|" + nonblank;
    if (seen.has(key)) return { status: "cycle", steps: step };
    seen.add(key);

    const symbol = tape.get(head) || 0;
    const slot = 2 * state + symbol;
    const row = table[slot];
    if (row === null) {
      return {
        status: "hole",
        steps: step,
        state: "ABCDEF"[state],
        symbol,
        slot,
      };
    }

    const write = Number(row[0]);
    const direction = row[1];
    const nextState = "ABCDEF".indexOf(row[2]);
    if (nextState < 0) throw new Error("Bad next state in row " + row);
    if (write === 0) tape.delete(head);
    else tape.set(head, 1);
    head += direction === "L" ? -1 : 1;
    state = nextState;
  }

  return { status: "limit", steps: maxSteps + 1 };
}

const firstHoles = remaining.map((table, queueIndex) => ({
  queueIndex,
  ...firstHole(table),
}));
const firstHoleTimeHistogram = {};
const firstHoleSlotHistogram = {};
for (const item of firstHoles) {
  if (item.status !== "hole") continue;
  firstHoleTimeHistogram[item.steps] =
    (firstHoleTimeHistogram[item.steps] || 0) + 1;
  const slot = item.state + item.symbol;
  firstHoleSlotHistogram[slot] = (firstHoleSlotHistogram[slot] || 0) + 1;
}
const maxFirstHole = Math.max(
  0,
  ...firstHoles.filter((x) => x.status === "hole").map((x) => x.steps)
);
const parent7 = canonical.entries.find((entry) => entry.canonical_index === 7);
const result = {
  queue_count: queueTables.length,
  canonical_count: canonical.entries.length,
  canonical_parent_matches: canonicalMatches
    .map((xs) => xs.join(","))
    .reduce((acc, x) => {
      acc[x] = (acc[x] || 0) + 1;
      return acc;
    }, {}),
  all_84_refine_only_canonical_parent_7: canonicalMatches.every(
    (xs) => xs.length === 1 && xs[0] === 7
  ),
  canonical_parent_7: {
    raw_residual_index: parent7.raw_residual_index,
    address: parent7.address,
    depth: parent7.depth,
    holes: parent7.holes,
    table: parent7.table,
  },
  source_safe_parent_counts: {
    literal_SWside_tables: sideCertificateRows.length,
    sweep_tables: sweepRows.length,
    total_parent_tables: sourceParents.length,
  },
  source_queue_coverage: {
    covered_nodes: queueTables.length - remaining.length,
    remaining_nodes: remaining.length,
    remaining_hole_histogram: holeHistogram,
    remaining_one_hole_nodes: holeHistogram[1] || 0,
    first_hole_status_counts: firstHoles.reduce((acc, x) => {
      acc[x.status] = (acc[x.status] || 0) + 1;
      return acc;
    }, {}),
    first_hole_time_histogram: firstHoleTimeHistogram,
    first_hole_slot_histogram: firstHoleSlotHistogram,
    max_first_hole_steps: maxFirstHole,
    first_hole_data: process.argv.includes("--list") ? firstHoles : undefined,
    remaining_tables: process.argv.includes("--list")
      ? remaining.map((table) => table.map((row) => row ?? "---").join("_"))
      : undefined,
  },
};

console.log(JSON.stringify(result, null, 2));
if (
  !result.all_84_refine_only_canonical_parent_7 ||
  remaining.length !== 50 ||
  (holeHistogram[1] || 0) !== 0 ||
  firstHoles.some((x) => x.status !== "hole") ||
  maxFirstHole !== 18
) {
  process.exitCode = 1;
}
