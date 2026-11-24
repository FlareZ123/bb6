#!/usr/bin/env node
"use strict";

// Exact finite cross-match between the 84 source queue tables and the 124
// canonical open residual tables. This is reproducible data analysis, not a
// safety proof: containment only identifies which canonical cylinder contains
// each queue node.
//
// Run from any working directory:
//   node im-results/agent50-weighted-tnf-pilot/q32-canonical-crossmatch.js

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

const queueSource = fs.readFileSync(queuePath, "utf8");
const canonical = JSON.parse(fs.readFileSync(canonicalPath, "utf8"));

// Agent32SourceEncoding stores each state as two adjacent 3-character rows;
// '---' is an unassigned row. Six state groups give the canonical 12 slots
// A0,A1,B0,B1,...,F0,F1.
const packedRows = [
  ...queueSource.matchAll(
    /\("([01A-FLR-]+(?:_[01A-FLR-]+){5})",\s*\d+,\s*\d+\)/g
  ),
].map((m) => m[1]);

function decodeQueueTable(serialized) {
  const groups = serialized.split("_");
  if (groups.length !== 6 || groups.some((g) => g.length !== 6)) {
    throw new Error(`Malformed queue table: ${serialized}`);
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

if (packedRows.length !== 84) {
  throw new Error(`Expected 84 packed queue tables, found ${packedRows.length}`);
}
if (canonical.entries.length !== 124) {
  throw new Error(
    `Expected 124 canonical entries, found ${canonical.entries.length}`
  );
}

const queueTables = packedRows.map(decodeQueueTable);
const matches = queueTables.map((child) =>
  canonical.entries
    .filter((entry) => refines(child, entry.table))
    .map((entry) => entry.canonical_index)
);
const covered = matches.filter((xs) => xs.length > 0).length;
const uncovered = matches.filter((xs) => xs.length === 0).length;
const nonUnique = matches.filter((xs) => xs.length !== 1).length;
const parentCounts = new Map();
for (const xs of matches) {
  for (const i of xs) parentCounts.set(i, (parentCounts.get(i) || 0) + 1);
}

const parent = canonical.entries.find((entry) => entry.canonical_index === 7);
const result = {
  queue_count: queueTables.length,
  canonical_count: canonical.entries.length,
  covered_queue_count: covered,
  uncovered_queue_count: uncovered,
  queue_nodes_with_nonunique_parent: nonUnique,
  parent_coverage: [...parentCounts.entries()].sort((a, b) => a[0] - b[0]),
  unique_parent_index: [...parentCounts.keys()],
  canonical_parent_7: {
    raw_residual_index: parent.raw_residual_index,
    address: parent.address,
    depth: parent.depth,
    holes: parent.holes,
    table: parent.table,
  },
  all_84_refine_only_parent_7: matches.every(
    (xs) => xs.length === 1 && xs[0] === 7
  ),
};

console.log(JSON.stringify(result, null, 2));
if (!result.all_84_refine_only_parent_7) process.exitCode = 1;
