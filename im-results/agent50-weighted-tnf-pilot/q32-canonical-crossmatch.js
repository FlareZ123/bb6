#!/usr/bin/env node
"use strict";

// Exact finite cross-match between the 84 source queue tables, the 124
// canonical open residual tables, and the 34 existing source-safe parents.
// This is reproducible data analysis, not a safety proof: containment only
// identifies which certified or canonical cylinder contains each queue node.
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
    throw new Error(`Malformed table: ${serialized}`);
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
    new RegExp(`Lemma ${name}[\\s\\S]*?TM_from_str "([^"]+)"`)
  );
  if (!match) throw new Error(`Missing serialized sweep table ${name}`);
  return match[1];
}

const sweepRows = [
  sweepTable("sweep_true_table"),
  sweepTable("sweep_false_table"),
];

if (queueRows.length !== 84) {
  throw new Error(`Expected 84 packed queue tables, found ${queueRows.length}`);
}
if (canonical.entries.length !== 124) {
  throw new Error(
    `Expected 124 canonical entries, found ${canonical.entries.length}`
  );
}
if (sideCertificateRows.length !== 32 || sweepRows.length !== 2) {
  throw new Error(
    `Expected 32 literal SWside tables plus 2 sweep tables; found ${sideCertificateRows.length} and ${sweepRows.length}`
  );
}

const queueTables = queueRows.map(decodeTable);
const canonicalTables = canonical.entries.map((entry) => entry.table);
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
    remaining_tables: process.argv.includes("--list")
      ? remaining.map((table) => table.map((row) => row ?? "---").join("_"))
      : undefined,
  },
};

console.log(JSON.stringify(result, null, 2));
if (
  !result.all_84_refine_only_canonical_parent_7 ||
  remaining.length !== 50 ||
  (holeHistogram[1] || 0) !== 0
) {
  process.exitCode = 1;
}
