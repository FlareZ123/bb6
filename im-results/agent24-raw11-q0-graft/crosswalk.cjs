#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");

const root = path.resolve(__dirname, "../..");
const readJson = (p) => JSON.parse(fs.readFileSync(path.join(root, p), "utf8"));
const q0 = readJson("im-results/agent5-weighted-tnf-queue/q0-open-automata.json");
const checkpoint = readJson("im-results/agent5-weighted-tnf-queue/q0-export/pilot-0-100-fuel-1000000.json");
const raw11 = readJson("im-results/agent44-raw11-fresh-cut/fresh-frontier.json");
const q32Source = fs.readFileSync(path.join(root, "im-results/agent24-q32-source-graft/Q32SideLeafRoster.lean"), "utf8");

const frontier = raw11.frontier.map((table, index) => ({ index, table: typeof table === "string" ? table : table.table }));
const checkpointRows = [
  ...checkpoint.active.map((x, index) => ({ index, kind: "active", table: x.table })),
  ...checkpoint.held.map((x, index) => ({ index: checkpoint.active.length + index, kind: "held", table: x.table })),
];
const q0Leaves = Object.entries(q0).map(([id, x]) => ({ id, table: x.table }));

function parseSection(source, start, end, regex) {
  const i = source.indexOf(start);
  if (i < 0) throw new Error("missing section: " + start);
  const j = source.indexOf(end, i);
  if (j < 0) throw new Error("missing section end: " + end);
  const section = source.slice(i, j);
  const rows = [];
  let m;
  while ((m = regex.exec(section)) !== null) rows.push(m);
  return rows;
}

const queueMatches = parseSection(
  q32Source,
  "def q32QueueData : List Q32QueueRecord :=",
  "theorem q32QueueData_length",
  /⟨"([^"]+)",\s*(\d+),\s*(\d+)⟩/g
);
const q32Queue = queueMatches.map((m, index) => ({ index, table: m[1], holes: Number(m[2]), cut: Number(m[3]) }));
const sideMatches = parseSection(
  q32Source,
  "def q32SideData : List Q32SideData :=",
  "theorem q32SideData_sourceExact",
  /⟨(\d+),\s*"([^"]+)",\s*\d+,\s*\d+,\s*(?:true|false),/g
);
const q32Side = sideMatches.map((m) => ({ index: Number(m[1]), table: m[2] }));

function slots(table) {
  const compact = table.replaceAll("_", "");
  if (compact.length !== 36) throw new Error("bad table length: " + table);
  return compact.match(/.{3}/g).map((x) => x === "---" ? null : x);
}
function refines(child, parent) {
  const c = slots(child), p = slots(parent);
  return p.every((v, i) => v === null || c[i] === v);
}
function compatible(a, b) {
  const x = slots(a), y = slots(b);
  return x.every((v, i) => v === null || y[i] === null || v === y[i]);
}
function hits(table, rows, relation) {
  return rows.map((x, i) => relation(table, x.table) ? i : null).filter((x) => x !== null);
}
function histogram(items, key) {
  const out = {};
  for (const x of items) {
    const k = key(x);
    out[k] = (out[k] || 0) + 1;
  }
  return Object.fromEntries(Object.entries(out).sort(([a], [b]) => a.localeCompare(b)));
}
function pairCount(xs, ys = xs, same = false) {
  let n = 0;
  for (let i = 0; i < xs.length; i++) {
    for (let j = same ? i + 1 : 0; j < ys.length; j++) {
      if (compatible(xs[i].table, ys[j].table)) n++;
    }
  }
  return n;
}

const checkpointCross = checkpointRows.map((x) => ({
  ...x,
  frontierRefines: hits(x.table, frontier, refines),
  frontierOverlaps: hits(x.table, frontier, compatible),
}));
const q0Cross = q0Leaves.map((x) => ({
  ...x,
  frontierRefines: hits(x.table, frontier, refines),
  checkpointParents: checkpointRows.filter((p) => refines(x.table, p.table)).map((p) => p.index),
}));
const q32SideCross = q32Side.map((x) => ({
  ...x,
  frontierRefines: hits(x.table, frontier, refines),
  queueRows: q32Queue.filter((p) => p.table === x.table).map((p) => p.index),
}));
const q32QueueCross = q32Queue.map((x) => ({
  ...x,
  frontierRefines: hits(x.table, frontier, refines),
}));

const unmapped = checkpointCross.filter((x) => x.frontierRefines.length === 0);
const coarse = unmapped.filter((x) => x.frontierOverlaps.length > 1);
const noOverlap = unmapped.filter((x) => x.frontierOverlaps.length === 0);
const q0ParentCounts = {};
for (const x of q0Cross) {
  if (x.checkpointParents.length !== 1) throw new Error("q0 leaf " + x.id + " has " + x.checkpointParents.length + " checkpoint parents");
  const k = String(x.checkpointParents[0]);
  q0ParentCounts[k] = (q0ParentCounts[k] || 0) + 1;
}
const checkpointFrontierHistogram = histogram(checkpointCross, (x) => x.frontierOverlaps.join(",") || "none");
const q0FrontierHistogram = histogram(q0Cross, (x) => x.frontierRefines.join(",") || "none");
const q32SideFrontierHistogram = histogram(q32SideCross, (x) => x.frontierRefines.join(",") || "none");
const q32QueueFrontierHistogram = histogram(q32QueueCross, (x) => x.frontierRefines.join(",") || "none");

const output = {
  status: "finite table crosswalk; not a parent Cover",
  raw11: { frontierCount: frontier.length, parent: "1RB---_1RC---_0LA---_------_------_------" },
  q0Checkpoint: {
    active: checkpoint.active.length,
    held: checkpoint.held.length,
    total: checkpointRows.length,
    frontierOverlapHistogram: checkpointFrontierHistogram,
    singleFrontierRefinements: checkpointCross.filter((x) => x.frontierRefines.length === 1).length,
    unmatchedCount: unmapped.length,
    noFrontierOverlap: noOverlap.map((x) => ({ index: x.index, kind: x.kind, table: x.table })),
    fourWayResidualParents: coarse.map((x) => ({ index: x.index, table: x.table, frontierIndices: x.frontierOverlaps })),
  },
  q0Automata: {
    count: q0Leaves.length,
    frontierRefinementHistogram: q0FrontierHistogram,
    checkpointParentCounts: Object.fromEntries(Object.entries(q0ParentCounts).sort(([a], [b]) => Number(a) - Number(b))),
    pairwiseCompatiblePairs: pairCount(q0Leaves, q0Leaves, true),
  },
  q32: {
    queueRows: q32Queue.length,
    queueFrontierRefinementHistogram: q32QueueFrontierHistogram,
    sideLeaves: q32Side.length,
    sideFrontierRefinementHistogram: q32SideFrontierHistogram,
    sideRowsMissingExactQueueMatch: q32SideCross.filter((x) => x.queueRows.length !== 1).map((x) => x.index),
    sidePairwiseCompatiblePairs: pairCount(q32Side, q32Side, true),
  },
  crossFamily: {
    q0AutomataVsQ32SideCompatiblePairs: pairCount(q0Leaves, q32Side),
    q0AutomataVsCheckpointCompatiblePairs: pairCount(q0Leaves, checkpointRows),
    q32SideVsCheckpointCompatiblePairs: pairCount(q32Side, checkpointRows),
  },
};

function assertEq(actual, expected, label) {
  if (JSON.stringify(actual) !== JSON.stringify(expected)) {
    throw new Error(label + ": got " + JSON.stringify(actual) + ", expected " + JSON.stringify(expected));
  }
}
if (frontier.length !== 116) throw new Error("Raw11 frontier length changed");
if (checkpointRows.length !== 157 || checkpoint.active.length !== 156 || checkpoint.held.length !== 1) throw new Error("q0 checkpoint cardinality changed");
if (q0Leaves.length !== 94 || q32Queue.length !== 84 || q32Side.length !== 32) throw new Error("source roster cardinality changed");
if (!checkpointRows.every((x) => refines(x.table, output.raw11.parent))) throw new Error("q0 checkpoint row does not refine Raw11 parent");
if (!q0Leaves.every((x) => refines(x.table, output.raw11.parent))) throw new Error("q0 automata leaf does not refine Raw11 parent");
if (!q32Queue.every((x) => refines(x.table, output.raw11.parent))) throw new Error("q32 queue row does not refine Raw11 parent");
if (!q32Side.every((x) => refines(x.table, output.raw11.parent))) throw new Error("q32 side leaf does not refine Raw11 parent");
assertEq(checkpointFrontierHistogram, {
  "100,101,102,103": 1, "104,105,106,107": 1, "109,110,111,112": 1,
  "14,15,16,17": 1, "24": 20, "25": 20, "90,91,92,93": 1,
  "94": 1, "95,96,97,98": 1, "99": 1, "108": 1, "113": 1,
  "114": 20, "115": 77, "none": 10
}, "q0 checkpoint frontier histogram");
assertEq(q0FrontierHistogram, { "115": 94 }, "q0 automata frontier histogram");
assertEq(q32SideFrontierHistogram, { "114": 2, "115": 30 }, "q32 side frontier histogram");
assertEq(q32QueueFrontierHistogram, { "114": 14, "115": 70 }, "q32 queue frontier histogram");
assertEq(Object.fromEntries(Object.entries(q0ParentCounts).sort(([a], [b]) => Number(a) - Number(b))), {
  "26":13,"33":1,"34":4,"39":16,"44":5,"46":1,"48":2,"49":21,"51":31
}, "q0 automata checkpoint parents");
assertEq(noOverlap.map((x) => x.index), [136,137,139,144,145,146,147,152,153,155], "no-overlap q0 rows");
assertEq(coarse.map((x) => x.index), [138,140,141,142,143,154], "four-way q0 rows");
assertEq(coarse.map((x) => x.frontierOverlaps), [
  [100,101,102,103],[90,91,92,93],[95,96,97,98],[104,105,106,107],[109,110,111,112],[14,15,16,17]
], "q0 four-way complements");
if (pairCount(q0Leaves, q0Leaves, true) !== 0) throw new Error("q0 automata leaves overlap");
if (pairCount(q32Side, q32Side, true) !== 0) throw new Error("q32 side leaves overlap");
if (pairCount(q0Leaves, q32Side) !== 0) throw new Error("q0 and q32 side leaves overlap");
if (output.crossFamily.q0AutomataVsCheckpointCompatiblePairs !== 94) throw new Error("q0 automata/checkpoint pairing changed");
if (output.crossFamily.q32SideVsCheckpointCompatiblePairs !== 10) throw new Error("q32 side/checkpoint overlap count changed");

const json = JSON.stringify(output, null, 2) + "\n";
if (process.argv.includes("--write")) {
  fs.writeFileSync(path.join(__dirname, "crosswalk.json"), json);
}
process.stdout.write(json);
