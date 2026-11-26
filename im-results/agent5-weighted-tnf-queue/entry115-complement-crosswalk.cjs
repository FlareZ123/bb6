#!/usr/bin/env node
'use strict';

// Exact finite-table crosswalk for the Raw11 first-D frontier entry 115.
// This is a syntactic containment/disjointness audit, not a Cover theorem.

const fs = require('node:fs');
const path = require('node:path');
const ROOT = path.resolve(__dirname, '../..');

function readJson(relative) {
  return JSON.parse(fs.readFileSync(path.join(ROOT, relative), 'utf8'));
}
function parseSection(source, start, end, pattern) {
  const a = source.indexOf(start);
  const b = source.indexOf(end, a);
  if (a < 0 || b < 0) throw new Error('missing Lean data section: ' + start);
  return [...source.slice(a, b).matchAll(pattern)];
}
function slots(table) {
  const compact = table.replaceAll('_', '');
  if (compact.length !== 36) throw new Error('bad table length: ' + table);
  return compact.match(/.{3}/g).map((x) => x === '---' ? null : x);
}
function refines(child, parent) {
  return parent.every((value, i) => value === null || child[i] === value);
}
function compatible(a, b) {
  return a.every((value, i) => value === null || b[i] === null || value === b[i]);
}
function pairList(left, right) {
  const pairs = [];
  for (const x of left) for (const y of right) {
    if (compatible(x.slots, y.slots)) pairs.push({ x, y });
  }
  return pairs;
}
function pairwiseCount(rows) {
  let count = 0;
  for (let i = 0; i < rows.length; i++) {
    for (let j = i + 1; j < rows.length; j++) {
      if (compatible(rows[i].slots, rows[j].slots)) count++;
    }
  }
  return count;
}
function histogram(rows, key) {
  const out = {};
  for (const row of rows) {
    const value = key(row);
    out[value] = (out[value] || 0) + 1;
  }
  return Object.fromEntries(Object.entries(out).sort(([a], [b]) => a.localeCompare(b)));
}
function assertEqual(actual, expected, label) {
  if (JSON.stringify(actual) !== JSON.stringify(expected)) {
    throw new Error(label + ': expected ' + JSON.stringify(expected) +
      ', got ' + JSON.stringify(actual));
  }
}

const frontier = readJson('im-results/agent44-raw11-fresh-cut/fresh-frontier.json');
const route = readJson('im-results/agent47-raw11-adapter/raw11-route.json');
const checkpoint = readJson('im-results/agent5-weighted-tnf-queue/q0-export/pilot-0-100-fuel-1000000.json');
const q0Automata = readJson('im-results/agent5-weighted-tnf-queue/q0-open-automata.json');
const q32Source = fs.readFileSync(
  path.join(ROOT, 'im-results/agent24-q32-source-graft/Q32SideLeafRoster.lean'), 'utf8');

const entry = frontier.frontier[115];
if (frontier.frontier.length !== 116 ||
    entry !== '1RB1RD_1RC---_0LA---_------_------_------') {
  throw new Error('Raw11 frontier entry 115 changed');
}
const parent = slots(entry);
const q0Rows = [
  ...checkpoint.active.map((x, index) => ({ index, kind: 'active', table: x.table })),
  ...checkpoint.held.map((x, index) => ({
    index: checkpoint.active.length + index, kind: 'held', table: x.table
  }))
].map((x) => ({ ...x, slots: slots(x.table) }))
 .filter((x) => refines(x.slots, parent));

const extras = route.extra.map((table, id) => ({ id, table, slots: slots(table) }))
  .filter((x) => refines(x.slots, parent));

const q0Leaves = Object.entries(q0Automata).map(([name, value]) => ({
  name, table: value.table, slots: slots(value.table)
})).filter((x) => refines(x.slots, parent));

const queueSection = parseSection(
  q32Source,
  'def q32QueueData : List Q32QueueRecord :=',
  'theorem q32QueueData_length',
  /⟨"([^"]+)",\s*(\d+),\s*(\d+)⟩/g
);
const sideSection = parseSection(
  q32Source,
  'def q32SideData : List Q32SideData :=',
  'theorem q32SideData_sourceExact',
  /⟨(\d+),\s*"([^"]+)",\s*\d+,\s*\d+,\s*(?:true|false),/g
);
const q32Queue = queueSection.map((m, index) => ({
  index, table: m[1], holes: Number(m[2]), cut: Number(m[3]), slots: slots(m[1])
}));
const q32Side = sideSection.map((m) => ({
  index: Number(m[1]), table: m[2], slots: slots(m[2])
}));
const q32Side115 = q32Side.filter((x) => refines(x.slots, parent));
const q32Side114 = q32Side.filter((x) => refines(x.slots, slots(frontier.frontier[114])));
const q32Queue115 = q32Queue.filter((x) => refines(x.slots, parent));
const q32Queue114 = q32Queue.filter((x) => refines(x.slots, slots(frontier.frontier[114])));

const q32ExtraPairs = pairList(q32Side115, extras);
const q32CheckpointPairs = pairList(q32Side115, q0Rows);
const q32AutomataPairs = pairList(q32Side115, q0Leaves);
const q0ExtraPairs = pairList(q0Rows, extras);
const q0AutomataExtraPairs = pairList(q0Leaves, extras);
const q0AutomataSidePairs = pairList(q0Leaves, q32Side115);

const q32ContainedInExtra = q32Side115.filter((side) =>
  extras.some((extra) => refines(side.slots, extra.slots)));
const q32ExactQ0 = q32Side115.filter((side) =>
  q0Rows.some((row) => side.table.replaceAll('_', '') === row.table.replaceAll('_', '')));
const q32Independent = q32Side115.filter((side) =>
  !extras.some((extra) => compatible(side.slots, extra.slots)) &&
  !q0Rows.some((row) => compatible(side.slots, row.slots)) &&
  !q0Leaves.some((leaf) => compatible(side.slots, leaf.slots)));

const moves = [
  '0LA','0RA','1LA','1RA','0LB','0RB','1LB','1RB',
  '0LC','0RC','1LC','1RC','0LD','0RD','1LD','1RD',
  '0LE','0RE','1LE','1RE','0LF','0RF','1LF','1RF'
];
const d0 = (row) => row.slots[6] ?? 'undefined';
const q0D0 = histogram(q0Rows, d0);
const q32D0 = histogram(q32Side115, d0);

assertEqual(q0Rows.length, 77, 'q0 checkpoint rows under entry 115');
assertEqual(pairwiseCount(q0Rows), 0, 'q0 checkpoint row disjointness');
assertEqual(extras.length, 58, 'Raw11 extra parents under entry 115');
assertEqual(pairwiseCount(extras), 0, 'Raw11 extra parent disjointness');
assertEqual(q0ExtraPairs.length, 0, 'q0 checkpoint / Raw11 extra disjointness');
assertEqual(q0Leaves.length, 94, 'q0 automata leaves under entry 115');
assertEqual(pairwiseCount(q0Leaves), 0, 'q0 automata leaf disjointness');
assertEqual(q0AutomataExtraPairs.length, 0, 'q0 automata / Raw11 extra disjointness');
assertEqual(q0AutomataSidePairs.length, 0, 'q0 automata / q32 side disjointness');
assertEqual(q32Queue.length, 84, 'q32 queue size');
assertEqual(q32Queue115.length, 70, 'q32 queue rows under entry 115');
assertEqual(q32Queue114.length, 14, 'q32 queue rows under entry 114');
assertEqual(q32Side.length, 32, 'q32 side leaf count');
assertEqual(q32Side115.length, 30, 'q32 side leaves under entry 115');
assertEqual(q32Side114.length, 2, 'q32 side leaves under entry 114');
assertEqual(pairwiseCount(q32Side), 0, 'q32 side leaf disjointness');
assertEqual(q32ExtraPairs.length, 18, 'q32 side / Raw11 extra overlaps');
assertEqual(q32CheckpointPairs.length, 8, 'q32 side / q0 checkpoint overlaps under entry 115');
assertEqual(q32AutomataPairs.length, 0, 'q32 side / q0 automata disjointness');
assertEqual(q32ContainedInExtra.length, 18, 'q32 side leaves contained in Raw11 extras');
assertEqual(q32ExactQ0.length, 8, 'q32 side leaves exactly matching q0 checkpoint rows');
assertEqual(q32Independent.length, 4, 'independent q32 side leaves under entry 115');
assertEqual(q32Independent.map((x) => x.index).sort((a,b) => a-b), [38,40,42,44],
  'independent q32 side leaf indices');
assertEqual(q32ExtraPairs.every((p) => refines(p.x.slots, p.y.slots) && p.y.id === 84), true,
  'all q32/extra overlaps refine Extra84');
assertEqual(q32CheckpointPairs.every((p) =>
  p.x.table.replaceAll('_', '') === p.y.table.replaceAll('_', '')), true,
  'all q32/checkpoint overlaps are exact rows');
assertEqual(q0Leaves.every((x) => x.slots[6] === '1LA'), true,
  'q0 automata D0 value');
assertEqual(extras.every((x) => x.slots[6] === '1LA'), true,
  'Raw11 extra D0 value');

const output = {
  status: 'finite syntactic crosswalk only; not a parent Cover',
  entry115: entry,
  q0Checkpoint: {
    rows: q0Rows.length,
    pairwiseCompatiblePairs: pairwiseCount(q0Rows),
    d0Distribution: q0D0,
    missingD0Values: moves.filter((move) => !q0D0[move])
  },
  raw11Extras: {
    parents: extras.length,
    ids: [Math.min(...extras.map((x) => x.id)), Math.max(...extras.map((x) => x.id))],
    d0Distribution: histogram(extras, d0),
    pairwiseCompatiblePairs: pairwiseCount(extras)
  },
  q0Automata: {
    leaves: q0Leaves.length,
    d0Distribution: histogram(q0Leaves, d0),
    pairwiseCompatiblePairs: pairwiseCount(q0Leaves),
    compatibleWithExtras: q0AutomataExtraPairs.length,
    compatibleWithQ32Side: q0AutomataSidePairs.length
  },
  q32: {
    queueRows: q32Queue.length,
    queueUnderEntry115: q32Queue115.length,
    queueUnderEntry114: q32Queue114.length,
    sideLeaves: q32Side.length,
    sideUnderEntry115: q32Side115.length,
    sideUnderEntry114: q32Side114.length,
    d0DistributionUnderEntry115: q32D0,
    sidePairwiseCompatiblePairs: pairwiseCount(q32Side),
    sideExtraOverlaps: q32ExtraPairs.map((p) => ({
      sideIndex: p.x.index, extraId: p.y.id, relation: 'side refines extra'
    })),
    sideCheckpointOverlaps: q32CheckpointPairs.map((p) => ({
      sideIndex: p.x.index, checkpointIndex: p.y.index, relation: 'exact table'
    })),
    independentSideLeaves: q32Independent.map((x) => ({ index: x.index, table: x.table }))
  },
  crossFamily: {
    q0CheckpointVsExtrasCompatiblePairs: q0ExtraPairs.length,
    q0AutomataVsExtrasCompatiblePairs: q0AutomataExtraPairs.length,
    q0AutomataVsQ32SideCompatiblePairs: q0AutomataSidePairs.length,
    q32SideVsExtrasCompatiblePairs: q32ExtraPairs.length,
    q32SideVsQ0CheckpointCompatiblePairs: q32CheckpointPairs.length
  }
};
console.log(JSON.stringify(output, null, 2));
