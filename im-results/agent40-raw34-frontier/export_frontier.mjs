#!/usr/bin/env node
/**
 * Constructive, exact 25-ary coverage/frontier DAG for original Raw34.
 *
 * Every covered terminal carries a source-accepted *local theorem family*
 * and the exact literal cylinder used. Every open terminal identifies a
 * disjoint still-unclassified partial table; "open" does NOT mean halting.
 *
 * Scope: finite physical tables. This script is NOT a Lean proof nor a
 * certified weighted Cover. The underlying nonhalting theorems reside in
 * agent50's separately accepted original-source Lean modules.
 *
 * Usage:
 *   node export_frontier.mjs 1RD > raw34-d1-1rd.json
 *   node export_frontier.mjs all > raw34-full-frontier.json
 */
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const dataDir = join(dirname(fileURLToPath(import.meta.url)), "../agent50-raw34-firsthole");
const depth2Data = JSON.parse(readFileSync(join(dataDir, "depth2-candidate-witnesses.json"), "utf8"));
const depth3Data = JSON.parse(readFileSync(join(dataDir, "depth3-candidate-witnesses.json"), "utf8"));
assert.equal(depth2Data.second_level.length, 74);
assert.equal(depth3Data.witnesses.length, 1206);

const alphabet = ["HALT"];
for (const write of "01")
  for (const direction of "LR")
    for (const state of "ABCDEF")
      alphabet.push(write + direction + state);
assert.equal(alphabet.length, 25);
assert.equal(new Set(alphabet).size, 25);

const raw34 = "1RB---_1RC---_0RD---_1LC---_------_------";
const originalSlots = raw34.replaceAll("_", "").match(/.{3}/g);
const fixed = new Map([[0, "1RB"], [2, "1RC"], [4, "0RD"], [6, "1LC"]]);
const slotOrder = [7, 5, 3, 1, 8, 9, 10, 11];
const slotNames = ["D1", "C1", "B1", "A1", "E0", "E1", "F0", "F1"];
assert.equal(originalSlots.length, 12);

function withEdits(edits) {
  const slots = originalSlots.slice();
  for (const [slot, move] of edits) {
    assert(!fixed.has(slot));
    slots[slot] = move;
  }
  return slots.map((x, i) => x + ([1, 3, 5, 7, 9].includes(i) ? "_" : "")).join("");
}
function parse(table) {
  const slots = table.replaceAll("_", "").match(/.{3}/g);
  assert(slots && slots.length === 12, "invalid 12-slot table " + table);
  for (const [idx, value] of fixed) assert.equal(slots[idx], value, "outside Raw34 " + table);
  return slotOrder.map(idx => {
    const move = slots[idx];
    assert(move === "---" || alphabet.includes(move), "invalid move " + move);
    return move === "---" ? null : move;
  });
}
function tableFromPrefix(prefix) {
  const slots = originalSlots.slice();
  for (let idx = 0; idx < prefix.length; idx++)
    slots[slotOrder[idx]] = prefix[idx] === "HALT" ? "1RZ" : prefix[idx];
  // The textual 1RZ is a display-only encoding of the unique HALT action;
  // symbolic slot prefix in JSON remains authoritative.
  return slots.map((x, i) => x + ([1, 3, 5, 7, 9].includes(i) ? "_" : "")).join("");
}
const certificates = [];
function add(family, table, source, label) {
  certificates.push({
    id: certificates.length,
    family, source, label,
    table, pattern: parse(table),
  });
}

for (const move of "0LA 0LB 0LC 0RA 0RB 0RC 0RD 1LC 1RA 1RB 1RC".split(" "))
  add("side-cycle-11", withEdits([[7, move]]),
      "Raw34ElevenSideCycles.lean", "D1=" + move);
depth2Data.second_level.forEach((entry, idx) =>
  add("side-cycle-74", entry.table, "Raw34Depth2SideCycles.lean", "index=" + idx));
add("unary-pump", "1RB---_1RC---_0RD1LC_1LC1RD_------_------",
    "Raw34UnaryGrowth.lean", "all-completions");

const cdMoves = [];
for (const write of "01")
  for (const direction of "LR")
    for (const next of "CD")
      cdMoves.push(write + direction + next);
for (const c1 of cdMoves)
  for (const d1 of cdMoves)
    add("closed-CD", withEdits([[5, c1], [7, d1]]),
        "Raw34ClosedComponent.lean", "C1=" + c1 + ",D1=" + d1);

depth3Data.witnesses.forEach((entry, idx) =>
  add("side-cycle-1206", entry.table, "Raw34Depth3All.lean", "index=" + idx));

const bcdMoves = [];
for (const write of "01")
  for (const direction of "LR")
    for (const next of "BCD")
      bcdMoves.push(write + direction + next);
for (const b1 of bcdMoves)
  for (const c1 of bcdMoves)
    for (const d1 of bcdMoves)
      add("closed-BCD", withEdits([[3, b1], [5, c1], [7, d1]]),
          "Raw34ClosedBCD.lean", "B1=" + b1 + ",C1=" + c1 + ",D1=" + d1);

add("triple-sweep-A", "1RB1LD_1RC---_0RD0RA_1LC1RD_------_------",
    "Raw34TripleSweepGrowth.lean", "A_never");
add("triple-sweep-E", "1RB---_1RC---_0RD0RE_1LC1RD_---1LD_------",
    "Raw34TripleSweepGrowth.lean", "E_never");
add("alternating-pump", "1RB---_1RC---_0RD0LD_1LC0RE_1RD---_------",
    "Raw34AlternatingGrowth.lean", "never");
assert.equal(certificates.length, 11+74+1+64+1206+1728+3);

const powers = Array.from({length: 9}, (_,i) => 25n**BigInt(i));
const nodes = [];
const memo = new Map();
const allIds = certificates.map(c => c.id);
const count = node => [BigInt(nodes[node].covered), BigInt(nodes[node].open)];

function makeLeaf(kind, at, witnessId) {
  const key = kind + ":" + at + ":" + (witnessId ?? "");
  if (memo.has(key)) return memo.get(key);
  const node = nodes.length;
  nodes.push({
    kind,
    remainingSlots: 8-at,
    ...(witnessId === undefined ? {} : {certificate: witnessId}),
    covered: kind === "covered" ? String(powers[8-at]) : "0",
    open: kind === "open" ? String(powers[8-at]) : "0",
  });
  memo.set(key, node);
  return node;
}
function solve(ids, at) {
  assert(at >= 0 && at <= 8);
  // A certificate with no remaining fixed slots covers the complete
  // current cube. Earlier slots were checked when the candidate survived.
  const winner = ids.find(id => certificates[id].pattern.slice(at).every(x => x === null));
  if (winner !== undefined) return makeLeaf("covered", at, winner);
  if (ids.length === 0) return makeLeaf("open", at);
  assert(at < 8, "nonempty pattern failed at terminal");
  const key = "split:" + at + ":" + ids.join(",");
  if (memo.has(key)) return memo.get(key);
  const free = [], byMove = new Map();
  for (const id of ids) {
    const move = certificates[id].pattern[at];
    if (move === null) free.push(id);
    else {
      if (!byMove.has(move)) byMove.set(move, []);
      byMove.get(move).push(id);
    }
  }
  const child = [];
  let covered = 0n, open = 0n;
  for (const action of alphabet) {
    const candidates = [...free, ...(byMove.get(action) ?? [])].sort((a,b) => a-b);
    const target = solve(candidates, at+1);
    const [c, o] = count(target);
    covered += c;
    open += o;
    child.push(target);
  }
  assert.equal(covered + open, powers[8-at], "partition conservation");
  const node = nodes.length;
  nodes.push({kind:"split",slot:slotNames[at],slotIndex:slotOrder[at],
              cases:child,covered:String(covered),open:String(open)});
  memo.set(key, node);
  return node;
}
const chosen = process.argv[2] ?? "1RD";
assert(chosen === "all" || alphabet.includes(chosen), "choose D1 action or all");
const startIds = chosen === "all" ? allIds :
  allIds.filter(i => certificates[i].pattern[0] === null ||
                        certificates[i].pattern[0] === chosen);
const root = chosen === "all" ? solve(startIds, 0) : solve(startIds, 1);
const [proved, remaining] = count(root);
assert.equal(proved + remaining, powers[chosen === "all" ? 8 : 7]);
if (chosen === "all") {
  assert.equal(proved, 97539062500n);
  assert.equal(remaining, 55048828125n);
}
if (chosen === "1RD") {
  assert.equal(proved, 3320312500n);
  assert.equal(remaining, 2783203125n);
}

// Unroll only OPEN paths to an explicit disjoint list of still-unknown
// partial cylinders. DAG nodes are shared, but each *path* is distinct.
const openCylinders = [];
const depthHistogram = {};
function listOpen(node, prefix) {
  const n = nodes[node];
  if (n.kind === "open") {
    assert.equal(prefix.length + n.remainingSlots, 8);
    depthHistogram[prefix.length] = (depthHistogram[prefix.length] ?? 0) + 1;
    openCylinders.push({
      prefix, // authoritative, including the explicit HALT action
      partialTableDisplay: tableFromPrefix(prefix),
      completeTables: String(powers[n.remainingSlots]),
    });
    return;
  }
  if (n.kind === "covered") return;
  for (let k = 0; k < alphabet.length; k++)
    listOpen(n.cases[k], [...prefix, alphabet[k]]);
}
listOpen(root, chosen === "all" ? [] : [chosen]);
const rebuilt = openCylinders.reduce((acc,x) => acc + BigInt(x.completeTables), 0n);
assert.equal(rebuilt, remaining, "explicit open-cylinder disjoint sum");

// A covered leaf is valid iff its certificate is compatible with the full
// prefix and imposes no constraints on the unfilled suffix. The constructor's
// candidate-filter invariant guarantees this at every recursion, but we
// recheck it independently against the fully built DAG.
let coveredPaths = 0;
function auditCovered(node, prefix) {
  const n = nodes[node];
  if (n.kind === "open") return;
  if (n.kind === "covered") {
    const p = certificates[n.certificate].pattern;
    assert(p.every((v,i) => v === null || (i < prefix.length && v === prefix[i])),
           "incorrect covered leaf containment");
    coveredPaths++;
    return;
  }
  for (let k = 0; k < alphabet.length; k++)
    auditCovered(n.cases[k], [...prefix,alphabet[k]]);
}
auditCovered(root, chosen === "all" ? [] : [chosen]);

const usedCertIds = new Set(nodes.filter(x=>x.kind==="covered").map(x=>x.certificate));
const payload = {
  status: "finite physical frontier, NOT a universal BB(6) Cover",
  parent: raw34, branchD1: chosen,
  slotOrder: slotNames, physicalActions: alphabet,
  totalCompleteTables: String(powers[chosen === "all" ? 8 : 7]),
  provablyNonhaltingFromAcceptedCylinderPatterns: String(proved),
  outsideTheseCertificates: String(remaining),
  uniqueDagNodes: nodes.length,
  coveredPaths, openCylinderCount: openCylinders.length, openDepthHistogram: depthHistogram,
  root, nodes, openCylinders,
  usedCertificates: certificates.filter(x=>usedCertIds.has(x.id)),
};
console.log(JSON.stringify(payload, null, 2));
