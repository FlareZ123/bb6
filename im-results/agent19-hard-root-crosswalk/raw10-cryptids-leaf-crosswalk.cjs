#!/usr/bin/env node
"use strict";

// Reproduce the source-pinned raw10 last-hole crosswalk.
// Run from the repository root:
//   node im-results/agent19-hard-root-crosswalk/raw10-cryptids-leaf-crosswalk.cjs /path/to/cryptids
//
// The script is finite computational evidence. The Lean adapter in
// Raw10CryptidsLeaf.lean is intended to certify the source theorem, exact
// first-hole path, weighted leaf, and residual-box integration.

const fs = require("node:fs");
const path = require("node:path");
const { execFileSync } = require("node:child_process");

const PINNED = "3647718b5df22e1a61462dec0376bd204526285a";
const MODULE = "M_1RB0LC_1LC0RE_1LA1LD_1LA1LB_0RF1RA_HHH0RE.lean";
const UPSTREAM = path.resolve(process.argv[2] || "/tmp/cryptids");
const NONHALT = path.join(UPSTREAM, "BusyBeaver/BB6/NonHalt", MODULE);

const readRepo = p => fs.readFileSync(p, "utf8");
const readUpstream = p => fs.readFileSync(path.join(UPSTREAM, p), "utf8");

function moveCode(write, right, next) {
  return 1 + 4 * Number(next) + 2 * (write === "true" ? 1 : 0)
    + (right === "true" ? 1 : 0);
}

function parseEncodedRows(source) {
  const match = source.match(/def rows : List \(List Nat\) := \[([\s\S]*?)\]\ndef slots/);
  if (!match) throw new Error("Could not find Raw10Encoded.rows");
  const rows = [...match[1].matchAll(/\[([0-9,\s]+)\]/g)]
    .map(x => x[1].split(",").map(v => Number(v.trim())));
  if (rows.length !== 66 || rows.some(r => r.length !== 12))
    throw new Error("Expected 66 twelve-slot Raw10Encoded rows");
  return rows;
}

function parsePartialCube(source, name) {
  const start = source.indexOf("def " + name + " : PartialMachine :=");
  const end = source.indexOf("\n\ndef witness", start);
  if (start < 0 || end < 0) throw new Error("Missing PartialMachine " + name);
  const body = source.slice(start, end);
  const pairs = [];
  for (const x of body.matchAll(/s = \((\d+),(false|true)\) then some \(some ⟨(true|false),(true|false),(\d+)⟩\)/g))
    pairs.push([2 * Number(x[1]) + (x[2] === "true" ? 1 : 0),
      moveCode(x[3], x[4], x[5])]);
  for (const x of body.matchAll(/s = \((\d+),(false|true)\) then some none/g))
    pairs.push([2 * Number(x[1]) + (x[2] === "true" ? 1 : 0), 0]);
  pairs.sort((a,b) => a[0] - b[0]);
  if (!pairs.length) throw new Error("No assignments parsed for " + name);
  return pairs;
}

function subtract(box, cube) {
  if (cube.some(([s,v]) => !box[s].includes(v))) return [box];
  const pieces = [];
  let accepted = box.map(domain => domain.slice());
  for (const [s,v] of cube) {
    const rejected = accepted.map(domain => domain.slice());
    rejected[s] = rejected[s].filter(x => x !== v);
    if (rejected.every(domain => domain.length > 0)) pieces.push(rejected);
    accepted = accepted.map(domain => domain.slice());
    accepted[s] = [v];
  }
  return pieces;
}

function mass(boxes) {
  return boxes.reduce((sum, box) =>
    sum + box.reduce((product, domain) => product * domain.length, 1), 0);
}

function permutations(s) {
  return s.length
    ? [...s].flatMap((c,i) => permutations(s.slice(0,i) + s.slice(i+1)).map(t => c+t))
    : [""];
}

const letters = "ABCDEF";

function rename(tokens, permutation) {
  const out = Array(12);
  for (let q = 0; q < 6; q++) for (let b = 0; b < 2; b++) {
    const move = tokens[2*q+b];
    out[2*letters.indexOf(permutation[q])+b] =
      move === "HHH" ? "HHH" : move.slice(0,2) + permutation[letters.indexOf(move[2])];
  }
  return out;
}

function encode(tokens) {
  return tokens.map(move => move === "HHH" ? 0
    : moveCode(move[0] === "1" ? "true" : "false",
      move[1] === "R" ? "true" : "false", letters.indexOf(move[2])));
}

function rle(table) {
  return Array.from({length:6}, (_,q) => table.slice(2*q,2*q+2).map(v => {
    if (v === 0) return "---";
    const z = v - 1;
    const next = Math.floor(z / 4);
    const write = Math.floor((z % 4) / 2);
    const right = z % 2;
    return (write ? "1" : "0") + (right ? "R" : "L") + letters[next];
  }).join("")).join("_");
}

function simulateFirstUse(tokens, limit = 50000000) {
  const tape = new Set();
  const visited = new Map();
  const trace = [];
  let state = 0, head = 0, steps = 0, halted = false;
  while (visited.size < 11 && steps < limit) {
    const bit = tape.has(head) ? 1 : 0;
    const slot = 2*state + bit;
    const move = tokens[slot];
    if (move === "HHH") { halted = true; break; }
    if (!visited.has(slot)) {
      visited.set(slot, steps);
      trace.push({time:steps, slot:letters[state]+bit, move});
    }
    if (move[0] === "1") tape.add(head); else tape.delete(head);
    head += move[1] === "R" ? 1 : -1;
    state = letters.indexOf(move[2]);
    steps++;
  }
  const holes = tokens.map((m,s) => m === "HHH" ? s : -1).filter(s => s >= 0);
  return {halted, steps, visitedOrdinary:visited.size, trace,
    unvisitedHaltSlot: holes.length === 1
      ? letters[Math.floor(holes[0]/2)] + (holes[0]%2) : null};
}

const local = p => readRepo(path.resolve(p));
const rows = parseEncodedRows(local("im-results/agent49-box-complement/Raw10Encoded.lean"));
const cycle = parsePartialCube(local("im-results/agent50-weighted-tnf-pilot/Raw10Box8Cycle.lean"), "table");
const halt = parsePartialCube(local("im-results/agent50-weighted-tnf-pilot/Raw10Box0Halt.lean"), "haltTable");
const certificates = [
  ...rows.map(row => row.flatMap((v,s) => v === 0 ? [] : [[s,v]])),
  cycle, halt
];
const parent = Array.from({length:12}, (_,s) =>
  s === 0 ? [8] : s === 2 ? [11] : Array.from({length:25}, (_,i) => i));
let boxes = [parent];
for (const certificate of certificates)
  boxes = boxes.flatMap(box => subtract(box, certificate));
const baseMass = mass(boxes);
if (boxes.length !== 41 || baseMass !== 90737503713725)
  throw new Error("The current 68-certificate raw10 partition did not reproduce");

const sourceCommit = execFileSync("git", ["-C", UPSTREAM, "rev-parse", "HEAD"], {encoding:"utf8"}).trim();
if (sourceCommit !== PINNED) throw new Error("Upstream source is not at the pinned commit");
const sourceText = fs.readFileSync(NONHALT, "utf8");
if (!/theorem is_not_halt\s*:\s*IsNotHalt target/.test(sourceText))
  throw new Error("Pinned source module does not expose is_not_halt");

const raw = MODULE.replace(/^M_/, "").replace(/\.lean$/, "");
const segments = raw.split("_");
if (segments.length !== 6 || segments.some(x => x.length !== 6))
  throw new Error("Candidate filename is not a six-row RLE");
const tokens = segments.flatMap(x => [x.slice(0,3), x.slice(3,6)]);
if (tokens[0] !== "1RB" || tokens.filter(x => x === "HHH").length !== 1)
  throw new Error("Candidate is not a 1RB-rooted one-halt table");

const holdouts = new Set(local("resources/BB6_holdouts_663_2026-10-16.txt")
  .split(/\r?\n/).map(x => x.trim().replaceAll("_","")).filter(Boolean));
const accepted608 = [
  "1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF",
  "1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA",
  "1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA",
  "1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---",
  "1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_---0LD",
  "1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF"
].map(x => x.replaceAll("_",""));

const compatible = [];
for (const tail of permutations("CDEF")) {
  const permutation = "AB" + tail;
  const table = encode(rename(tokens, permutation));
  if (table[0] !== 8 || table[2] !== 11) continue;
  const leafBoxes = boxes.map((box,i) => {
    const hole = table.indexOf(0);
    return table.every((v,s) => s === hole
      ? box[s].length === 25 : box[s].includes(v)) ? i : -1;
  }).filter(i => i >= 0);
  compatible.push({permutation, rle:rle(table), leafBoxes});
}
if (compatible.length !== 6) throw new Error("Expected six A/B-fixing aliases of the raw10 parent");
if (compatible.some(x => x.leafBoxes.length !== 1 || x.leafBoxes[0] !== 0))
  throw new Error("Not every raw10 alias has its full leaf in residual box 0");
if (compatible.some(x => holdouts.has(x.rle.replaceAll("_",""))))
  throw new Error("Candidate unexpectedly overlaps the historical 663 list");
if (compatible.some(x => accepted608.includes(x.rle.replaceAll("_",""))))
  throw new Error("Candidate duplicates an already accepted six-root graft");

const table = encode(tokens);
const hole = table.indexOf(0);
const leafCube = table.flatMap((v,s) => v === 0 ? [] : [[s,v]]);
const containing = boxes.map((box,i) =>
  table.every((v,s) => s === hole ? box[s].length === 25 : box[s].includes(v)) ? i : -1
).filter(i => i >= 0);
if (containing.length !== 1 || containing[0] !== 0)
  throw new Error("Identity-renamed leaf is not uniquely contained in residual box 0");

const after = boxes.flatMap(box => subtract(box, leafCube));
if (after.length !== 49 || mass(after) !== 90737503713700)
  throw new Error("Post-leaf residual count/mass mismatch");
if (baseMass - mass(after) !== 25) throw new Error("The leaf did not remove exactly 25 completions");

const simulation = simulateFirstUse(tokens);
if (simulation.halted || simulation.visitedOrdinary !== 11 ||
    simulation.unvisitedHaltSlot !== "F0" || simulation.steps !== 21)
  throw new Error("The blank-start first-hole trace did not reach the expected last hole");
const expectedTrace = [
  "A0@0","B0@1","C1@2","D0@3","B1@5",
  "E1@6","A1@7","C0@11","E0@14","F1@15","D1@20"
];
const actualTrace = simulation.trace.map(x => x.slot+"@"+x.time);
if (JSON.stringify(actualTrace) !== JSON.stringify(expectedTrace))
  throw new Error("First-use trace changed: " + actualTrace.join(","));

console.log(JSON.stringify({
  upstreamCommit:sourceCommit,
  sourceModule:MODULE,
  sourceTheorem:"is_not_halt : IsNotHalt target",
  candidateRLE:rle(table),
  haltSlot:"F0",
  raw10ParentAliases:compatible.length,
  allAliasesOutside663:true,
  allAliasesOutside608:true,
  allAliasesAlreadyIntegrated:false,
  preLeaf:{boxes:boxes.length,mass:baseMass},
  containingResidualBox:0,
  leafCompletions:25,
  firstUseTrace:simulation.trace,
  postLeaf:{boxes:after.length,mass:mass(after)},
  massRemoved:25
}, null, 2));
