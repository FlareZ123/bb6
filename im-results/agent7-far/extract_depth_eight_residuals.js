#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const base = path.resolve(__dirname, "../agent50-weighted-tnf-pilot");
const root = JSON.parse(fs.readFileSync(path.join(base, "root-frontier.json"), "utf8"));
const files = [1, 2, 3, 4].map(i =>
  fs.readFileSync(path.join(base, "DepthEightSiblingData" + i + ".lean"), "utf8"));

function parseTreeExpr(src, start) {
  let i = start;
  function skip() {
    while (i < src.length) {
      if (/\s/.test(src[i])) { i++; continue; }
      if (src.startsWith("--", i)) { while (i < src.length && src[i] !== "\n") i++; continue; }
      if (src.startsWith("/-", i)) {
        i += 2; let depth = 1;
        while (i < src.length && depth) {
          if (src.startsWith("/-", i)) { depth++; i += 2; }
          else if (src.startsWith("-/", i)) { depth--; i += 2; }
          else i++;
        }
        continue;
      }
      break;
    }
  }
  function eat(s) {
    skip();
    if (!src.startsWith(s, i)) throw new Error("Expected " + s + " at " + i);
    i += s.length;
  }
  function token() {
    skip();
    const m = src.slice(i).match(/^-?\d+|^[A-Za-z_][A-Za-z0-9_']*/);
    if (!m) throw new Error("Expected token at " + i);
    i += m[0].length;
    return m[0];
  }
  const num = () => Number(token());
  function bool() {
    const x = token();
    if (x === "true") return true;
    if (x === "false") return false;
    throw new Error("Unexpected Bool " + x);
  }
  function slot() {
    eat("("); const q = num(); eat(","); const b = bool(); eat(")");
    return [q, b];
  }
  function parenInt() { eat("("); const n = num(); eat(")"); return n; }
  function list() {
    eat("["); const out = []; skip();
    if (src[i] === "]") { i++; return out; }
    while (true) {
      out.push(tree()); skip();
      if (src[i] === ",") { i++; continue; }
      if (src[i] === "]") { i++; return out; }
      throw new Error("Expected list separator at " + i);
    }
  }
  function tree() {
    skip();
    if (src.startsWith("branchList", i)) {
      eat("branchList");
      return { kind: "branch", n: num(), slot: slot(), children: list() };
    }
    if (src.startsWith(".side", i)) {
      eat(".side");
      return { kind: "side", n: num(), k: num(), right: bool(), boundary: parenInt() };
    }
    if (src.startsWith(".last", i)) {
      eat(".last");
      return { kind: "last", n: num(), slot: slot() };
    }
    if (src.startsWith(".openLeaf", i)) { eat(".openLeaf"); return { kind: "open" }; }
    throw new Error("Unknown Tree expression at " + i + ": " + src.slice(i, i + 60));
  }
  return tree();
}

const moves = [];
for (let q = 0; q < 6; q++)
  for (const write of [false, true])
    for (const right of [false, true])
      moves.push({ next: q, write, right });
const moveIndex = m => m.next * 4 + (m.write ? 2 : 0) + (m.right ? 1 : 0);
const moveCode = m => (m.write ? "1" : "0") + (m.right ? "R" : "L") + String.fromCharCode(65 + m.next);
const slotCode = s => String.fromCharCode(65 + s[0]) + "/" + (s[1] ? "1" : "0");

function decodeMove(c) {
  if (c === null || c === "---") return null;
  if (c === "HHH") return { halt: true };
  return { write: c[0] === "1", right: c[1] === "R", next: c.charCodeAt(2) - 65 };
}
function encodeTable(p) {
  return Array.from({ length: 6 }, (_, q) =>
    [0, 1].map(b => {
      const x = p[2 * q + b];
      if (x === null) return "---";
      if (x.halt) return "HHH";
      return (x.write ? "1" : "0") + (x.right ? "R" : "L") + String.fromCharCode(65 + x.next);
    }).join("")
  ).join("_");
}
function residuals(p, t, pathSoFar = []) {
  if (t.kind === "open") return [{ table: p, path: pathSoFar }];
  if (t.kind === "side" || t.kind === "last") return [];
  const out = [];
  const slotIndex = 2 * t.slot[0] + (t.slot[1] ? 1 : 0);
  for (const move of moves) {
    const child = t.children[moveIndex(move)] || { kind: "open" };
    const next = p.slice();
    next[slotIndex] = move;
    out.push(...residuals(next, child, pathSoFar.concat([{
      slot: slotCode(t.slot), move: moveCode(move)
    }])));
  }
  return out;
}

const all = [];
for (const src of files) {
  const mappings = [...src.matchAll(/⟨\s*tableAt\s+(\d+)\s*,\s*tree(\d+)\s*,\s*tree\d+_checked\s*⟩/g)];
  const trees = new Map();
  for (const m of src.matchAll(/def\s+tree(\d+)\s*:\s*Tree\s*:=/g))
    trees.set(Number(m[1]), parseTreeExpr(src, m.index + m[0].length));
  for (const m of mappings) {
    const parentIndex = Number(m[1]), treeId = Number(m[2]);
    const parent = root.residuals[parentIndex];
    if (!parent) throw new Error("Missing root residual index " + parentIndex);
    const p = parent.rows.flat().map(decodeMove);
    const t = trees.get(treeId);
    if (!t) throw new Error("Missing tree" + treeId);
    for (const r of residuals(p, t))
      all.push({ parentIndex, treeId, holes: r.table.filter(x => x === null).length,
        table: encodeTable(r.table), path: r.path });
  }
}
const unique = [...new Map(all.map(x => [x.table, x])).values()];
const oneHole = unique.filter(x => x.holes === 1);
const twoHole = unique.filter(x => x.holes === 2);
if (all.length !== 107 || unique.length !== 107 || oneHole.length !== 101 || twoHole.length !== 6)
  throw new Error("Residual count mismatch: occurrences=" + all.length +
    " unique=" + unique.length + " one-hole=" + oneHole.length + " two-hole=" + twoHole.length);
const expected = [
  "1RB0LB_1RC1LF_0RD1RA_1LD1RE_---0LB_---0LA",
  "1RB1LD_1RC1LF_0RD1RA_1LD1RE_---0LB_---0LA",
  "1RB1LC_1RC1LF_0RD1RB_1LD1RE_---0LB_---0LA",
  "1RB1RD_1RC1LF_0RD1RB_1LD1RE_---0LB_---0LA",
  "1RB1LE_1RC1LF_0RD1RB_1LD1RE_---0LB_---0LA",
  "1RB1LF_1RC1LF_0RD1RB_1LD1RE_---0LB_---0LA"
].sort();
if (twoHole.map(x => x.table).sort().join("\n") !== expected.join("\n"))
  throw new Error("The six two-hole tables differ from the recorded roster.");
function simulateBlankRun(table, cap) {
  const codes = table.replace(/_/g, "").match(/.{3}/g);
  const machine = codes.map(decodeMove);
  const tape = new Map();
  let state = 0, symbol = 0, head = 0, maxHead = 0;
  for (let step = 0; step < cap; step++) {
    const tr = machine[2 * state + symbol];
    if (tr === null)
      return { kind: "hole", steps: step,
        slot: String.fromCharCode(65 + state) + "/" + symbol,
        maxHead, tapeCells: tape.size };
    if (tr.halt) return { kind: "halt", steps: step, maxHead, tapeCells: tape.size };
    if (tr.write) tape.set(head, 1); else tape.delete(head);
    head += tr.right ? 1 : -1;
    maxHead = Math.max(maxHead, Math.abs(head));
    state = tr.next;
    symbol = tape.get(head) || 0;
  }
  return { kind: "cap", steps: cap, maxHead, tapeCells: tape.size };
}

const output = {
  residualOccurrences: all.length, uniqueResiduals: unique.length,
  oneHole: oneHole.length, twoHole: twoHole.length,
  twoHoleTables: twoHole.map(({ parentIndex, treeId, table, path }) =>
    ({ parentIndex, treeId, table, path }))
};
if (process.argv.includes("--one-hole"))
  output.oneHoleTables = oneHole.map(({ parentIndex, treeId, table, path }) =>
    ({ parentIndex, treeId, table, path }));
const simArg = process.argv.find(x => x.startsWith("--simulate-steps="));
if (simArg) {
  const cap = Number(simArg.split("=")[1]);
  if (!Number.isSafeInteger(cap) || cap < 1) throw new Error("Invalid simulation step cap");
  const runs = oneHole.map(x => ({ parentIndex: x.parentIndex, treeId: x.treeId,
    table: x.table, ...simulateBlankRun(x.table, cap) }));
  output.simulation = {
    cap, capped: runs.filter(x => x.kind === "cap").length,
    holeReached: runs.filter(x => x.kind === "hole").length,
    halted: runs.filter(x => x.kind === "halt").length,
    maxHead: Math.max(...runs.map(x => x.maxHead)),
    maxTapeCells: Math.max(...runs.map(x => x.tapeCells))
  };
  if (process.argv.includes("--one-hole")) output.oneHoleSimulation = runs;
}
console.log(JSON.stringify(output, null, 2));
