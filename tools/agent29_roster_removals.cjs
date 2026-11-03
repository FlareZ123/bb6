"use strict";

/**
 * Source-rooted exact table-family audit for six unexplained October 2026
 * BB(6) inventory deletions. Run at repository root:
 * node tools/agent29_roster_removals.cjs
 */
const fs = require("node:fs");
const path = require("node:path");
const { normalize, parse } = require("./holdout_families.cjs");

const root = path.resolve(__dirname, "..");
/** @param {string} file */
const read = file => fs.readFileSync(path.join(root, file), "utf8");
/** @param {string} text */
function readRemoved(text) {
  return text.split(/\r?\n/).filter(line => /^\d+\t/.test(line)).map(line => {
    const [row, code] = line.split("\t");
    parse(code);
    return { row: Number(row), code };
  });
}
const original = read("resources/BB6_holdouts_663_2026-10-16.txt").trim().split(/\s+/);
const removed623 = readRemoved(read("im-results/agent4-dated-roster/removed-663-to-623.tsv"));
const removed608 = readRemoved(read("im-results/agent4-dated-roster/removed-623-to-608.tsv"));
if (original.length !== 663 || removed623.length !== 40 || removed608.length !== 15)
  throw new Error("Pinned inventory count mismatch");
const early = new Set(removed623.map(x => x.code));
const late = new Set(removed608.map(x => x.code));
const families = new Map();
for (const [i, code] of original.entries()) {
  const x = normalize(code);
  const members = families.get(x.normalized) || [];
  members.push({ oct16Line: i + 1, code, canonicalStart: x.start,
    status: early.has(code) ? "deleted-16-to-24" :
      late.has(code) ? "deleted-24-to-30" : "retained-30" });
  families.set(x.normalized, members);
}

/**
 * @param {string} code
 * @param {string[]} names Permutation mapping old states onto new states
 * @param {boolean} mirror
 */
function transform(code, names, mirror) {
  const old = parse(code);
  const output = Array(6);
  for (let i = 0; i < 6; ++i) {
    output[names[i].charCodeAt(0) - 65] = old[i].map(t => t === "---" ? t :
      t[0] + (mirror ? (t[1] === "L" ? "R" : "L") : t[1]) +
      names[t.charCodeAt(2) - 65]).join("");
  }
  return output.join("_");
}
const r146 = removed608.find(x => x.row === 146);
const r411 = removed608.find(x => x.row === 411);
const stateMap = ["B", "C", "D", "A", "E", "F"];
if (transform(r146.code, stateMap, true) !== r411.code)
  throw new Error("Row 146 -> 411 mirrored state relabeling failed");
if (transform(r146.code, stateMap, false) === r411.code)
  throw new Error("Row 146 -> 411 unexpectedly needs no reflection");

const targets = [109, 119, 146, 247, 411, 531].map(row => {
  const target = removed608.find(x => x.row === row);
  if (!target) throw new Error(`Missing deleted row ${row}`);
  const normalized = normalize(target.code);
  return { oct24Row: row, oct16Line: original.indexOf(target.code) + 1,
    code: target.code, canonicalStart: normalized.start,
    sameUnrootedTable: families.get(normalized.normalized) };
});
const deletionGroups = new Map();
for (const x of removed608) {
  const k = normalize(x.code).normalized;
  deletionGroups.set(k, [...(deletionGroups.get(k) || []), x.row]);
}
if (deletionGroups.size !== 10) throw new Error("Expected 10 table families in 15 removals");
if (!targets.find(x => x.oct24Row === 119).sameUnrootedTable
  .some(x => x.status === "retained-30"))
  throw new Error("Row 119 must share a table with a retained rooted sibling");
console.log(JSON.stringify({
  rosterOriginal: original.length,
  deletionCount: removed608.length,
  deletedUnrootedGroups: [...deletionGroups.values()].sort((a, b) => a[0] - b[0]),
  row146To411: { mirror: true, stateMap: { A: "B", B: "C", C: "D",
    D: "A", E: "E", F: "F" }, newBlankARepresentsOriginalBlankD: true },
  targets,
}, null, 2));
