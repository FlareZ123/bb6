"use strict";

/**
 * Audit the shape of the pinned 663-machine holdout snapshot.
 *
 * Usage: node tools/holdout_shape_audit.cjs resources/BB6_holdouts_663_2026-10-16.txt
 *
 * This reports only syntactic/support properties of that dated snapshot. It
 * does not prove that the file equals the current upstream queue's holdout_i.
 */
const fs = require("node:fs");
const { parse } = require("./holdout_families.cjs");

function main() {
  const args = process.argv.slice(2);
  if (args.length !== 1) throw new Error("Expected one RLE snapshot file");
  const machines = fs.readFileSync(args[0], "utf8").trim().split(/\s+/);
  const seen = new Set();
  const holeCounts = {};
  const freshCounts = {};
  const usedCounts = {};
  const nonPrefix = [];
  const twoHoleExamples = [];

  for (let i = 0; i < machines.length; i++) {
    const rle = machines[i];
    if (seen.has(rle)) throw new Error("Duplicate RLE at row " + (i + 1));
    seen.add(rle);
    const table = parse(rle);
    const used = new Set();
    let holes = 0;
    for (let q = 0; q < 6; q++) {
      for (const move of table[q]) {
        if (move === "---") {
          holes++;
        } else {
          used.add(q);
          used.add(move.charCodeAt(2) - 65);
        }
      }
    }
    let fresh = 0;
    while (fresh < 6 && used.has(fresh)) fresh++;
    const prefix = [...Array(fresh).keys()].every(q => used.has(q)) &&
      [...used].every(q => q >= 0 && q < fresh);
    holeCounts[holes] = (holeCounts[holes] || 0) + 1;
    freshCounts[fresh] = (freshCounts[fresh] || 0) + 1;
    usedCounts[used.size] = (usedCounts[used.size] || 0) + 1;
    if (!prefix) nonPrefix.push({ row: i + 1, rle, used: [...used].sort((a,b)=>a-b), fresh });
    if (holes === 2) twoHoleExamples.push({ row: i + 1, rle });
  }

  console.log(JSON.stringify({
    snapshotRows: machines.length,
    uniqueRows: seen.size,
    holeCounts,
    freshCounts,
    usedStateCounts: usedCounts,
    nonPrefixCount: nonPrefix.length,
    nonPrefix,
    twoHoleExamples,
  }, null, 2));
}

if (require.main === module) main();
