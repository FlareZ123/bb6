"use strict";

/**
 * Pin-sensitive, read-only historical holdout/hardness crosswalk.
 * Both input files are checked into the BB(6) repository. No network or downloads.
 * The DeepMind source is pinned by commit and blob SHA in the input header.
 */
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");

const root = path.resolve(__dirname, "..", "..");
const sourcePath = path.join(root, "resources", "BB6_holdouts_663_2026-10-16.txt");
const corpusPath = path.join(__dirname, "hardness-codes-20261024.txt");
const rle = /^(?:[01][LR][A-F]|---){2}(?:_(?:[01][LR][A-F]|---){2}){5}$/;

/** @param {string} filePath @returns {string[]} */
function readCodes(filePath) {
  const rows = fs.readFileSync(filePath, "utf8")
    .split(/\r?\n/u)
    .map((line) => line.trim())
    .filter((line) => line.length > 0 && !line.startsWith("#"));
  for (const line of rows) assert.match(line, rle, `invalid RLE in ${filePath}: ${line}`);
  assert.equal(new Set(rows).size, rows.length, `duplicate RLE in ${filePath}`);
  return rows;
}

const historical = readCodes(sourcePath);
const hardness = readCodes(corpusPath);
assert.equal(historical.length, 663);
assert.equal(hardness.length, 36);
const index = new Map(historical.map((code, i) => [code, i + 1]));
const present = hardness.filter((code) => index.has(code)).map((code) => ({
  code,
  line_20261016: index.get(code)
}));
const absent = hardness.filter((code) => !index.has(code));
assert.equal(present.length, 35);
assert.deepEqual(absent, ["1RB1LA_0RC1RD_1LC0LA_1LE1RE_0RB0LF_---0LD"]);
process.stdout.write(JSON.stringify({
  archived_snapshot: "2026-10-16",
  archived_count: historical.length,
  source: "google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/Hardness.lean",
  source_distinct_machine_literals: hardness.length,
  exact_matches: present,
  absent
}, null, 2) + "\n");
