"use strict";

/**
 * Reconcile reported external Rocq confirmations with the pinned October 16
 * rooted holdout list. This script makes zero assertions about the validity
 * of reported proof files or the latest holdout roster.
 */
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { normalize } = require("../../tools/holdout_families.cjs");
const historical = fs.readFileSync(
  path.join(__dirname, "..", "..", "resources", "BB6_holdouts_663_2026-10-16.txt"), "utf8"
).trim().split(/\s+/u);
const report = JSON.parse(
  fs.readFileSync(path.join(__dirname, "2026-10-reported-halts.json"), "utf8")
);

assert.equal(historical.length, 663);
assert.equal(new Set(historical).size, 663);
const ranks = new Map(historical.map((code, index) => [code, index + 1]));
assert.equal(report.reported_halts.length, 5);

/** @param {string} code */
function rootedKey(code) {
  const normalized = normalize(code);
  return `${normalized.normalized}/initial=${normalized.start}`;
}

const halts = report.reported_halts.map((item) => {
  assert.equal(typeof item.rle, "string");
  assert.equal(item.steps === null || /^\d+$/u.test(item.steps), true);
  assert.equal(ranks.has(item.rle), true, `missing Oct16 root: ${item.rle}`);
  const normalized = normalize(item.rle);
  return {
    rle: item.rle,
    historical_line: ranks.get(item.rle),
    source_reported_date: item.reported_date,
    source_reported_verification: item.reported_verification,
    steps: item.steps,
    normalized_table: normalized.normalized,
    normalized_root: normalized.start,
    rooted_canonical_key: rootedKey(item.rle)
  };
});

assert.deepEqual(halts.map((h) => h.historical_line), [311, 584, 405, 368, 462]);
assert.equal(new Set(halts.map((h) => h.rooted_canonical_key)).size, 5);

// The last two reports share a raw transition table up to state relabeling
// and reflection, but their two initial states are inequivalent.
assert.equal(halts[3].normalized_table, halts[4].normalized_table);
assert.notEqual(halts[3].normalized_root, halts[4].normalized_root);
const alias = report.known_alias;
assert.equal(rootedKey(alias.rle), rootedKey(alias.root_equivalent_to));
assert.equal(rootedKey(alias.root_equivalent_to), halts[1].rooted_canonical_key);

process.stdout.write(JSON.stringify({
  archived_date: "2026-10-16",
  archived_size: historical.length,
  reported_roots: halts,
  distinct_reported_rooted_classes: 5,
  distinct_reported_unrooted_tables: new Set(halts.map((h) => h.normalized_table)).size,
  verified_alias: alias.rle,
  alias_of: alias.root_equivalent_to,
  note: report.provenance_note
}, null, 2) + "\n");
