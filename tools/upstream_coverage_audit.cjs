"use strict";

const fs = require("node:fs");

/**
 * Read the all-quoted CSV cells emitted by holdout_family_ledger.cjs.
 * @param {string} contents
 * @returns {string[][]}
 */
function readCsv(contents) {
  return contents.trim().split(/\r?\n/).map(line =>
    Array.from(line.matchAll(/"((?:[^"]|"")*)"/g), m =>
      m[1].replace(/""/g, '"')));
}

/**
 * Audit pinned Cryptids source coverage against historical rooted BB(6) families.
 * Input 1: im-results/agent24-upstream-census/upstream-coverage.csv
 * Input 2: im-results/holdout-family-coverage/2026-10-16-rooted-ledger.csv
 * Writes only a JSON report to stdout.
 * @param {string} sourceContents
 * @param {string} ledgerContents
 */
function audit(sourceContents, ledgerContents) {
  const upstream = readCsv(sourceContents).slice(1);
  const historical = readCsv(ledgerContents).slice(1);
  const roots = new Set(upstream.map(row => row[0]));
  const families = new Set(upstream.filter(row =>
    row[7] === "exact-rooted-match").map(row => row[5]));
  const related = historical.filter(row => families.has(row[3]));
  const indirect = related.filter(row => !roots.has(row[2])).map(row => ({
    rooted_rle: row[2],
    family_id: row[3],
    canonical_start: row[5],
    proof_status: "table-isomorphic only; independent blank start must be proved",
  }));
  return {
    snapshot_date: "2026-10-16",
    snapshot_rooted_count: historical.length,
    upstream_rooted_count: upstream.length,
    exact_rooted_matches: upstream.filter(row =>
      row[7] === "exact-rooted-match").length,
    source_matched_transition_table_families: families.size,
    historical_roots_on_source_matched_tables: related.length,
    additional_distinct_blank_starts_without_exact_root_source: indirect.length,
    indirect_reuse_candidates: indirect,
  };
}

if (require.main === module) {
  if (process.argv.length !== 4) {
    throw new Error("Expected upstream-coverage.csv and historic rooted-ledger.csv");
  }
  console.log(JSON.stringify(audit(
    fs.readFileSync(process.argv[2], "utf8"),
    fs.readFileSync(process.argv[3], "utf8")), null, 2));
}
module.exports = { audit, readCsv };
