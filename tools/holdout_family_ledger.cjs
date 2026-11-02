"use strict";

/**
 * Reproduce the conservative rooted-machine ledger from the pinned snapshot.
 * Run with Node.js CommonJS. No filesystem writes: output is CSV on stdout.
 * The classification uses the same canonicalization as holdout_families.cjs.
 */
const fs = require("node:fs");
const { normalize } = require("./holdout_families.cjs");

const SOURCE_STATUS = new Map([
  ["1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE", [
    "raw-to-map halting iff certified; P1 global halt unresolved",
    "im-results/agent19-p1-source-bridge/P1HaltingBridge.lean", "41388451571"]],
  ["1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE", [
    "raw-to-map halting iff certified; B global halt unresolved",
    "im-results/agent18-b-cycle/BReduction.lean", "41388514940"]],
  ["1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC", [
    "raw-to-map halting iff certified; C global halt unresolved",
    "im-results/agent21-c-source-bridge/CSourceBridge.lean", "41389979481"]],
  ["1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE", [
    "raw-to-section halting iff certified; Sheep global halt unresolved",
    "im-results/agent22-sheep-infinite-inverse/GeneralAncestry.lean", "41390686337"]],
  ["1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---", [
    "raw blank-origin finite prefix certified; D0 global halt unresolved",
    "im-results/agent35-cryptid-code/BlankFurther.lean", "41421823798"]],
  ["1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA", [
    "full raw table and exact-time conjugacy to D0 from F; root halt open",
    "im-results/agent3-portfolio-raw-conjugacy/DTableWitness.lean", "41457732702"]],
  ["1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---", [
    "full raw table and exact-time conjugacy to D0 from C; root halt open",
    "im-results/agent3-portfolio-raw-conjugacy/DTableWitness.lean", "41457732702"]],
  ["1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---", [
    "full raw table and exact-time conjugacy to D0 from B; root halt open",
    "im-results/agent3-portfolio-raw-conjugacy/DTableWitness.lean", "41457732702"]],
]);

// Curated external classifications are separate from locally checked results.
// Pin upstream repository commits and preserve the difference between a published
// Lean theorem and a local independent reconstruction of its dependency closure.
const EXTERNAL_HALTING = new Map([
  ["1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---", [
    "nonhalting (upstream Lean proof; no independent local rebuild)",
    "Cryptids theorem is_not_halt; google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b; artifacts/a6/Audit.lean"
  ]],
]);

const FIELDS = [
  "catalogue_asof", "curation_asof", "rooted_rle", "family_id",
  "canonical_unrooted_table", "canonical_start_for_root",
  "mirror_original_to_canonical", "canonical_state_order_original_letters",
  "family_member_count", "local_proof_status", "local_source_path",
  "local_ci_run_id", "global_rooted_halting_status", "external_status",
];

/** @param {string|number} value @returns {string} */
function quote(value) {
  return '"' + String(value).replace(/"/g, '""') + '"';
}

/** @param {string} snapshot @returns {string} */
function buildLedger(snapshot) {
  const machines = snapshot.trim().split(/\s+/);
  if (machines.length !== 663 || new Set(machines).size !== 663) {
    throw new Error("The pinned snapshot must contain 663 unique machine strings");
  }
  const entries = machines.map(normalize);
  const grouped = new Map();
  for (const item of entries) {
    if (!grouped.has(item.normalized)) grouped.set(item.normalized, []);
    grouped.get(item.normalized).push(item);
  }
  const multi = [...grouped.values()].filter(items => items.length > 1);
  if (grouped.size !== 435 || multi.length !== 145) {
    throw new Error("Unexpected canonical unrooted-family census");
  }

  const tables = [...grouped.keys()].sort();
  const ids = new Map(tables.map((table, i) =>
    [table, "F" + String(i + 1).padStart(3, "0")]));
  const csv = [FIELDS.map(quote).join(",")];
  for (const e of entries) {
    const [status, source, ci] = SOURCE_STATUS.get(e.machine) ||
      ["not curated in this ledger; investigate before treating as open or solved", "", ""];
    const row = [
      "2026-10-16", "2026-11-02", e.machine, ids.get(e.normalized),
      e.normalized, String.fromCharCode(65 + e.start), e.reflect ? "yes" : "no",
      e.order.map(i => String.fromCharCode(65 + i)).join(""),
      grouped.get(e.normalized).length, status, source, ci,
      ...(EXTERNAL_HALTING.get(e.machine) || ["not established by this ledger", "not checked"]),
    ];
    csv.push(row.map(quote).join(","));
  }
  return csv.join("\n") + "\n";
}

if (require.main === module) {
  if (process.argv.length !== 3) {
    throw new Error("Expected one pinned catalogue filename");
  }
  process.stdout.write(buildLedger(fs.readFileSync(process.argv[2], "utf8")));
}

module.exports = { buildLedger };
