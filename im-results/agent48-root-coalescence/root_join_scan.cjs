"use strict";

/**
 * Agent48 R008 finite blank-root coalescence screen.
 * Input: the exact pinned Agent18 663-root ledger with 14 quoted CSV columns.
 * Two configurations are equivalent when state and all marked tape cells
 * relative to the head coincide; finite head translation preserves future
 * ordinary Turing steps. Every candidate is checked with exact integer tape.
 * A bounded non-match is never an all-time negative mathematical theorem.
 */
const fs = require("node:fs");
const path = require("node:path");

/** @typedef {{row: number, rooted_rle: string, family_id: string, canonical_unrooted_table: string, canonical_start_for_root: string}} Root */

/**
 * The pinned CSV is uniformly quoted, with 14 fields and no escaped field
 * delimiters; assert that invariant so malformed input cannot corrupt roots.
 * @param {string} input
 * @returns {Root[]}
 */
function readLedger(input) {
  const lines = input.trim().split(/\r?\n/u);
  const keys = lines.shift().slice(1, -1).split('","');
  if (keys.length !== 14) throw new Error("Unexpected ledger schema");
  return lines.map((line, i) => {
    if (!line.startsWith('"') || !line.endsWith('"')) {
      throw new Error("Malformed quoted CSV row " + (i + 1));
    }
    const values = line.slice(1, -1).split('","');
    if (values.length !== keys.length) {
      throw new Error("Unexpected number of CSV columns at row " + (i + 1));
    }
    return {row: i + 1, ...Object.fromEntries(keys.map((k, j) => [k, values[j]]))};
  });
}

/** @param {string} rle @returns {string[][]} */
function parseTable(rle) {
  if (!/^(?:[01][LR][A-F]|---){2}(?:_(?:[01][LR][A-F]|---){2}){5}$/u.test(rle)) {
    throw new Error("Invalid canonical table " + rle);
  }
  return rle.split("_").map(x => [x.slice(0, 3), x.slice(3)]);
}

/**
 * @param {Root[]} roots
 * @param {number} cutoff Number of sampled raw configurations: n=0..cutoff-1.
 */
function scan(roots, cutoff = 800) {
  /** @type {Map<string, Root[]>} */
  const grouped = new Map();
  for (const root of roots) {
    const group = grouped.get(root.canonical_unrooted_table) || [];
    group.push(root);
    grouped.set(root.canonical_unrooted_table, group);
  }
  const multi = [...grouped.values()].filter(g => g.length > 1);
  /** @type {{family:string,row1:number,row2:number,n1:number,n2:number,shift:number,rle1:string,rle2:string}[]} */
  const mergers = [];
  /** @type {{family:string,row:number,step:number,rle:string}[]} */
  const halts = [];
  let sampled = 0;
  for (const group of multi) {
    const table = parseTable(group[0].canonical_unrooted_table);
    /** @type {Map<string, {root:Root,n:number,head:number}[]>} */
    const seen = new Map();
    const acceptedPairs = new Set();
    for (const root of group) {
      let q = root.canonical_start_for_root.charCodeAt(0) - 65;
      let head = 0;
      const ones = new Set();
      for (let n = 0; n < cutoff; n++) {
        sampled++;
        // Translation-free canonicalization, preserving *every* one-cell.
        const shifted = [...ones].map(x => x - head).sort((a,b) => a - b);
        const key = q + ";" + shifted.join(",");
        const witnesses = seen.get(key) || [];
        for (const old of witnesses) {
          if (old.root.row === root.row) continue;
          const keyPair = [old.root.row,root.row].sort((a,b) => a-b).join(",");
          if (acceptedPairs.has(keyPair)) continue;
          acceptedPairs.add(keyPair);
          mergers.push({
            family: root.family_id, row1: old.root.row, row2: root.row,
            n1: old.n, n2: n, shift: head - old.head,
            rle1: old.root.rooted_rle, rle2: root.rooted_rle
          });
        }
        if (!witnesses.some(w => w.root.row === root.row)) {
          witnesses.push({root,n,head});
          seen.set(key,witnesses);
        }
        const a = table[q][ones.has(head) ? 1 : 0];
        if (a === "---") {
          halts.push({family: root.family_id,row:root.row,step:n,rle:root.rooted_rle});
          break;
        }
        if (a[0] === "1") ones.add(head);
        else ones.delete(head);
        head += a[1] === "R" ? 1 : -1;
        q = a.charCodeAt(2) - 65;
      }
    }
  }
  return {
    source_rows: roots.length,
    families: grouped.size,
    multi_root_families: multi.length,
    scanned_rooted_rows: multi.reduce((n,g) => n+g.length,0),
    cutoff_snapshots_per_root: cutoff,
    sampled_snapshots: sampled,
    merges: mergers,
    early_halts: halts
  };
}

function main() {
  const source = path.resolve(__dirname, "../holdout-family-coverage/2026-10-16-rooted-ledger.csv");
  const rows = readLedger(fs.readFileSync(source, "utf8"));
  const report = scan(rows);
  if (report.source_rows !== 663 || report.multi_root_families !== 145
      || report.scanned_rooted_rows !== 373) {
    throw new Error("Input root counts differ from pinned inventory");
  }
  console.log(JSON.stringify(report, null, 2));
}

if (require.main === module) main();
module.exports = {readLedger, parseTable, scan};
