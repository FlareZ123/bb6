#!/usr/bin/env node
"use strict";

/*
 * Compare Agent 32's five-slot translated cylinder with the repository's
 * rooted BB(6) holdout rosters under exactly the symmetries used by
 * tools/holdout_families.cjs: state renaming fixing initial state A, and
 * optional left/right reflection. Blank symbol 0 is fixed.
 *
 * Reproduce from the repository root:
 *   node im-results/agent27-five-slot-hard-root-check/compare_five_slot_hard_roots.cjs
 *
 * Snapshot result (2026-11-20):
 *   historical 663 raw roots:       0 matching machines, 0 witnesses
 *   canonical 663-row ledger:       0 matching machines, 0 witnesses
 *   reconstructed Oct30 608 roots:  0 matching machines, 0 witnesses
 *   55 documented removals:         0 matching machines, 0 witnesses
 *
 * The Oct30 608 set is reconstructed from the 663 snapshot by subtracting
 * the repository's exact 40-row and 15-row removal ledgers. It is not a
 * separately mirrored raw 608 file.
 */

const fs = require("node:fs");
const path = require("node:path");
const assert = require("node:assert/strict");
const root = path.resolve(__dirname, "../..");
const { parse } = require(path.join(root, "tools/holdout_families.cjs"));

const rawPath = path.join(root, "resources/BB6_holdouts_663_2026-10-16.txt");
const ledgerPath = path.join(root, "im-results/holdout-family-coverage/2026-10-16-rooted-ledger.csv");
const removed40Path = path.join(root, "im-results/agent4-dated-roster/removed-663-to-623.tsv");
const removed15Path = path.join(root, "im-results/agent4-dated-roster/removed-623-to-608.tsv");

const candidate = [
  { state: 0, bit: 0, action: "1RB" }, // A/0
  { state: 1, bit: 0, action: "1LC" }, // B/0
  { state: 2, bit: 1, action: "0RD" }, // C/1
  { state: 3, bit: 1, action: "1RE" }, // D/1
  { state: 4, bit: 0, action: "1LC" }  // E/0
];

function parseCsvLine(line) {
  const fields = [];
  let field = "";
  let quoted = false;
  for (let i = 0; i < line.length; i++) {
    const ch = line[i];
    if (quoted) {
      if (ch === '"' && line[i + 1] === '"') {
        field += '"';
        i++;
      } else if (ch === '"') {
        quoted = false;
      } else {
        field += ch;
      }
    } else if (ch === '"') {
      quoted = true;
    } else if (ch === ",") {
      fields.push(field);
      field = "";
    } else {
      field += ch;
    }
  }
  fields.push(field);
  return fields;
}

function permutations(items) {
  if (items.length <= 1) return [items];
  const out = [];
  for (let i = 0; i < items.length; i++) {
    for (const tail of permutations(items.filter((_, j) => j !== i))) {
      out.push([items[i], ...tail]);
    }
  }
  return out;
}

// order[newState] = oldState, with old A fixed at new A.
const orders = permutations([1, 2, 3, 4, 5]).map(tail => [0, ...tail]);

function matchWitnesses(machineRle) {
  const table = parse(machineRle);
  const witnesses = [];

  for (const order of orders) {
    const inverse = Array(6);
    for (let newState = 0; newState < 6; newState++) {
      inverse[order[newState]] = newState;
    }

    for (const reflect of [false, true]) {
      let matches = true;
      const transformedRows = [];

      for (const row of candidate) {
        const oldNext = row.action.charCodeAt(2) - 65;
        const direction = reflect
          ? (row.action[1] === "L" ? "R" : "L")
          : row.action[1];
        const transformedAction =
          row.action[0] + direction + String.fromCharCode(65 + inverse[oldNext]);
        const transformedState = inverse[row.state];

        transformedRows.push({
          slot: `${String.fromCharCode(65 + transformedState)}/${row.bit}`,
          action: transformedAction
        });

        if (table[transformedState][row.bit] !== transformedAction) {
          matches = false;
          break;
        }
      }

      if (matches) {
        witnesses.push({
          order: order.map(s => String.fromCharCode(65 + s)).join(""),
          reflect,
          transformedRows
        });
      }
    }
  }
  return witnesses;
}

function readRemoved(file) {
  return fs.readFileSync(file, "utf8")
    .split(/\r?\n/)
    .filter(line => line && !line.startsWith("#"))
    .map(line => {
      const fields = line.split("\t");
      if (fields.length !== 2) throw new Error("Malformed removal row: " + line);
      return { originalLine: Number(fields[0]), rle: fields[1] };
    });
}

function hitsFor(rles) {
  return rles.flatMap(rle => {
    const witnesses = matchWitnesses(rle);
    return witnesses.length ? [{ rle, witnesses }] : [];
  });
}

const raw = fs.readFileSync(rawPath, "utf8").trim().split(/\s+/);
const csvLines = fs.readFileSync(ledgerPath, "utf8").trim().split(/\r?\n/);
const header = parseCsvLine(csvLines[0]);
const ledgerRows = csvLines.slice(1).map(parseCsvLine);
const columns = Object.fromEntries(header.map((name, i) => [name, i]));
const ledgerRaw = ledgerRows.map(row => row[columns.rooted_rle]);

const removed40 = readRemoved(removed40Path);
const removed15 = readRemoved(removed15Path);
const removed = [...removed40, ...removed15];
const rawSet = new Set(raw);
const ledgerSet = new Set(ledgerRaw);
const removedSet = new Set(removed.map(row => row.rle));
const retained608 = raw.filter(rle => !removedSet.has(rle));

assert.equal(raw.length, 663);
assert.equal(rawSet.size, 663);
assert.equal(ledgerRows.length, 663);
assert.equal(ledgerSet.size, 663);
assert.deepEqual(rawSet, ledgerSet);
assert.equal(removed40.length, 40);
assert.equal(removed15.length, 15);
assert.equal(removedSet.size, 55);
assert(removed.every(row => rawSet.has(row.rle)));
assert(removed40.every(row => !new Set(removed15.map(x => x.rle)).has(row.rle)));
assert.equal(retained608.length, 608);
assert.equal(new Set(retained608).size, 608);

const historicalHits = hitsFor(raw);
const ledgerHits = hitsFor(ledgerRaw);
const current608Hits = hitsFor(retained608);
const removedHits = hitsFor(removed.map(row => row.rle));

const output = {
  candidate: candidate.map(row => ({
    slot: `${String.fromCharCode(65 + row.state)}/${row.bit}`,
    action: row.action
  })),
  allowedSymmetries: {
    rootStateFixed: "A",
    statePermutations: orders.length,
    leftRightReflections: 2,
    total: orders.length * 2,
    blankSymbolComplemented: false
  },
  rosterIntegrity: {
    historicalRawCount: raw.length,
    historicalUniqueCount: rawSet.size,
    canonicalLedgerRows: ledgerRows.length,
    canonicalLedgerUniqueCount: ledgerSet.size,
    rawAndLedgerSetsEqual: true,
    removed663To623: removed40.length,
    removed623To608: removed15.length,
    removedUnion: removedSet.size,
    reconstructedOct30Count: retained608.length,
    reconstructedOct30UniqueCount: new Set(retained608).size
  },
  comparison: {
    historical663: {
      distinctMatchingMachines: historicalHits.length,
      symmetryWitnesses: historicalHits.reduce((n, x) => n + x.witnesses.length, 0),
      matches: historicalHits
    },
    canonicalLedger663: {
      distinctMatchingMachines: ledgerHits.length,
      symmetryWitnesses: ledgerHits.reduce((n, x) => n + x.witnesses.length, 0),
      matches: ledgerHits
    },
    reconstructedOct30_608: {
      distinctMatchingMachines: current608Hits.length,
      symmetryWitnesses: current608Hits.reduce((n, x) => n + x.witnesses.length, 0),
      matches: current608Hits
    },
    removed55: {
      distinctMatchingMachines: removedHits.length,
      symmetryWitnesses: removedHits.reduce((n, x) => n + x.witnesses.length, 0),
      matches: removedHits
    }
  }
};

console.log(JSON.stringify(output, null, 2));
