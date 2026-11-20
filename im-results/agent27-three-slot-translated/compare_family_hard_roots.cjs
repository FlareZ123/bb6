#!/usr/bin/env node
"use strict";

/*
 * Compare all 80 parameterized three-slot translated cylinders with the
 * pinned rooted BB(6) rosters under the repository's exact allowed
 * symmetries: state permutations fixing initial state A, plus optional
 * left/right reflection. Blank symbol 0 is never complemented.
 *
 * Run from the repository root:
 *   node im-results/agent27-three-slot-translated/compare_family_hard_roots.cjs
 *
 * This is a finite roster screen only. It does not prove that the 663-root
 * snapshot is the current complete holdout set, nor does a zero hit establish
 * anything about machines outside the checked rosters.
 */

const fs = require("node:fs");
const path = require("node:path");
const assert = require("node:assert/strict");
const root = path.resolve(__dirname, "../..");
const { parse } = require(path.join(root, "tools/holdout_families.cjs"));

const candidatePath = path.join(__dirname, "candidates.json");
const rawPath = path.join(root, "resources/BB6_holdouts_663_2026-10-16.txt");
const ledgerPath = path.join(root, "im-results/holdout-family-coverage/2026-10-16-rooted-ledger.csv");
const removed40Path = path.join(root, "im-results/agent4-dated-roster/removed-663-to-623.tsv");
const removed15Path = path.join(root, "im-results/agent4-dated-roster/removed-623-to-608.tsv");

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

function transformedRows(candidate, order, reflect) {
  const inverse = Array(6);
  for (let newState = 0; newState < 6; newState++) {
    inverse[order[newState]] = newState;
  }

  return candidate.transitions.map(row => {
    const [oldStateLetter, bitText] = row.slot.split("/");
    const oldState = oldStateLetter.charCodeAt(0) - 65;
    const oldNext = row.action.charCodeAt(2) - 65;
    const direction = reflect
      ? (row.action[1] === "L" ? "R" : "L")
      : row.action[1];

    return {
      slot: String.fromCharCode(65 + inverse[oldState]) + "/" + bitText,
      state: inverse[oldState],
      bit: Number(bitText),
      action: row.action[0] + direction +
        String.fromCharCode(65 + inverse[oldNext])
    };
  });
}

function matchWitnesses(machineRle, candidate) {
  const table = parse(machineRle);
  const witnesses = [];

  for (const order of orders) {
    for (const reflect of [false, true]) {
      const rows = transformedRows(candidate, order, reflect);
      if (rows.every(row => table[row.state][row.bit] === row.action)) {
        witnesses.push({
          order: order.map(s => String.fromCharCode(65 + s)).join(""),
          reflect,
          transformedRows: rows.map(({ slot, action }) => ({ slot, action }))
        });
      }
    }
  }
  return witnesses;
}

function hitsFor(rles, candidates) {
  return rles.flatMap(rle => {
    const matches = [];
    for (let i = 0; i < candidates.length; i++) {
      const witnesses = matchWitnesses(rle, candidates[i]);
      if (witnesses.length) {
        matches.push({
          candidateIndex: i,
          entry: candidates[i].entry,
          period: candidates[i].period,
          displacement: candidates[i].displacement,
          witnesses
        });
      }
    }
    return matches.length ? [{ rle, matches }] : [];
  });
}

function pairwiseConflictCount(candidates) {
  let conflicts = 0;
  const compatiblePairs = [];
  for (let i = 0; i < candidates.length; i++) {
    const left = new Map(candidates[i].transitions.map(row => [row.slot, row.action]));
    for (let j = i + 1; j < candidates.length; j++) {
      const conflict = candidates[j].transitions.some(row =>
        left.has(row.slot) && left.get(row.slot) !== row.action
      );
      if (conflict) conflicts++;
      else compatiblePairs.push([i, j]);
    }
  }
  return { conflicts, compatiblePairs };
}

const source = JSON.parse(fs.readFileSync(candidatePath, "utf8"));
const candidates = source.candidates;
assert.equal(candidates.length, 80);
assert.equal(new Set(candidates.map(c => c.transitions
  .map(row => row.slot + "=" + row.action).sort().join("|"))).size, 80);

const raw = fs.readFileSync(rawPath, "utf8").trim().split(/\s+/);
const csvLines = fs.readFileSync(ledgerPath, "utf8").trim().split(/\r?\n/);
const header = parseCsvLine(csvLines[0]);
const ledgerRows = csvLines.slice(1).map(parseCsvLine);
const columns = Object.fromEntries(header.map((name, i) => [name, i]));
const ledgerRaw = ledgerRows.map(row => row[columns.rooted_rle]);

const removed40 = readRemoved(removed40Path);
const removed15 = readRemoved(removed15Path);
const removed = [...removed40, ...removed15];
const removedSet = new Set(removed.map(row => row.rle));
const retained608 = raw.filter(rle => !removedSet.has(rle));

const rawSet = new Set(raw);
const ledgerSet = new Set(ledgerRaw);
assert.equal(raw.length, 663);
assert.equal(rawSet.size, 663);
assert.equal(ledgerRows.length, 663);
assert.equal(ledgerSet.size, 663);
assert.deepEqual(rawSet, ledgerSet);
assert.equal(removed40.length, 40);
assert.equal(removed15.length, 15);
assert.equal(removedSet.size, 55);
assert(removed.every(row => rawSet.has(row.rle)));
assert.equal(retained608.length, 608);
assert.equal(new Set(retained608).size, 608);

const conflicts = pairwiseConflictCount(candidates);
assert.equal(conflicts.conflicts, 3160);
assert.equal(conflicts.compatiblePairs.length, 0);

const rosters = {
  historical663: raw,
  canonicalLedger663: ledgerRaw,
  reconstructedOct30_608: retained608,
  removed55: removed.map(row => row.rle)
};

const comparison = {};
for (const [name, rles] of Object.entries(rosters)) {
  const hits = hitsFor(rles, candidates);
  comparison[name] = {
    rosterSize: rles.length,
    distinctMatchingMachines: hits.length,
    distinctCandidateIndices: [...new Set(hits.flatMap(hit =>
      hit.matches.map(match => match.candidateIndex)
    ))].length,
    matches: hits
  };
}

const output = {
  candidateFamily: {
    count: candidates.length,
    entryHistogram: candidates.reduce((acc, c) => {
      acc[c.entry] = (acc[c.entry] || 0) + 1;
      return acc;
    }, {}),
    periodHistogram: candidates.reduce((acc, c) => {
      acc[c.period] = (acc[c.period] || 0) + 1;
      return acc;
    }, {}),
    pairwiseConflictingPairs: conflicts.conflicts,
    compatiblePairs: conflicts.compatiblePairs.length,
    massEach: "25^9 = 3814697265625",
    disjointUnionMass: (80n * 25n ** 9n).toString(),
    fractionOfAllTables: "0.512%"
  },
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
  comparison
};

console.log(JSON.stringify(output, null, 2));
