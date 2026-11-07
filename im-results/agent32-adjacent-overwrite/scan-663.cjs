'use strict';

const assert = require('node:assert/strict');
const fs = require('node:fs');
const crypto = require('node:crypto');
const path = require('node:path');

/**
 * This scanner is independent of the Lean source proof. It checks the exact
 * finite syntactic hypotheses under which BB6Overwrite.forbidden_transition
 * excludes a specified immediate halting predecessor for all blank-root times.
 * No machine is classified as halting or nonhalting by this scan.
 *
 * @typedef {{state:number, read:boolean, halt:true} |
 *   {state:number, read:boolean, halt:false,
 *    write:boolean, right:boolean, next:number}} Rule
 */

/** @param {boolean} bit @returns {string} */
function bool(bit) {
  return bit ? 'true' : 'false';
}

/** @param {string} rle @returns {Rule[]} */
function parse(rle) {
  const sections = rle.split('_');
  assert.equal(sections.length, 6, 'six states per RLE');
  const rules = [];
  for (const [state, row] of sections.entries()) {
    assert.equal(row.length, 6, 'two triple instructions per state');
    for (let b = 0; b < 2; b += 1) {
      const instr = row.slice(3 * b, 3 * b + 3);
      if (instr === '---') {
        rules.push({state, read: b === 1, halt: true});
        continue;
      }
      assert.match(instr, /^[01][LR][A-F]$/);
      rules.push({
        state, read: b === 1, halt: false,
        write: instr[0] === '1', right: instr[1] === 'R',
        next: instr.charCodeAt(2) - 65,
      });
    }
  }
  return rules;
}

/** @param {Rule} rule @returns {string} */
function leanRule(rule) {
  if (rule.halt) return 'none';
  return `some ⟨${bool(rule.write)}, ${bool(rule.right)}, ⟨${rule.next}, by decide⟩⟩`;
}

/**
 * @param {Rule[]} rules
 * @returns {{halt:Rule, before:Rule, numEntering:number}[]}
 */
function blockedPredecessors(rules) {
  const blocked = [];
  for (const halt of rules.filter((rule) => rule.halt)) {
    const incoming = rules.filter((rule) => !rule.halt && rule.next === halt.state);
    for (const edge of incoming) {
      const parents = rules.filter((rule) => !rule.halt && rule.next === edge.state);
      const validOnEntry = parents.every((parent) =>
        parent.write !== halt.read && parent.right !== edge.right);
      const validAtBlankStart = edge.state !== 0 || halt.read === true;
      if (validOnEntry && validAtBlankStart) {
        blocked.push({halt, before: edge, numEntering: incoming.length});
      }
    }
  }
  return blocked;
}

/** @param {string} source @param {number} index @param {string} rle
 *  @param {Rule[]} rules @param {{halt:Rule,before:Rule}} cert */
function verifyLeanTable(source, index, rle, rules, cert) {
  const first = source.indexOf(`def root${index} : Machine := fun (q,b) =>`);
  const last = source.indexOf(`private theorem root${index}_entry :`, first);
  assert(first >= 0 && last > first, `missing machine ${index}`);
  assert(source.includes(`Holdout #${index}: ${rle}`));
  const definition = source.slice(first, last);
  for (const rule of rules) {
    const expected = `  | ${rule.state}, ${bool(rule.read)} => ${leanRule(rule)}`;
    assert(definition.includes(expected), `holdout #${index} table mismatch: ${expected}`);
  }
  const theorem = source.indexOf(`theorem root${index}_forbidden_parent`, last);
  assert(theorem > last, `missing verified parent theorem root${index}`);
  assert(source.includes(`t.next = ⟨${cert.before.state}, by decide⟩`));
}

const corpusFile = path.resolve(__dirname, '../../resources/BB6_holdouts_663_2026-10-16.txt');
const leanFile = path.resolve(__dirname, 'Overwrite55.lean');
const corpus = fs.readFileSync(corpusFile, 'utf8');
const lean = fs.readFileSync(leanFile, 'utf8');
const lines = corpus.trim().split(/\r?\n/);
assert.equal(lines.length, 663, 'pinned historical holdout census length');

const selected = [];
for (const [ordinal, rle] of lines.entries()) {
  const rules = parse(rle);
  for (const cert of blockedPredecessors(rules)) {
    selected.push({index: ordinal + 1, rle, rules, cert});
  }
}
assert.equal(selected.length, 55, 'distinct blocked predecessor instances');
assert.equal(new Set(selected.map((value) => value.index)).size, 55,
  'one blocked incoming edge per selected holdout');

for (const {index, rle, rules, cert} of selected) {
  assert.equal(cert.numEntering, 2, 'one remaining halting-state entry');
  verifyLeanTable(lean, index, rle, rules, cert);
}
const printedTheorems = [...lean.matchAll(/^#print axioms root(\d+)_forbidden_parent$/gm)];
assert.equal(printedTheorems.length, selected.length, 'one printed theorem per certificate');
assert.deepEqual(printedTheorems.map((match) => Number(match[1])),
  selected.map((item) => item.index));

process.stdout.write(`${JSON.stringify({
  result: 'verified-corpus-to-Lean-table-identity',
  corpusSha256: crypto.createHash('sha256').update(corpus).digest('hex'),
  totalHistoricalHoldouts: lines.length,
  rootsWithOneBlockedImmediateHaltingPredecessor: selected.length,
  indices: selected.map((item) => item.index),
}, null, 2)}\n`);
