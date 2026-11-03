'use strict';

/**
 * Source-pinned root audit for the five October 2026 Rocq-reported BB(6) halters.
 * Run from the repository root with Node.js: node im-results/agent46-rocq-original-source/audit.cjs
 * This verifies the upstream source text and blank-root syntactic conjugacy.
 * It does not compile Rocq or certify any claimed exact halting runtime.
 */
const assert = require('node:assert/strict');
const crypto = require('node:crypto');
const fs = require('node:fs');
const path = require('node:path');

const dir = __dirname;
const sources = {
  v3: { name: 'Others_v3.v', sha: 'ab372a2521d386c39ce68e57baa5d6d52d1f49d0' },
  v4: { name: 'Others_v4.v', sha: '82c3fe38fc4d56d45722e27190745ba7a068ecba' }
};

/** @param {Buffer} bytes */
function blobSha(bytes) {
  return crypto.createHash('sha1').update(Buffer.from('blob ' + bytes.length + '\0')).update(bytes).digest('hex');
}

/** @param {string} src @param {string} mod */
function sourceMachine(src, mod) {
  const marker = 'Module ' + mod + '.';
  const start = src.indexOf(marker);
  assert(start >= 0, 'missing original Rocq module ' + mod);
  const end = src.indexOf('End ' + mod + '.', start);
  assert(end > start, 'missing module end for ' + mod);
  const body = src.slice(start, end);
  const match = body.match(/Definition tm := Eval compute in \(TM_from_str "([^"]+)"\)\./);
  assert(match, 'missing TM_from_str in ' + mod);
  assert.match(body, /Theorem halt:\s*halts tm c0\s*\.\s*Proof\.[\s\S]*?native_check_eq\.[\s\S]*?Qed\./, 'missing source halting theorem for ' + mod);
  return match[1];
}

/** @param {string} code */
function reflect(code) {
  return code.replace(/[LR]/g, c => c === 'L' ? 'R' : 'L');
}

/**
 * @param {string} code
 * @returns {Array<[string,string]>}
 */
function parse(code) {
  const rows = code.split('_');
  assert.equal(rows.length, 6, 'six states required');
  const moves = new Set(['L', 'R']);
  const states = new Set(['A', 'B', 'C', 'D', 'E', 'F']);
  let halts = 0;
  const out = [];
  for (const row of rows) {
    assert.equal(row.length, 6, 'two actions per state');
    /** @type {string[]} */
    const acts = [];
    for (const a of [row.slice(0, 3), row.slice(3)]) {
      if (a === '---') { halts++; acts.push(a); continue; }
      assert.equal(a.length, 3);
      assert(['0', '1'].includes(a[0]));
      assert(moves.has(a[1]));
      assert(states.has(a[2]));
      acts.push(a);
    }
    out.push(/** @type {[string,string]} */ (acts));
  }
  assert.equal(halts, 1, 'single absent halt action');
  return out;
}

/**
 * @param {Array<[string,string]>} table
 * @param {number} count
 * @returns {{q: number, head: number, tape: Map<number,number>, halted: boolean}}
 */
function simulate(table, count) {
  let q = 0;
  let head = 0;
  const tape = new Map();
  for (let step = 0; step < count; step++) {
    const symbol = tape.get(head) || 0;
    const a = table[q][symbol];
    if (a === '---') return {q, head, tape, halted: true};
    const write = Number(a[0]);
    if (write) tape.set(head, 1);
    else tape.delete(head);
    head += a[1] === 'R' ? 1 : -1;
    q = a.charCodeAt(2) - 65;
  }
  return {q, head, tape, halted: false};
}

const loaded = {};
for (const [key, source] of Object.entries(sources)) {
  const bytes = fs.readFileSync(path.join(dir, source.name));
  assert.equal(blobSha(bytes), source.sha, source.name + ' original Git object differs');
  const data = bytes.toString('utf8');
  assert(!/\b(?:Admitted|Axiom)\s*(?:\.|[A-Za-z_])/.test(data), 'unexpected explicit proof escape in ' + source.name);
  loaded[key] = data;
  console.log('Verified original source blob', source.name, source.sha, bytes.length, 'bytes');
}

const records = [
  {key:'v3', module:'TM9', root:'1RB0LC_1RC0RC_1LD0RB_1LA1LE_0RA0LF_0LD---', direction:'direct'},
  {key:'v3', module:'TM6', root:'1RB0LD_1RC1RE_1LD0RA_1LA0LA_0LC0RF_0RB---', direction:'mirror'},
  {key:'v3', module:'TM7', root:'1RB1RE_1LC0RD_1LD0LD_1RA0LC_0LB0RF_0RA---', direction:'mirror'},
  {key:'v3', module:'TM8', root:'1RB0RB_1LC0RA_1LE1LD_0RE0LF_1RA0LB_0LC---', direction:'direct'},
  {key:'v4', module:'TM', root:'1RB1LD_1RC0RB_0LA1RE_1LA0LB_0RA0RF_---0LC', direction:'direct'}
];
for (const record of records) {
  const src = sourceMachine(loaded[record.key], record.module);
  const expected = record.direction === 'mirror' ? reflect(record.root) : record.root;
  assert.equal(src, expected, 'blank-root table mismatch for ' + record.module);
  const target = parse(record.root);
  const original = parse(src);
  const n = 10000;
  const x = simulate(target, n);
  const y = simulate(original, n);
  assert.equal(x.halted, y.halted);
  assert.equal(x.q, y.q);
  assert.equal(x.head, record.direction === 'mirror' ? -y.head : y.head);
  assert.equal(x.tape.size, y.tape.size);
  for (const [pos,bit] of x.tape) {
    assert.equal(bit, y.tape.get(record.direction === 'mirror' ? -pos : pos));
  }
  console.log(record.module, record.direction, 'exact 12-action match; 10,000-step blank-origin mirror regression PASS; observed halt:',x.halted);
}
assert.match(loaded.v3, /Lemma raw_spec c:\s*transfer c \(raw c\)/);
assert.match(loaded.v3, /Lemma macro_spec c c':/);
assert.match(loaded.v3, /Lemma check_spec n q:\s*check n q=true -> halts tm/);
assert.match(loaded.v3, /Print Assumptions TM7\.halt\./);
assert.match(loaded.v4, /Lemma check_spec n:\s*check n=true -> halts tm c0/);
assert.match(loaded.v4, /Print Assumptions TM\.halt\./);
console.log('PASS: source theorems and exact rooted-table mappings; external Rocq kernel execution and exact raw runtimes remain UNVERIFIED.');
