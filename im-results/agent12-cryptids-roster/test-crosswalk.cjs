'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

const root = path.resolve(__dirname, '..', '..');
const lines = (file) => fs.readFileSync(path.join(root, file), 'utf8')
  .split(/\r?\n/).map((line) => line.trim()).filter(Boolean);
const roster663 = lines('resources/BB6_holdouts_663_2026-10-16.txt');
const readRemovals = (file) => lines(file).filter((line) => !line.startsWith('#'))
  .map((line) => line.split('\t').at(-1));
const removed = [
  ...readRemovals('im-results/agent4-dated-roster/removed-663-to-623.tsv'),
  ...readRemovals('im-results/agent4-dated-roster/removed-623-to-608.tsv'),
];
const validRLE = /^((?:[01][RL][A-F]|---){2}_){5}(?:[01][RL][A-F]|---){2}$/;
assert.equal(roster663.length, 663);
assert.equal(new Set(roster663).size, 663);
assert.equal(removed.length, 55);
assert.equal(new Set(removed).size, 55);
const originalSet = new Set(roster663);
const removedSet = new Set(removed);
for (const code of roster663) assert.match(code, validRLE);
for (const code of removed) assert.ok(originalSet.has(code), `foreign removed code ${code}`);
const retainedSet = new Set(roster663.filter((code) => !removedSet.has(code)));
assert.equal(retainedSet.size, 608);

const records = lines('im-results/agent12-cryptids-roster/proof-manifest.tsv')
  .filter((line) => !line.startsWith('#')).map((line) => {
    const [status, code, source, blob] = line.split('\t');
    assert.ok(['halt', 'nonhalt'].includes(status));
    assert.match(code, validRLE);
    assert.match(blob, /^[0-9a-f]{40}$/);
    assert.equal(source.includes('/NonHalt/') ? 'nonhalt' : 'halt', status);
    assert.equal(source.split('/').at(-1), 'M_' + code.replace('---', 'HHH') + '.lean');
    return {status, code, source, blob};
  });
assert.equal(records.length, 181);
assert.equal(records.filter((record) => record.status === 'halt').length, 31);
assert.equal(records.filter((record) => record.status === 'nonhalt').length, 150);
assert.equal(new Set(records.map((x) => x.code)).size, 181);
const oldMatches = records.filter((r) => originalSet.has(r.code));
const retained = oldMatches.filter((r) => retainedSet.has(r.code));
assert.equal(oldMatches.length, 29);
assert.equal(retained.length, 9);
assert.equal(retained.filter((r) => r.status === 'halt').length, 4);
assert.equal(retained.filter((r) => r.status === 'nonhalt').length, 5);
const knownF287 = '1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---';
assert.ok(retainedSet.has(knownF287));
assert.ok(!retained.some((r) => r.code === knownF287));

console.log('PASS: all 663 Oct16 rooted RLEs validated; 55 exact rooted removals; 608 retained');
console.log('PASS: pinned upstream Cryptids source manifest 181 entries, 31 halt and 150 nonhalt');
console.log('PASS: exact rooted overlap Oct16 29, of which 9 survive Oct30 (4 halt, 5 nonhalt)');
console.log('PASS: previously certified retained F287 is distinct from these nine');
for (const r of retained) console.log(r.status + '\t' + r.code + '\t' + r.source);
console.log('Science status: source proof existence; independent Lean compilation required for certification');
