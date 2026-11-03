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

// Explore all 5! state renamings fixing the blank initial state A, and both tape directions.
/** @type {number[][]} */
const rootPermutations = [];
/** @param {number[]} prefix @param {number[]} available */
function enumerate(prefix, available) {
  if (!available.length) {
    rootPermutations.push([0, ...prefix]);
    return;
  }
  for (let i = 0; i < available.length; i++) {
    enumerate([...prefix, available[i]], available.filter((_, j) => i !== j));
  }
}
enumerate([], [1, 2, 3, 4, 5]);
assert.equal(rootPermutations.length, 120);

/** @param {string} code @returns {string} */
function rootedSymmetryCanonical(code) {
  const rule = code.split('_').flatMap((pair) => [pair.slice(0, 3), pair.slice(3)]);
  let minimum = '~';
  for (const stateMap of rootPermutations) {
    for (const reflect of [false, true]) {
      const transformed = new Array(12);
      for (let q = 0; q < 6; q++) {
        for (let bit = 0; bit < 2; bit++) {
          const action = rule[2 * q + bit];
          const result = action === '---' ? '---'
            : action[0] + (reflect ? (action[1] === 'R' ? 'L' : 'R') : action[1])
              + String.fromCharCode(65 + stateMap[action.charCodeAt(2) - 65]);
          transformed[2 * stateMap[q] + bit] = result;
        }
      }
      const candidate = Array.from({length: 6}, (_, q) =>
        transformed[2 * q] + transformed[2 * q + 1]).join('_');
      if (candidate < minimum) minimum = candidate;
    }
  }
  return minimum;
}
const proofCanonicals = new Set(records.map((r) => rootedSymmetryCanonical(r.code)));
assert.equal(proofCanonicals.size, 181);
const isomorphic = [...retainedSet].filter((code) =>
  proofCanonicals.has(rootedSymmetryCanonical(code)));
assert.equal(isomorphic.length, 9);
assert.ok(isomorphic.every((code) => retained.some((r) => r.code === code)));
console.log('PASS: all 240 A-preserving state/direction symmetries add zero further retained roots');

console.log('PASS: all 663 Oct16 rooted RLEs validated; 55 exact rooted removals; 608 retained');
console.log('PASS: pinned upstream Cryptids source manifest 181 entries, 31 halt and 150 nonhalt');
console.log('PASS: exact rooted overlap Oct16 29, of which 9 survive Oct30 (4 halt, 5 nonhalt)');
console.log('PASS: previously certified retained F287 is distinct from these nine');
for (const r of retained) console.log(r.status + '\t' + r.code + '\t' + r.source);
console.log('Science status: source proof existence; independent Lean compilation required for certification');
