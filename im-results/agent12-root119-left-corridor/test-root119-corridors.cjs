'use strict';

const assert = require('node:assert/strict');

const rules = '1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD'.split('_');
const tape = new Set();
const counts = { leftA: 0, leftB: 0, right: 0, cross: 0 };
const witnesses = [];
const limit = 10_000_000;
let q = 0;
let h = 0;
let pending = null;
let shieldStarts = 0;
let shieldEnds = 0;

/** @param {number} x */
function bit(x) { return tape.has(x); }
/** @param {number} x */
function runOfOnes(x) {
  let count = 0;
  while (bit(x + count)) count++;
  return count;
}
/** @param {number} x @param {number} size */
function word(x, size) {
  let out = '';
  for (let i = 0; i < size; i++) out += bit(x + i) ? '1' : '0';
  return out;
}
/** @param {number} head */
function shield(head) {
  for (const x of tape) {
    if (x + 3 < head && bit(x + 1) && !bit(x + 2) && !bit(x + 3)) return false;
  }
  return true;
}
/** @param {number} time */
function candidate(time) {
  const left6 = word(h - 6, 6);
  if ((left6 === '100111' || left6 === '101001') && !bit(h - 7)) {
    let n = 0;
    while (bit(h - 8 - 2 * n) && !bit(h - 9 - 2 * n)) n++;
    if (!bit(h - 8 - 2 * n)) {
      return { type: left6 === '100111' ? 'leftA' : 'leftB',
        n, start: time, head: h, finish: time + 14 + 2 * n,
        finishHead: h - 8 - 2 * n };
    }
  }
  if (left6 === '000000') {
    const r = runOfOnes(h + 1);
    if (r % 2 === 0 && !bit(h + r + 2)) {
      const n = r / 2;
      return { type: 'right', n, start: time, head: h,
        finish: time + 2 * n + 12, finishHead: h + 2 * n + 2 };
    }
  }
  if (left6 === '101010') {
    const r = runOfOnes(h + 1);
    if (r % 2 === 0) {
      const n = r / 2;
      let m = 1;
      while (bit(h - 2 * m) && !bit(h - 2 * m - 1)) m++;
      if (m >= 2 && !bit(h - 2 * m)) {
        return { type: 'cross', n, m, start: time, head: h,
          finish: time + 4 * n + 2 * m + 6, finishHead: h - 2 * m };
      }
    }
  }
  return null;
}

for (let time = 0; time < limit; time++) {
  const symbol = Number(bit(h));
  if (q === 1 && symbol === 0) {
    if (pending !== null) {
      assert.equal(time, pending.finish, `Early/wrong B0 return after ${pending.start}`);
      assert.equal(h, pending.finishHead, `Wrong B0 return head after ${pending.start}`);
      counts[pending.type]++;
      shieldEnds += Number(shield(h));
      witnesses.push(pending);
      pending = null;
    }
    const next = candidate(time);
    if (next !== null) {
      pending = next;
      shieldStarts += Number(shield(h));
    }
  }
  const rule = rules[q].slice(symbol * 3, symbol * 3 + 3);
  assert.notEqual(rule, '---', `Unexpected halt at ${time}`);
  if (rule[0] === '1') tape.add(h);
  else tape.delete(h);
  h += rule[1] === 'R' ? 1 : -1;
  q = rule.charCodeAt(2) - 65;
}
assert.equal(pending, null, 'Unfinished corridor return at replay cutoff');
assert.deepEqual(counts, { leftA: 21, leftB: 10, right: 18, cross: 2 });
assert.equal(shieldStarts, 51);
assert.equal(shieldEnds, 51);
console.log(JSON.stringify({ rawSteps: limit, certifiedConditionalFamilyInstances: counts,
  inputShielded: shieldStarts, outputShielded: shieldEnds,
  doubleSweepInstances: witnesses.filter(x => x.type === 'cross'),
  previouslyClassifiedLeftAStarts: [1275, 3638],
  total: witnesses.length }, null, 2));
