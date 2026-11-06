'use strict';

const assert = require('node:assert/strict');

const RULES = '1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD'.split('_');
const LIMIT = 10_000_000;
const tape = new Set();
const predictions = new Map();
let state = 'A';
let head = 0;
let previousBZero = null;
let bZeros = 0;
const counts = { ten: 0, oldWave: 0, leftOneWave: 0, other: 0 };

/** @param {number} h */
function positiveRunLength(h) {
  let length = 0;
  while (tape.has(h + 1 + length)) length++;
  return length % 2 === 1 ? (length - 1) / 2 : null;
}

for (let time = 0; time < LIMIT; time++) {
  const symbol = Number(tape.has(head));

  if (state === 'F' && symbol === 1) {
    const n = positiveRunLength(head);
    if (n !== null) {
      let type;
      let returnTime;
      let returnHead;
      if (!tape.has(head - 1)) {
        type = 'oldWave';
        returnTime = time + 4 * n + 5;
        returnHead = head - 1;
      } else if (!tape.has(head - 2) && !tape.has(head - 3)) {
        type = 'leftOneWave';
        returnTime = time + 4 * n + 7;
        returnHead = head - 3;
      }
      if (type !== undefined) {
        const old = predictions.get(returnTime);
        if (old) {
          assert.equal(old.head, returnHead, 'Nested wave predictions disagree');
        } else {
          predictions.set(returnTime, { type, head: returnHead });
        }
      }
    }
  }

  if (state === 'B' && symbol === 0) {
    bZeros++;
    if (previousBZero !== null) {
      const expected = predictions.get(time);
      if (expected) {
        assert.equal(head, expected.head, 'Wave theorem endpoint disagrees with raw machine');
        counts[expected.type]++;
        predictions.delete(time);
      } else if (time - previousBZero === 10) {
        counts.ten++;
      } else {
        counts.other++;
      }
    }
    previousBZero = time;
  }

  const rule = RULES[state.charCodeAt(0) - 65].slice(symbol * 3, symbol * 3 + 3);
  assert.notEqual(rule, '---', `Unexpected halt at step ${time}`);
  if (rule[0] === '1') tape.add(head);
  else tape.delete(head);
  head += rule[1] === 'R' ? 1 : -1;
  state = rule[2];
}

assert.equal(bZeros, 22_984);
assert.deepEqual(counts, { ten: 15_176, oldWave: 7_508, leftOneWave: 177, other: 122 });
assert.equal(Object.values(counts).reduce((a, b) => a + b, 0), bZeros - 1);
assert.equal(predictions.size, 0, 'Unfinished wave predictions at cutoff');
console.log(JSON.stringify({ rawSteps: LIMIT, bZeroSections: bZeros, firstReturnClasses: counts }, null, 2));
