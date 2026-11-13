#!/usr/bin/env node
'use strict';

const assert = require('node:assert/strict');

// Literal six-state auxiliary RLE used by the Root119 census:
// 1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD
const LIMIT = 10_000_000;
const OFFSET = LIMIT;
const tape = new Uint8Array(3 * LIMIT + 16);
const rules = [
  [[1, 1, 1], null],
  [[1, -1, 2], [1, -1, 5]],
  [[1, -1, 3], [0, -1, 2]],
  [[0, -1, 4], [1, 1, 5]],
  [[1, 1, 0], [1, -1, 0]],
  [[1, -1, 1], [0, 1, 3]]
];

let state = 0;
let head = OFFSET;
let eligible = 0;
let matched = 0;
let previousB0 = null;
const samples = [];

function rightRun(first) {
  let length = 0;
  while (tape[first + length] === 1) length++;
  return length;
}

function leftSix(h) {
  let word = '';
  for (let i = 6; i >= 1; i--) word += tape[h - i] === 1 ? '1' : '0';
  return word;
}

for (let time = 0; time < LIMIT; time++) {
  const read = tape[head];

  if (state === 1 && read === 0) {
    if (previousB0?.qualifies) {
      const p = previousB0;
      const expectedSteps = p.run + 12;
      const expectedDisplacement = p.run + 2;
      assert.equal(time - p.time, expectedSteps,
        `return time mismatch from B/0 at t=${p.time}`);
      assert.equal(head - p.head, expectedDisplacement,
        `return head mismatch from B/0 at t=${p.time}`);
      assert.equal(read, 0);
      assert.equal(leftSix(head), '010111',
        `output left boundary mismatch from B/0 at t=${p.time}`);
      matched++;
      if (samples.length < 24) {
        samples.push({
          startTime: p.time,
          startHead: p.head - OFFSET,
          rightRun: p.run,
          n: p.run / 2,
          steps: time - p.time,
          displacement: head - p.head,
          endTime: time,
          endHead: head - OFFSET,
          endLeftSix: leftSix(head)
        });
      }
    }

    const run = rightRun(head + 1);
    const leftZero3 =
      tape[head - 1] === 0 &&
      tape[head - 2] === 0 &&
      tape[head - 3] === 0;
    const nextZero = tape[head + run + 2] === 0;
    const qualifies = leftZero3 && run % 2 === 0 && nextZero;
    if (qualifies) eligible++;
    previousB0 = { time, head, run, qualifies };
  }

  const rule = rules[state][read];
  if (rule === null) throw new Error(`unexpected halt at t=${time}`);
  tape[head] = rule[0];
  head += rule[1];
  state = rule[2];
}

assert.equal(eligible, 18, 'unexpected number of eligible B/0 inputs');
assert.equal(matched, 18, 'not every eligible B/0 input returned by the macro');
console.log(JSON.stringify({
  machine: '1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD',
  transitions: LIMIT,
  eligibleZeroLeftEvenRunInputs: eligible,
  exactReturns: matched,
  observedLaw: '2n+12 steps; head h+2n+2; output left-six 010111',
  samples
}, null, 2));
