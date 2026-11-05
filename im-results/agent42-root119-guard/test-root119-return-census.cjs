'use strict';

const assert = require('node:assert/strict');

const RULES = '1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD'.split('_');
const LIMIT = 10_000_000;

/** @typedef {{time: number, head: number, validTen: boolean}} BSection */
/** @typedef {{head: number, n: number}} WavePrediction */

/** @param {Set<number>} tape @param {number} head */
function tenStepEligible(tape, head) {
  const expected = [1, 1, 1, 0, 1];
  return expected.every((value, index) => Number(tape.has(head - index - 1)) === value);
}

/** @param {Set<number>} tape @param {number} head */
function waveLength(tape, head) {
  if (tape.has(head - 1)) return null;
  let ones = 0;
  while (tape.has(head + 1 + ones)) ones++;
  if (ones % 2 === 0) return null;
  return (ones - 1) / 2;
}

const tape = new Set();
const wavePredictions = new Map();
const unclassifiedLengthCounts = new Map();
let q = 'A';
let head = 0;
let previous = null;
let bSections = 0;
let tenStepReturns = 0;
let waveReturns = 0;
let otherReturns = 0;
let maximumWaveN = 0;
let totalWaveSteps = 0;

for (let time = 0; time < LIMIT; time++) {
  const bit = Number(tape.has(head));
  if (q === 'F' && bit === 1) {
    const n = waveLength(tape, head);
    if (n !== null) {
      const returnTime = time + 4 * n + 5;
      assert.ok(!wavePredictions.has(returnTime), 'Overlapping return-time predictions');
      wavePredictions.set(returnTime, { head: head - 1, n });
      maximumWaveN = Math.max(maximumWaveN, n);
      totalWaveSteps += 4 * n + 5;
    }
  }

  if (q === 'B' && bit === 0) {
    bSections++;
    if (previous !== null) {
      const duration = time - previous.time;
      const predicted = wavePredictions.get(time);
      if (predicted !== undefined) {
        assert.equal(head, predicted.head, 'Incorrect F/1 wave endpoint');
        assert.ok(duration > 10, 'Wave unexpectedly overlaps a 10-step first return');
        waveReturns++;
        wavePredictions.delete(time);
      } else if (duration === 10) {
        assert.ok(previous.validTen, 'Ten-step return violates exact macro hypothesis');
        tenStepReturns++;
      } else {
        otherReturns++;
        unclassifiedLengthCounts.set(
          duration, (unclassifiedLengthCounts.get(duration) || 0) + 1
        );
      }
    }
    previous = { time, head, validTen: tenStepEligible(tape, head) };
  }

  const instruction = RULES[q.charCodeAt(0) - 65].slice(bit * 3, bit * 3 + 3);
  assert.notEqual(instruction, '---', `Unexpected blank-root halt at time ${time}`);
  if (instruction[0] === '1') tape.add(head);
  else tape.delete(head);
  head += instruction[1] === 'R' ? 1 : -1;
  q = instruction[2];
}

assert.equal(wavePredictions.size, 0, 'Some wave endpoints exceed the execution cutoff');
assert.equal(tenStepReturns + waveReturns + otherReturns, bSections - 1);
assert.deepEqual(
  [bSections, tenStepReturns, waveReturns, otherReturns, maximumWaveN],
  [22_984, 15_176, 7_508, 299, 754],
  'Regression against the audited ten-million-step census'
);

console.log(JSON.stringify({
  rawSteps: LIMIT,
  bZeroSections: bSections,
  firstReturnIntervals: bSections - 1,
  tenStepReturns,
  verifiedWaveEndpoints: waveReturns,
  otherReturns,
  totalWaveSteps,
  maximumWaveN,
  otherReturnLengths: [...unclassifiedLengthCounts]
    .sort((left, right) => right[1] - left[1])
    .map(([length, count]) => ({ length, count }))
}, null, 2));
