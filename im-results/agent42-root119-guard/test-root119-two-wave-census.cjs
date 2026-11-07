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
let cphaseShieldInputs = 0;
let cphaseShieldOutputs = 0;
const prefixShieldAudit = {
  evenPrefix: { inputs: 0, outputs: 0 },
  oddEvenPrefix: { inputs: 0, outputs: 0, boundarySafe: 0 },
};
const prefixLeftSixAudit = { evenPrefix: {}, oddEvenPrefix: {} };
const b0Left101Audit = { count: 0, boundaryUnsafe: 0, leftSix: {}, unsafe: [] };
const counts = {
  oldWave: 0,
  leftOneWave: 0,
  evenPrefix: 0,
  oddEvenPrefix: 0,
  twoWaveRoot: 0,
  prefixUnmatched: 0,
  cphaseD1: 0,
  other: 0,
};
const cphaseRuns = {};
const twoWavePairs = {};
const twoWaveIntervals = [];
const twoWaveShieldAudit = { inputs: 0, outputs: 0 };

/** @param {number} h */
function positiveRunLength(h) {
  let length = 0;
  while (tape.has(h + 1 + length)) length++;
  return length % 2 === 1 ? (length - 1) / 2 : null;
}

/** @param {number} first */
function rightRunLength(first) {
  let length = 0;
  while (tape.has(first + length)) length++;
  return length;
}

/** @param {number} h */
function noLeft1100(h) {
  for (const x of tape) {
    if (x + 3 < h && tape.has(x + 1) && !tape.has(x + 2) && !tape.has(x + 3)) return false;
  }
  return true;
}

/** @param {number} h @param {number} time */
function prefixAtBZero(h, time) {
  if (!(tape.has(h - 1) && !tape.has(h - 2) && tape.has(h - 3))) return null;
  const m = rightRunLength(h + 1) + 1;
  if (m % 2 === 0 && !tape.has(h + m + 1)) {
    return { type: 'evenPrefix', m, returnTime: time + m + 13, returnHead: h + m + 1 };
  }
  if (m % 2 === 1 &&
      !tape.has(h + m + 1) && !tape.has(h + m + 2)) {
    return { type: 'oddEvenPrefix', m, returnTime: time + 3 * m + 20, returnHead: h + m + 2 };
  }
  return { type: 'prefixUnmatched', m };
}

/** @param {number} h @param {number} time */
function cphaseD1AtBZero(h, time) {
  let r = 0;
  while (tape.has(h - 1 - r)) r++;
  if (r < 2 || !tape.has(h - 2 - r)) return null;
  return { r, returnTime: time + r + 7, returnHead: h - r + 1 };
}

/** Exact hypotheses of b0_two_wave_root_interval_to_b0. */
function twoWaveRootAtBZero(h, time) {
  if (!(tape.has(h - 1) && !tape.has(h - 2) &&
      tape.has(h - 3) && tape.has(h - 4))) return null;
  const run = rightRunLength(h + 1);
  if (run < 2 || run % 2 !== 0) return null;
  const n1 = run / 2;
  if (tape.has(h + 2 * n1 + 1) ||
      !tape.has(h + 2 * n1 + 2) ||
      tape.has(h + 2 * n1 + 3)) return null;
  let r = 0;
  while (!tape.has(h - 5 - 2 * r) &&
      tape.has(h - 6 - 2 * r)) r++;
  if (tape.has(h - 5 - 2 * r) ||
      tape.has(h - 6 - 2 * r)) return null;
  return {
    n1,
    r,
    returnTime: time + 8 * n1 + 2 * r + 30,
    returnHead: h - 2 * r - 6,
  };
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
    const prefix = prefixAtBZero(head, time);
    const cphase = cphaseD1AtBZero(head, time);
    const twoWave = twoWaveRootAtBZero(head, time);
    const twoWaveShield = twoWave === null ? null : noLeft1100(head);
    if (tape.has(head - 1) && !tape.has(head - 2) && tape.has(head - 3)) {
      const leftSix = Array.from({ length: 6 }, (_, i) =>
        tape.has(head - 6 + i) ? '1' : '0').join('');
      b0Left101Audit.count++;
      b0Left101Audit.leftSix[leftSix] = (b0Left101Audit.leftSix[leftSix] || 0) + 1;
      if (leftSix.startsWith('110')) {
        b0Left101Audit.boundaryUnsafe++;
        b0Left101Audit.unsafe.push({
          time,
          head,
          leftSix,
          prefix,
          rightWindow: Array.from({ length: 10 }, (_, i) =>
            tape.has(head + 1 + i) ? '1' : '0').join(''),
          rightTail: Array.from({ length: 6 }, (_, i) =>
            tape.has(head + prefix.m + i) ? '1' : '0').join(''),
        });
      }
    }
    const cphaseShield = cphase === null ? null : noLeft1100(head);
    const prefixShield = prefix === null || prefix.type === 'prefixUnmatched'
      ? null : noLeft1100(head);
    const oddEvenBoundarySafe = prefix?.type === 'oddEvenPrefix'
      ? !(tape.has(head - 6) && tape.has(head - 5) && !tape.has(head - 4))
      : null;
    const prefixLeftSix = Array.from({ length: 6 }, (_, i) =>
      tape.has(head - 6 + i) ? '1' : '0').join('');

    if (previousBZero !== null) {
      const expected = predictions.get(time);
      const validPrefix = previousBZero.prefix &&
        previousBZero.prefix.type !== 'prefixUnmatched';
      const validCphase = previousBZero.cphase !== null;
      const validTwoWave = previousBZero.twoWave !== null;
      assert(!(expected && (validPrefix || validCphase || validTwoWave)),
        'A wave prediction overlaps a macro return');
      assert(!(validPrefix && validCphase),
        'The even-wave and C-phase macro hypotheses overlap');
      assert(!(validTwoWave && (validPrefix || validCphase)),
        'The two-wave root and another macro hypothesis overlap');

      if (expected) {
        assert.equal(head, expected.head, 'Wave theorem endpoint disagrees with raw machine');
        counts[expected.type]++;
        predictions.delete(time);
      } else if (validPrefix) {
        assert.equal(time, previousBZero.prefix.returnTime,
          'Even-wave prefix return time disagrees with raw machine');
        assert.equal(head, previousBZero.prefix.returnHead,
          'Even-wave prefix return head disagrees with raw machine');
        counts[previousBZero.prefix.type]++;
        const audit = prefixShieldAudit[previousBZero.prefix.type];
        audit.inputs += Number(previousBZero.prefixShield);
        audit.outputs += Number(noLeft1100(head));
        if (previousBZero.prefix.type === 'oddEvenPrefix') {
          audit.boundarySafe += Number(previousBZero.oddEvenBoundarySafe);
        }
        const familyPatterns = prefixLeftSixAudit[previousBZero.prefix.type];
        familyPatterns[previousBZero.prefixLeftSix] =
          (familyPatterns[previousBZero.prefixLeftSix] || 0) + 1;
      } else if (validTwoWave) {
        assert(previousBZero.prefix &&
          previousBZero.prefix.type === 'prefixUnmatched',
          'Two-wave root candidate was not in the unmatched prefix class');
        assert.equal(time, previousBZero.twoWave.returnTime,
          'Two-wave root theorem return time disagrees with raw machine');
        assert.equal(head, previousBZero.twoWave.returnHead,
          'Two-wave root theorem return head disagrees with raw machine');
        assert.equal(previousBZero.twoWaveShield, true,
          'Two-wave root input does not satisfy the 1100 exclusion');
        assert.equal(noLeft1100(head), true,
          'Two-wave root return did not preserve the 1100 exclusion');
        counts.twoWaveRoot++;
        const key = previousBZero.twoWave.n1 + ',' + previousBZero.twoWave.r;
        twoWavePairs[key] = (twoWavePairs[key] || 0) + 1;
        twoWaveIntervals.push({
          startTime: previousBZero.time,
          startHead: previousBZero.head,
          n1: previousBZero.twoWave.n1,
          r: previousBZero.twoWave.r,
          returnTime: time,
          returnHead: head,
          steps: time - previousBZero.time,
          displacement: head - previousBZero.head,
          leftSix: previousBZero.prefixLeftSix,
        });
        assert.equal(time - previousBZero.time,
          8 * previousBZero.twoWave.n1 + 2 * previousBZero.twoWave.r + 30);
        assert.equal(head - previousBZero.head,
          -2 * previousBZero.twoWave.r - 6);
        twoWaveShieldAudit.inputs++;
        twoWaveShieldAudit.outputs++;
      } else if (previousBZero.prefix &&
          previousBZero.prefix.type === 'prefixUnmatched') {
        counts.prefixUnmatched++;
      } else if (validCphase) {
        assert.equal(previousBZero.cphaseShield, true,
          "C-phase D1 input does not satisfy the 1100 exclusion");
        cphaseShieldInputs++;
        assert.equal(noLeft1100(head), true,
          "C-phase D1 return did not preserve the 1100 exclusion");
        cphaseShieldOutputs++;
        assert.equal(time, previousBZero.cphase.returnTime,
          'C-phase D1 return time disagrees with raw machine');
        assert.equal(head, previousBZero.cphase.returnHead,
          'C-phase D1 return head disagrees with raw machine');
        counts.cphaseD1++;
        const r = previousBZero.cphase.r;
        cphaseRuns[r] = (cphaseRuns[r] || 0) + 1;
      } else {
        counts.other++;
      }
    }
    previousBZero = {
      time, head, prefix, cphase, twoWave, cphaseShield, prefixShield,
      twoWaveShield, oddEvenBoundarySafe, prefixLeftSix,
    };
  }

  const rule = RULES[state.charCodeAt(0) - 65].slice(symbol * 3, symbol * 3 + 3);
  assert.notEqual(rule, '---', 'Unexpected halt at step ' + time);
  if (rule[0] === '1') tape.add(head);
  else tape.delete(head);
  head += rule[1] === 'R' ? 1 : -1;
  state = rule[2];
}

assert.equal(bZeros, 22_984);
assert.deepEqual(counts, {
  oldWave: 7_508,
  leftOneWave: 177,
  evenPrefix: 21,
  oddEvenPrefix: 22,
  twoWaveRoot: 8,
  prefixUnmatched: 0,
  cphaseD1: 15_198,
  other: 49,
});
assert.deepEqual(cphaseRuns, { 2: 1, 3: 15_176, 4: 21 });
assert.equal(Object.values(counts).reduce((a, b) => a + b, 0), bZeros - 1);
assert.equal(cphaseShieldInputs, counts.cphaseD1);
assert.equal(cphaseShieldOutputs, counts.cphaseD1);
assert.deepEqual(Object.keys(twoWavePairs).sort(), [
  '176,73', '184,194', '32,109', '32,17', '32,2', '40,15', '40,46', '96,1',
]);
assert.deepEqual(twoWavePairs, {
  '176,73': 1, '184,194': 1, '32,109': 1, '32,17': 1,
  '32,2': 1, '40,15': 1, '40,46': 1, '96,1': 1,
});
assert.deepEqual(twoWaveShieldAudit, { inputs: 8, outputs: 8 });
assert.equal(predictions.size, 0, 'Unfinished wave predictions at cutoff');
console.log(JSON.stringify({
  rawSteps: LIMIT,
  bZeroSections: bZeros,
  firstReturnClasses: counts,
  cphaseD1RunLengths: cphaseRuns,
  cphaseD1ShieldAudit: { inputShielded: cphaseShieldInputs, outputShielded: cphaseShieldOutputs },
  prefixShieldAudit,
  prefixLeftSixAudit,
  twoWaveRootAudit: {
    pairs: twoWavePairs,
    intervals: twoWaveIntervals,
    shield: twoWaveShieldAudit,
  },
  b0Left101Audit,
}, null, 2));
