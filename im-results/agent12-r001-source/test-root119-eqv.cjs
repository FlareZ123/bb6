'use strict';

const assert = require('node:assert/strict');

/** @typedef {{write: number, direction: string, next: string} | null} Rule */
/** @typedef {{state: string, head: number, ones: Set<number>, completed: number}} Config */

const original = '1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD';
const removed119 = '1RB1LB_1RC---_1LD1LF_1LE0LD_0LA1RF_1LC0RE';
const permutation = 'BCDEAF';

/** @param {string} code @returns {Rule[][]} */
function parse(code) {
  const parts = code.split('_');
  assert.equal(parts.length, 6);
  return parts.map((pair) => {
    assert.equal(pair.length, 6);
    return [pair.slice(0, 3), pair.slice(3)].map((token) => {
      if (token === '---') return null;
      assert.match(token, /^[01][LR][A-F]$/);
      return {write: Number(token[0]), direction: token[1], next: token[2]};
    });
  });
}

/** @param {string} state @returns {string} */
function rename(state) { return permutation[state.charCodeAt(0) - 65]; }

/** @param {Rule[][]} table @param {number} steps @param {string} label @returns {Config} */
function simulate(table, steps, label) {
  let state = 'A';
  let head = 0;
  const ones = new Set();
  for (let n = 0; n < steps; n++) {
    const bit = Number(ones.has(head));
    const rule = table[state.charCodeAt(0) - 65][bit];
    assert.notEqual(rule, null, `${label} unexpectedly halted at raw step ${n}`);
    if (rule.write === 1) ones.add(head);
    else ones.delete(head);
    head += rule.direction === 'R' ? 1 : -1;
    state = rule.next;
  }
  return {state, head, ones, completed: steps};
}

/** @param {Config} config @returns {number[]} */
function relativeOnes(config) {
  return [...config.ones].map((index) => index - config.head).sort((a, b) => a - b);
}

/** @param {Rule[][]} tableA @param {Rule[][]} tableB */
function verifyExactRenaming(tableA, tableB) {
  for (let q = 0; q < 6; q++) {
    for (let bit = 0; bit < 2; bit++) {
      const lhs = tableA[q][bit];
      const rhs = tableB[rename(String.fromCharCode(65 + q)).charCodeAt(0) - 65][bit];
      assert.deepEqual(lhs && {...lhs, next: rename(lhs.next)}, rhs,
        `transition mismatch for state ${String.fromCharCode(65 + q)} / ${bit}`);
    }
  }
  console.log('PASS: exact 12/12 transition entries match under permutation', permutation);
}

const first = parse(original);
const second = parse(removed119);
verifyExactRenaming(first, second);
const x = simulate(first, 315075, 'auxiliary root');
const y = simulate(second, 337226, 'removed root 119');
assert.equal(rename(x.state), y.state);
assert.deepEqual(relativeOnes(x), relativeOnes(y));
const footprint = relativeOnes(x);
console.log('PASS: both full configurations merge modulo state permutation and tape translation');
console.log('Auxiliary:', {rawSteps: x.completed, state: x.state, head: x.head, setBits: x.ones.size});
console.log('Root 119:', {rawSteps: y.completed, state: y.state, head: y.head, setBits: y.ones.size});
console.log('Common relative ones:', {count: footprint.length, min: footprint.at(0), max: footprint.at(-1)});
console.log('PASS: neither blank-root run halted during its checked prefix');
console.log('Result: computationally verified finite-prefix coalescence; infinite behavior remains unclassified');
