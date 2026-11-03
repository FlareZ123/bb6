/**
 * Original-source TM63 first checkpoint audit. Rebuilds the physical tape from
 * BusyCoq's BinDec and directed-tape notation, then checks ordinary steps.
 * Pinned source: ccz181078/busycoq@3f302b87 verify/SOBCv5.v and
 * verify/BinaryCounter.v; no data files or network access are used.
 * @type {string}
 */
'use strict';

const assert = require('node:assert/strict');
const source = '1RB---_1LC0RF_1RE0LD_0LC1RB_1RA1RE_1RE0RD';

/** @typedef {{ write: number, delta: number, next: number } | null} Move */
/** @type {Move[][]} */
const table = source.split('_').map((row) => [0, 1].map((read) => {
  const raw = row.slice(read * 3, read * 3 + 3);
  return raw === '---'
    ? null
    : { write: Number(raw[0]), delta: raw[1] === 'R' ? 1 : -1,
      next: raw.charCodeAt(2) - 'A'.charCodeAt(0) };
}));

/**
 * BusyCoq BinaryCounter(d0,d1,tail,x) prepends low-order bit blocks until
 * reaching the leading binary digit; BinDec uses x=2^(len+1)-1-n.
 * @param {number[]} d0
 * @param {number[]} d1
 * @param {number} len
 * @param {number} n
 * @param {number[]} tail
 * @returns {number[]}
 */
function binDec(d0, d1, len, n, tail) {
  let value = (1n << BigInt(len + 1)) - 1n - BigInt(n);
  assert(value >= 1n);
  const parts = [];
  while (value > 1n) {
    parts.push(...((value & 1n) === 1n ? d1 : d0));
    value >>= 1n;
  }
  return [...parts, ...tail];
}

const d0 = [0, 0, 1]; // Coq <[1;0;0]
const d1 = [1, 1, 1]; // Coq <[1;1;1]
const lh = [1, 1, 0, 1, 1, 1]; // Coq 0inf <* <[1;1;1;0;1;1]
const m2 = [1, 1, 0, 1]; // Coq <[1;0;1;1]
const left = binDec(d0, d1, 6, 0,
  [...m2, ...d0, ...binDec(d0, d1, 3, 7, lh)]);
const right = [0, 1, 1, 1, 0, 0, ...Array(3 * (1 + 63)).fill(1)];

// Primitive-state A=0 ... F=5, blank tape, ordinary successful moves.
const ones = new Set();
let state = 0;
let head = 0;
const steps = 27959;
for (let step = 0; step < steps; step++) {
  const instruction = table[state][ones.has(head) ? 1 : 0];
  assert(instruction !== null, 'unexpected early halt at step ' + step);
  if (instruction.write === 1) ones.add(head);
  else ones.delete(head);
  head += instruction.delta;
  state = instruction.next;
}

assert.equal(state, 3, 'S1 should use the left-directed D state');
assert.equal(head, 29, 'the first genuine S1 checkpoint head coordinate');
assert.equal(ones.size, 225);
assert.equal(ones.has(head), true, 'the D-head cell belongs to the left stack');
assert.equal(left.length, 40);
assert.equal(right.length, 198);

const expected = new Set();
left.forEach((bit, i) => { if (bit === 1) expected.add(head - i); });
right.forEach((bit, i) => { if (bit === 1) expected.add(head + i + 1); });
assert.deepEqual([...ones].sort((a, b) => a - b),
  [...expected].sort((a, b) => a - b),
  'every marked cell must agree, including the infinite zero tails');

console.log(JSON.stringify({
  source,
  originalSourceCheckpoint: 'TM63.S1 3 7 m2 6 0 63',
  successfulPrimitiveMoves: steps,
  state: 'D',
  head,
  markedCells: ones.size,
  leftPrefixCells: left.length,
  rightPrefixCells: right.length,
  repeatedRightOnes: 3 * 64,
  completeBiInfiniteTapeMatch: true,
  proofStatus: 'deterministic finite simulation, not a kernel proof'
}, null, 2));
