'use strict';

const assert = require('node:assert/strict');

const RLE = '1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD';
const ROWS = RLE.split('_');

/** @typedef {{q: string, head: number, tape: Set<number>}} Configuration */

/** @param {Configuration} config */
function step(config) {
  const stateIndex = config.q.charCodeAt(0) - 65;
  const scanned = Number(config.tape.has(config.head));
  const instruction = ROWS[stateIndex].slice(scanned * 3, scanned * 3 + 3);
  assert.notEqual(instruction, '---', `Unexpected halt at ${config.q}/${scanned}`);
  if (instruction[0] === '1') config.tape.add(config.head);
  else config.tape.delete(config.head);
  config.head += instruction[1] === 'R' ? 1 : -1;
  config.q = instruction[2];
}

/** @param {Configuration} config @param {number} count */
function advance(config, count) {
  for (let i = 0; i < count; i++) step(config);
}

/** @param {Set<number>} left @param {Set<number>} right */
function sameTape(left, right) {
  return left.size === right.size && [...left].every(p => right.has(p));
}

/** @param {number} seed */
function pseudoRandom(seed) {
  let s = seed >>> 0;
  return () => {
    s = (Math.imul(s, 1664525) + 1013904223) >>> 0;
    return s;
  };
}

let cases = 0;
for (let n = 0; n <= 12; n++) {
  for (let trial = 0; trial < 30; trial++) {
    const nextRandom = pseudoRandom(0x9a82e9 + n * 193 + trial);
    const initial = new Set();
    for (let x = -45; x <= 75; x++) if ((nextRandom() & 7) <= 2) initial.add(x);
    const origin = -5;
    initial.add(origin);
    initial.delete(origin - 1);
    for (let x = origin + 1; x <= origin + 2 * n + 1; x++) initial.add(x);
    const endpoint = origin + 2 * n + 2;
    initial.delete(endpoint);
    const config = { q: 'F', head: origin, tape: new Set(initial) };
    advance(config, 4 * n + 5);
    assert.equal(config.q, 'B');
    assert.equal(config.head, origin - 1);
    assert.equal(config.tape.has(config.head), false);
    const expected = new Set(initial);
    expected.add(endpoint);
    assert.ok(sameTape(config.tape, expected), `Full tape disagrees, n=${n}, trial=${trial}`);
    cases++;
  }
}
console.log(`Synthetic full-tape wave returns validated: ${cases} (n=0..12, 30 seeded exteriors each)`);

const actual = { q: 'A', head: 0, tape: new Set() };
advance(actual, 3194058);
assert.equal(actual.q, 'F');
assert.equal(actual.head, -692);
assert.ok(actual.tape.has(-692));
assert.ok(!actual.tape.has(-693));
const n = 202;
for (let x = -691; x <= -692 + 2 * n + 1; x++) assert.ok(actual.tape.has(x));
assert.ok(!actual.tape.has(-692 + 2 * n + 2));
const old = new Set(actual.tape);
advance(actual, 4 * n + 5);
assert.equal(actual.q, 'B');
assert.equal(actual.head, -693);
assert.ok(!actual.tape.has(-693));
old.add(-286);
assert.ok(sameTape(actual.tape, old));
console.log('Authentic blank-root witness: F/1 at raw time 3194058, head -692, n=202;');
console.log('after 813 exact raw steps B/0 at time 3194871, head -693, only tape change is -286: 0→1');
