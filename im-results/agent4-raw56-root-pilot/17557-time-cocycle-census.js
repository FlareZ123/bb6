#!/usr/bin/env node
'use strict';

/*
 * Raw56 E1=0LE leaf 17557: literal six-state blank-tape simulation.
 *
 * Counts A/B triads, the length of the third right one-run at each A triad,
 * and whether the scanned final one-run is terminal. Verifies each complete
 * triad's exact primitive-step cost against the original sweep formulas.
 *
 * This is finite computational evidence only, NOT an infinite-time proof.
 * The time-cocycle arithmetic is in Raw56LE17557TimeCocycle.lean.
 *
 * Usage: node 17557-time-cocycle-census.js [MAX_N=9], 3 <= MAX_N <= 10.
 * With MAX_N=9, checks epochs n=2..8 (1,097,479 primitive steps).
 */
const MAX_N = Number(process.argv[2] || 9);
if (!Number.isInteger(MAX_N) || MAX_N < 3 || MAX_N > 10) {
  throw Error('MAX_N must be an integer between 3 and 10');
}
const T = n => 4 * 4 ** n + 8 * 3 ** (n - 1) - 7 * 2 ** n - 1;

// Six-state table 1RB1LA_1RC1RB_0RD0RC_1LD1LE_1LF0LE_0LA---.
// Each row is indexed by read bit: [written bit, movement ±1, next state].
// The only undefined rule is F1, which must never be encountered.
const table = [
  [[1, 1, 1], [1, -1, 0]],
  [[1, 1, 2], [1, 1, 1]],
  [[0, 1, 3], [0, 1, 2]],
  [[1, -1, 3], [1, -1, 4]],
  [[1, -1, 5], [0, -1, 4]],
  [[0, -1, 0], null],
];
const tape = new Set();
let head = 0, state = 0, firstD = null, triadD = [], boundaryIndex = 0,
    previous = null;
const epochs = Object.fromEntries(
  Array.from({length: MAX_N - 2}, (_, i) =>
    [i + 2, {A: 0, B: 0, cSum: 0, finalA: 0,
             finalB: 0, cost: 0, word: ''}])
);

function rightOneRuns(pos) {
  let max = pos;
  for (const x of tape) max = Math.max(max, x);
  const out = [];
  for (let i = pos + 1; i <= max;) {
    while (i <= max && !tape.has(i)) ++i;
    let len = 0;
    while (i <= max && tape.has(i)) { ++len; ++i; }
    if (len) out.push(len);
  }
  return out;
}
function leftOnes(pos) {
  let len = 0;
  while (tape.has(pos - 1 - len)) ++len;
  return len;
}
function completeTriad(time) {
  if (!previous) return;
  if (triadD.length !== 3) throw Error('Not 3 first-D reads at ' + time);
  const label = triadD.join('') === '101' ? 'A'
    : triadD.join('') === '001' ? 'B' : '?';
  if (label === '?') throw Error('Unknown triad at ' + previous.t);
  const e = epochs[previous.epoch];
  if (!e) return;
  const [a, b, c] = previous.runs;
  const elapsed = time - previous.t;
  let expected;
  if (label === 'A') {
    if (!(c >= 1)) throw Error('A triad needs third right one-run');
    expected = b >= 6 ? a + b + 2 * c + 26
      : b === 5 ? 2 * a + 2 * c + previous.d + 33 : NaN;
    e.cSum += c;
    if (previous.runs.length === 3) e.finalA++;
  } else {
    if (!(a >= 2 && b >= 1)) throw Error('Bad B right runs');
    expected = 2 * a + 2 * b + 29;
    if (previous.runs.length === 2) e.finalB++;
  }
  if (elapsed !== expected) {
    throw Error('Source triad cost mismatch at ' + previous.t +
      ': label=' + label + ' observed=' + elapsed + ' expected=' + expected +
      ' runs=' + JSON.stringify(previous.runs) + ' left ones=' + previous.d);
  }
  e[label]++;
  e.cost += elapsed;
  e.word += label;
}
for (let time = 0; time <= T(MAX_N); time++) {
  if (state === 0 && !tape.has(head) && time >= T(2)) {
    if (boundaryIndex % 3 === 0) {
      completeTriad(time);
      triadD = [];
      let epoch = 2;
      while (epoch + 1 <= MAX_N && time >= T(epoch + 1)) epoch++;
      previous = {t: time, epoch, runs: rightOneRuns(head), d: leftOnes(head)};
    }
    boundaryIndex++;
    firstD = null;
  }
  if (time === T(MAX_N)) break;
  const read = tape.has(head) ? 1 : 0;
  if (state === 3 && firstD === null && time >= T(2)) {
    firstD = read;
    triadD.push(read);
  }
  const rule = table[state][read];
  if (!rule) throw Error('Undefined F1 reached at primitive step ' + time);
  const [write, direction, next] = rule;
  if (write) tape.add(head); else tape.delete(head);
  head += direction; state = next;
}
const sigma = word => [...word].map(x => x === 'A' ? 'ABA' : 'BBA').join('');
let previousWord;
for (let n = 2; n < MAX_N; n++) {
  const e = epochs[n], p3 = 3 ** (n - 2), p2 = 2 ** (n - 2);
  const expectedC = 3 * 4 ** n - 32 * p3 - p2;
  const expectedCount = 2 * p3;
  if (e.A !== expectedCount || e.B !== expectedCount ||
      e.finalA !== p2 || e.finalB !== p2 || e.cSum !== expectedC ||
      e.cost !== T(n + 1) - T(n)) {
    throw Error('Failed epoch identity n=' + n + ': ' + JSON.stringify(e));
  }
  if (previousWord === undefined) {
    if (e.word !== 'ABBA') throw Error('Bad W_2');
  } else if (e.word !== sigma(previousWord)) {
    throw Error('Substitution mismatch at W_' + n);
  }
  previousWord = e.word;
  console.log(JSON.stringify({
    n, A: e.A, B: e.B, finalA: e.finalA, finalB: e.finalB,
    thirdOneRunSumA: e.cSum, primitiveSteps: e.cost, triadCount: e.word.length
  }));
}
if (state !== 0 || tape.has(head)) throw Error('Last checkpoint is not A0');
console.log('PASS finite primitive trace through C_' + MAX_N +
  ', t=' + T(MAX_N) + ', all triad costs and cocycle observables matched');
