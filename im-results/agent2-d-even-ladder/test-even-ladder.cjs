'use strict';

/**
 * A single-file, dependency-free primitive-step test of the all-even-depth
 * D-cryptid embedding. Run with Node.js on Windows 11.
 *
 * Every visit to F scanning zero is checked against the WHOLE left tape,
 * including cells to the left of the original head. This avoids the known
 * false-return bug in earlier experimental drivers.
 */
const assert = require('node:assert/strict');

// Transition index = 2 * state + scanned bit. States A...F = 0...5.
// F scanning one is the unique missing rule and enters the frozen halt state.
const WRITE = Uint8Array.from([1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1]);
const MOVE = Int8Array.from([1, 1, -1, 1, -1, -1, -1, -1, -1, -1, -1]);
const NEXT = Uint8Array.from([1, 4, 2, 0, 0, 3, 2, 5, 2, 1, 4]);

/** @typedef {{time: number, head: number, unary: number, suffix: string}} ReturnRecord */

/**
 * Primitive simulation of I_(3k+4)((01)^q1).
 * @param {number} k Nonnegative E-entry index.
 * @param {number} q Positive alternating-pair count.
 * @param {number} wanted Number of genuine physical returns to record.
 * @param {number} limit Primitive-step limit.
 * @returns {ReturnRecord[]}
 */
function rawReturns(k, q, wanted, limit) {
  const tape = new Uint8Array(1 << 20);
  const origin = tape.length >>> 1;
  const unary = 3 * k + 4;
  let rightMost = origin + unary + 2 * q + 1;
  for (let j = 1; j <= unary; j++) tape[origin + j] = 1;
  for (let j = 0; j < q; j++) tape[origin + unary + 2 * j + 2] = 1;
  tape[rightMost] = 1;

  let head = origin;
  let state = 5;
  let leftOnes = 0;
  const returns = [];

  for (let time = 0; time < limit; time++) {
    const bit = tape[head];
    if (time > 0 && state === 5 && bit === 0 && leftOnes === 0) {
      const right = [];
      for (let j = head + 1; j <= rightMost; j++) right.push(tape[j]);
      while (right.length && right[right.length - 1] === 0) right.pop();
      let n = 0;
      while (n < right.length && right[n] === 1) n++;
      const record = {
        time,
        head: head - origin,
        unary: n,
        suffix: right.slice(n).join('')
      };
      returns.push(record);
      console.log(
        '  return=' + returns.length +
        ' time=' + time +
        ' head=' + record.head +
        ' unary=' + n +
        ' suffix=' + record.suffix
      );
      if (returns.length === wanted) return returns;
    }

    const rule = 2 * state + bit;
    assert.notEqual(rule, 11, 'Unexpected halt at primitive step ' + time);
    tape[head] = WRITE[rule];
    if (tape[head] === 1 && head > rightMost) rightMost = head;

    if (MOVE[rule] > 0) {
      leftOnes += tape[head];
      head++;
    } else {
      head--;
      leftOnes -= tape[head];
    }
    state = NEXT[rule];
    assert.ok(head > 0 && head < tape.length - 1, 'Tape window exceeded');
    assert.ok(leftOnes >= 0, 'Physical left-one count became negative');
  }
  assert.fail('Exceeded primitive limit ' + limit);
}

/**
 * Base-3 digit lifting gives the least nonnegative v for
 * 4096*v + 1161 divisible by 3^(m+1).
 * @param {number} m Even depth.
 * @returns {{m:number, q:number, v:bigint, k:bigint, U:bigint, N:bigint}}
 */
function evenParameters(m) {
  assert.ok(Number.isSafeInteger(m) && m >= 0 && m % 2 === 0);
  let v = 0n;
  let power = 1n;
  for (let j = 0; j <= m; j++) {
    const numerator = 4096n * v + 1161n;
    assert.equal(numerator % power, 0n);
    const quotient = numerator / power;
    const digit = (3n - quotient % 3n) % 3n;
    v += digit * power;
    power *= 3n;
    assert.equal((4096n * v + 1161n) % power, 0n);
  }
  const N = 4096n * v + 1162n;
  const U = (N - 1n) / power;
  const q = (3 * m + 6) / 2;
  assert.ok(v >= 0n && v < power && U >= 1n);
  assert.equal(N, power * U + 1n);
  assert.equal(2 * q - 3, 3 * m + 3);
  return { m, q, v, k: 27n * v + 7n, U, N };
}

function verifyRawCases() {
  const p = (n) => '01'.repeat(n);
  for (const fixture of [
    { q: 3, times: [999, 6320, 42665, 298593], unary: [61, 161, 434, 1162] },
    { q: 6, times: [1011, 6332, 42677, 298605, 2105529, 14911650],
      unary: [61, 161, 434, 1162, 3097, 8257] }
  ]) {
    const q = fixture.q;
    console.log('Raw run: X(7,' + q + '), ' + fixture.times.length + ' returns');
    const records = rawReturns(7, q, fixture.times.length, 16000000);
    const suffixes = [
      '0' + '1'.repeat(2 * q) + '0' + '1'.repeat(6),
      p(2) + '0' + '1'.repeat(2 * q - 3) + '0' + '1'.repeat(6),
      '010' + '1'.repeat(2 * q - 3) + '0' + '1'.repeat(6),
      '0' + '1'.repeat(2 * q - 3) + '0' + '1'.repeat(6)
    ];
    if (q === 6) suffixes.push(
      p(2) + '0' + '1'.repeat(6) + '0' + '1'.repeat(6),
      p(4) + '0' + '1'.repeat(3) + '0' + '1'.repeat(6)
    );
    assert.deepEqual(records.map(r => r.time), fixture.times);
    assert.deepEqual(records.map(r => r.unary), fixture.unary);
    assert.deepEqual(records.map(r => r.suffix), suffixes);
    console.log('  EXACT PHYSICAL RETURN TIMES AND TAPES: PASS');
  }

  const m = 2n, U = 43n;
  const exactCost = 108n * U * U * ((64n ** m - 9n ** m) / 55n) +
    15n * U * (8n ** m - 3n ** m) + 6n * m * m + 15n * m;
  assert.equal(exactCost, 14911650n - 298605n);
  assert.equal(3n * 8n ** m * U + 1n, 8257n);
  console.log('Exact two-stage primitive cost=' + exactCost + ': PASS');
}

function main() {
  console.log('D cryptid even-depth source-parameter / raw-TM SFT');
  const start = Date.now();
  for (let m = 0; m <= 40; m += 2) {
    const row = evenParameters(m);
    if (m <= 8) console.log(
      'depth=' + m + ' q=' + row.q +
      ' v=' + row.v + ' k=' + row.k +
      ' N=' + row.N + ' U=' + row.U
    );
  }
  console.log('21 CONSTRUCTIVE MODULAR PARAMETER CASES: PASS');
  verifyRawCases();
  console.log('ALL CHECKS PASSED in ' + (Date.now() - start) + ' ms');
}

main();
