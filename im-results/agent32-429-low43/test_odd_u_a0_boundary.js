#!/usr/bin/env node
"use strict";

// Empirical grid test for the odd-u A/0 boundary conjecture.
// Original #429 table; no external dependencies.

const assert = require("node:assert/strict");

const T = [
  [[1,  1, 1], [0, -1, 5]],
  [[1,  1, 2], [1,  1, 0]],
  [[0,  1, 3], [0,  1, 1]],
  [[1, -1, 4], null],
  [[0, -1, 0], [1, -1, 4]],
  [[1,  1, 3], [1, -1, 0]],
];

const ones = n => Array(n).fill(1);
const pairs01 = n => Array.from({ length: n }, () => [0, 1]).flat();
const read = (tape, x) => tape.get(x) || 0;
const write = (tape, x, b) => b ? tape.set(x, 1) : tape.delete(x);

function A0(u, v) {
  const left = [...ones(2 * v + 9), ...pairs01(u - 1), ...ones(5)];
  const tape = new Map();
  left.forEach((b, i) => { if (b) tape.set(-1 - i, 1); });
  tape.set(1, 1); // right tape [true]
  return { state: 0, head: 0, tape };
}

function parseJunc(state, head, tape) {
  if (state !== 0 || read(tape, head) !== 1) return null;
  let p = head - 1;
  if (read(tape, p) !== 1) return null;
  p--;
  let u = 0;
  while (read(tape, p) === 0 && read(tape, p - 1) === 1) {
    u++;
    p -= 2;
  }
  for (let i = 0; i < 5; i++) if (read(tape, p - i) !== 1) return null;
  const leftMin = p - 4;
  for (const x of tape.keys()) if (x < leftMin) return null;

  let q = head + 1;
  if (read(tape, q) !== 1) return null;
  q++;
  let v = 0;
  while (read(tape, q) === 0 && read(tape, q + 1) === 1) {
    v++;
    q += 2;
  }
  let w = 0;
  while (read(tape, q) === 1) {
    w++;
    q++;
  }
  if (read(tape, q) !== 0 || read(tape, q + 1) !== 1) return null;
  for (const x of tape.keys()) if (x > q + 1) return null;
  return { u, v, w };
}

function firstJunc00(u, v) {
  const c = A0(u, v);
  const tape = new Map(c.tape);
  let { state, head } = c;
  const expectedTime = 9 * u + 6 * v + 76;
  for (let t = 0; t <= expectedTime; t++) {
    const j = parseJunc(state, head, tape);
    if (j && j.u === 0 && j.v === 0) return { t, delta: head, j };
    if (t === expectedTime) break;
    const tr = T[state][read(tape, head)];
    if (tr === null) throw new Error(`halt at t=${t}, u=${u}, v=${v}`);
    const [bit, move, nextState] = tr;
    write(tape, head, bit);
    head += move;
    state = nextState;
  }
  return null;
}

let tested = 0;
for (let u = 1; u <= 21; u += 2) {
  for (let v = 1; v <= 20; v++) {
    assert.deepEqual(firstJunc00(u, v), {
      t: 9 * u + 6 * v + 76,
      delta: -(2 * u + 2 * v + 9),
      j: { u: 0, v: 0, w: 2 * u + 2 * v + 14 },
    }, `failed at u=${u}, v=${v}`);
    tested++;
  }
}

const root = firstJunc00(77, 120);
assert.deepEqual(root, {
  t: 1489, delta: -403, j: { u: 0, v: 0, w: 408 },
});

console.log(JSON.stringify({
  conjecture: "A0(u,v) -> J(0,0,2*u+2*v+14)",
  time: "9*u + 6*v + 76",
  displacement: "-(2*u + 2*v + 9)",
  testedOddU: tested,
  range: { u: "1,3,...,21", v: "1,...,20" },
  rootInstance: { u: 77, v: 120, ...root },
  failures: 0,
}, null, 2));
