#!/usr/bin/env node
"use strict";

// Empirical grid test for the even-u, w=1 MidA boundary conjecture.
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

function midApos(u, v) {
  const left = [1, ...ones(2 * (v + 2)), ...pairs01(u), ...ones(5)];
  const right = [0, 1]; // ones(w-1) ++ [false,true], with w=1
  const tape = new Map();
  left.forEach((b, i) => { if (b) tape.set(-1 - i, 1); });
  right.forEach((b, i) => { if (b) tape.set(1 + i, 1); });
  tape.set(0, 1);
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

function firstJunc0(u, v) {
  const c = midApos(u, v);
  const tape = new Map(c.tape);
  let { state, head } = c;
  const expectedTime = 9 * u + 6 * v + 43;
  for (let t = 0; t <= expectedTime; t++) {
    const j = parseJunc(state, head, tape);
    if (j && j.u === 0) return { t, delta: head, j };
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
for (let u = 2; u <= 20; u += 2) {
  for (let v = 1; v <= 20; v++) {
    const out = firstJunc0(u, v);
    assert.deepEqual(out, {
      t: 9 * u + 6 * v + 43,
      delta: -(2 * u + 2 * v + 5),
      j: { u: 0, v: u + 1, w: 2 * v + 5 },
    }, `failed at u=${u}, v=${v}`);
    tested++;
  }
}

const rootCases = [
  { u: 14, v: 172, time: 1201, delta: -377, out: { u: 0, v: 15, w: 349 } },
  { u: 134, v: 60, time: 1609, delta: -393, out: { u: 0, v: 135, w: 125 } },
];
for (const c of rootCases) {
  assert.deepEqual(firstJunc0(c.u, c.v), {
    t: c.time, delta: c.delta, j: c.out,
  });
}

console.log(JSON.stringify({
  conjecture: "midApos(u,v,1) -> J(0,u+1,2v+5)",
  time: "9*u + 6*v + 43",
  displacement: "-(2*u + 2*v + 5)",
  testedEvenU: tested,
  range: { u: "2,4,...,20", v: "1,...,20" },
  rootCases,
  failures: 0,
}, null, 2));
