#!/usr/bin/env node
"use strict";

// Reproduce the parity-shifted J(93,0,173) path for the original #429 table.
// Tape cells are stored sparsely; absent cells are blank (false). The left
// side of a Junc zipper is nearest-first.

const assert = require("node:assert/strict");

const T = [
  [[1,  1, 1], [0, -1, 5]], // A: 1RB / 0LF
  [[1,  1, 2], [1,  1, 0]], // B: 1RC / 1RA
  [[0,  1, 3], [0,  1, 1]], // C: 0RD / 0RB
  [[1, -1, 4], null],       // D: 1LE / halt
  [[0, -1, 0], [1, -1, 4]], // E: 0LA / 1LE
  [[1,  1, 3], [1, -1, 0]], // F: 1RD / 1LA
];

const read = (tape, x) => tape.get(x) || 0;
const write = (tape, x, b) => b ? tape.set(x, 1) : tape.delete(x);

function makeJunc(u, v, w) {
  const tape = new Map();
  const left = [1];
  for (let i = 0; i < u; i++) left.push(0, 1);
  left.push(...Array(5).fill(1));
  const right = [1];
  for (let i = 0; i < v; i++) right.push(0, 1);
  right.push(...Array(w).fill(1), 0, 1);
  left.forEach((b, i) => { if (b) tape.set(-1 - i, 1); });
  right.forEach((b, i) => { if (b) tape.set(1 + i, 1); });
  tape.set(0, 1);
  return { state: 0, head: 0, tape };
}

// Recognize an exact Junc(u,v,w) tape, including blank margins.
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

function simulate(initial, steps, { watch = [], recordJuncFrom = 0 } = {}) {
  const tape = new Map(initial.tape);
  let { state, head } = initial;
  let minHead = head;
  let maxHead = head;
  const trace = [];
  const visits = [];
  const juncs = [];
  let c0 = null;
  let c0Tape = null;

  for (let t = 0; t <= steps; t++) {
    minHead = Math.min(minHead, head);
    maxHead = Math.max(maxHead, head);
    trace.push([state, head]);

    if (watch.includes(head)) {
      visits.push({ t, head, state, bit: read(tape, head) });
    }
    if (t === 31154) {
      const minCell = Math.min(...tape.keys());
      const leftWord = Array.from(
        { length: head - minCell },
        (_, i) => read(tape, head - 1 - i)
      );
      c0Tape = new Map(tape);
      c0 = {
        t, state, head, current: read(tape, head),
        right: read(tape, head + 1), minHead, maxHead,
        leftWord, tapeSize: tape.size,
      };
    }
    if (t >= recordJuncFrom && state === 0 && read(tape, head) === 1) {
      const j = parseJunc(state, head, tape);
      if (j) juncs.push({ t, head, ...j });
    }
    if (t === steps) break;

    const tr = T[state][read(tape, head)];
    if (tr === null) throw new Error(`halt at step ${t}, state ${state}, head ${head}`);
    const [bit, move, nextState] = tr;
    write(tape, head, bit);
    head += move;
    state = nextState;
  }
  return { state, head, tape, minHead, maxHead, trace, visits, juncs, c0, c0Tape };
}

const shifted = simulate(makeJunc(93, 0, 173), 134235, {
  watch: [-188, -193, -194],
  recordJuncFrom: 31154,
});
const standard = simulate(makeJunc(94, 0, 173), 31154, {
  watch: [-188, -193, -194],
});

// The two inputs differ only in the three far-left cells, and the first
// 31,154 primitive transitions never visit any of them.
assert.deepEqual(shifted.trace.slice(0, 31155), standard.trace);
assert.deepEqual(
  [...shifted.c0Tape.keys()].filter(x => !standard.tape.has(x)).sort((a,b)=>a-b),
  [-188]
);
assert.deepEqual(
  [...standard.tape.keys()].filter(x => !shifted.c0Tape.has(x)).sort((a,b)=>a-b),
  [-194, -193]
);
assert.deepEqual(shifted.c0 && {
  t: shifted.c0.t, state: shifted.c0.state, head: shifted.c0.head,
  current: shifted.c0.current, right: shifted.c0.right,
  minHead: shifted.c0.minHead, maxHead: shifted.c0.maxHead,
}, {
  t: 31154, state: 2, head: 178, current: 0, right: 0,
  minHead: -176, maxHead: 178,
});

const expectedAltLeft = [
  1, 0,
  ...Array(353).fill(1),
  0, 1, 0, 1, 0, 1, 0, 1,
  0,
  ...Array(6).fill(1),
];
assert.deepEqual(shifted.c0.leftWord, expectedAltLeft);
assert.equal(shifted.visits.find(x => x.head === -188)?.t, 31528);
assert.equal(shifted.visits.find(x => x.head === -188)?.bit, 1);

const expected = [
  [31579, 0,   7, 349],
  [31620, 10,  0, 346],
  [32147, 23,  0, 323],
  [34520, 49,  0, 274],
  [44641, 101, 0, 173],
  [74741, 15, 172, 1],
  [76292, 0,  15, 349],
  [76349, 18,  0, 346],
  [77852, 39,  0, 307],
  [84353, 81,  0, 226],
  [111434,165, 0, 61],
  [115214,135,60, 1],
  [116949,0, 135,125],
  [117246,138, 0, 122],
  [132006,78,120, 2],
  [134235,0,  0, 408],
];
assert.deepEqual(
  shifted.juncs.map(({t,u,v,w}) => [t,u,v,w]),
  expected
);
assert.deepEqual(
  { state: shifted.state, head: shifted.head, final: parseJunc(shifted.state, shifted.head, shifted.tape) },
  { state: 0, head: -219, final: {u:0,v:0,w:408} }
);

const durations = expected.slice(1).map((row, i) => row[0] - expected[i][0]);
assert.deepEqual(durations, [
  41, 527, 2373, 10121, 30100, 1551, 57, 1503,
  6501, 27081, 3780, 1735, 297, 14760, 2229,
]);
const afterJunc07 = durations.reduce((a,b)=>a+b,0);
assert.equal(afterJunc07, 102656);
assert.equal(425 + afterJunc07, 103081);
assert.equal(31154 + 103081, 134235);

console.log(JSON.stringify({
  start: "J(93,0,173)",
  c0: {
    step: shifted.c0.t, head: shifted.c0.head,
    headRange: [shifted.c0.minHead, shifted.c0.maxHead],
    leftWordLength: shifted.c0.leftWord.length,
  },
  firstDivergenceCell: shifted.visits.find(x => x.head === -188),
  juncCheckpoints: shifted.juncs,
  durationsAfterJunc07: durations,
  afterJunc07,
  c0Continuation: 103081,
  totalFromJunc93: 134235,
  endpoint: { state: shifted.state, head: shifted.head, junc: {u:0,v:0,w:408} },
}, null, 2));
