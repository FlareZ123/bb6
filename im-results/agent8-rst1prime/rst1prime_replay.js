#!/usr/bin/env node
"use strict";

// Exact finite-support replay of the original TM63 table and the ten
// Rst1' phases.  This is computational evidence, not a universal proof.
// Usage: node rst1prime_replay.js [maxParameter], default 8.

function binDec(len, n) {
  let p = (2n ** BigInt(len + 1)) - 1n - BigInt(n);
  const out = [];
  for (let k = len; k > 0; --k) {
    if (p <= 1n) break;
    if (p % 2n === 0n) {
      out.push(0, 0, 1); // d0
      p /= 2n;
    } else {
      out.push(1, 1, 1); // d1
      p = (p - 1n) / 2n;
    }
  }
  return out;
}

function markerWord(m) {
  return m % 3 === 0 ? [0, 1] : m % 3 === 1 ? [1, 0, 1] : [1, 1, 0, 1];
}

function s1Config(L, n, m, a, z, b, head = 0) {
  const left = [
    ...binDec(a, z), ...markerWord(m), 0, 0, 1,
    ...binDec(L, n), 1, 1, 0, 1, 1, 1
  ];
  const right = [0, 1, 1, 1, 0, 0, ...Array(3 * (b + 1)).fill(1)];
  const tape = new Set();
  left.forEach((bit, i) => { if (bit) tape.add(head - i); });
  right.forEach((bit, i) => { if (bit) tape.add(head + 1 + i); });
  return { state: 3, head, tape };
}

// Each transition is [writeOne, moveRight, nextState]; null means halt.
const TM63 = [
  [[1, 1, 1], null],
  [[1, 0, 2], [0, 1, 5]],
  [[1, 1, 4], [0, 0, 3]],
  [[0, 0, 2], [1, 1, 1]],
  [[1, 1, 0], [1, 1, 4]],
  [[1, 1, 4], [0, 1, 3]]
];

function run(config, steps) {
  let state = config.state;
  let head = config.head;
  const tape = new Set(config.tape);
  for (let k = 0; k < steps; ++k) {
    const transition = TM63[state][tape.has(head) ? 1 : 0];
    if (transition === null) return null;
    const [writeOne, moveRight, nextState] = transition;
    if (writeOne) tape.add(head);
    else tape.delete(head);
    state = nextState;
    head += moveRight ? 1 : -1;
  }
  return { state, head, tape };
}

function requireCheck(condition, message) {
  if (!condition) throw new Error(message);
}

function matchesWindow(tape, head, lo, hi, markedOffsets) {
  const expected = new Set(markedOffsets.map(x => head + x));
  for (let x = lo; x <= hi; ++x) {
    if (tape.has(head + x) !== expected.has(head + x)) return false;
  }
  return true;
}

function leftSweepInput(tape, head, n) {
  if (tape.has(head + 1)) return false;
  for (let i = 0; i < n; ++i) if (!tape.has(head - i)) return false;
  return true;
}

function rightSweepInput(tape, head, n) {
  for (let i = 0; i < n; ++i)
    for (let j = 0; j < 3; ++j)
      if (!tape.has(head + 3 * i + j)) return false;
  return true;
}

function sameTape(a, b) {
  return a.size === b.size && [...a].every(x => b.has(x));
}

function checkOne(L, a, b) {
  const fail = phase => { throw new Error(`phase ${phase}, L=${L}, a=${a}, b=${b}`); };
  let c = s1Config(L, 0, 1, a, 0, b);
  if (!leftSweepInput(c.tape, 0, 3 * a + 1)) fail("1-input");

  // 1. Sweep the leading d1^a and first marker bit.
  c = run(c, 3 * (3 * a + 1));
  const hN = -(3 * a + 1);
  if (!c || c.state !== 3 || c.head !== hN ||
      !matchesWindow(c.tape, hN, -3, 0, [-1])) fail("1-output");

  // 2. Fixed 8-step bridge, then sweep d0 + d1^L + first two lh bits.
  c = run(c, 8);
  const h1 = hN - 2;
  if (!c || c.state !== 3 || c.head !== h1 ||
      !matchesWindow(c.tape, hN, -3, 0, [0, -2, -3]) ||
      !leftSweepInput(c.tape, h1, 3 * L + 5)) fail("2-input");
  c = run(c, 3 * (3 * L + 5));
  const h2 = h1 - (3 * L + 5);
  if (!c || c.state !== 3 || c.head !== h2 ||
      !matchesWindow(c.tape, h2, -5, 3, [-3, -2, -1, 2, 3])) fail("2-output");

  // 3. Fixed 20-step bridge, then scan L+1 blocks to the right.
  c = run(c, 20);
  const h3 = h2 + 4;
  if (!c || c.state !== 3 || c.head !== h3 ||
      !rightSweepInput(c.tape, h3, L + 1)) fail("3-input");
  c = run(c, 3 * (L + 1));
  const h4 = h3 + 3 * (L + 1);
  if (!c || c.state !== 3 || c.head !== h4 ||
      !matchesWindow(c.tape, h4, -2, 2, [0, 2])) fail("3-output");

  // 4. Fixed 9-step bridge, then scan a+1 blocks to the right.
  c = run(c, 9);
  const h5 = h4 + 3;
  if (!c || c.state !== 3 || c.head !== h5 ||
      !rightSweepInput(c.tape, h5, a + 1)) fail("4-input");
  c = run(c, 3 * (a + 1));
  const h6 = h5 + 3 * (a + 1);
  if (!c || c.state !== 3 || c.head !== h6 ||
      !matchesWindow(c.tape, h6, -1, 3, [2, 3])) fail("4-output");

  // 5. Fixed 6-step bridge, then drain b rightward three-one blocks.
  c = run(c, 6);
  const h7 = h6 + 4;
  if (!c || c.state !== 3 || c.head !== h7 ||
      !rightSweepInput(c.tape, h7, b)) fail("5-input");
  c = run(c, 3 * b);
  const h8 = h7 + 3 * b;
  if (!c || c.state !== 3 || c.head !== h8 ||
      !matchesWindow(c.tape, h8, -3, 5, [-3, 0])) fail("5-output");

  // 6. Final fixed 30-step bridge reaches the canonical S1 successor.
  c = run(c, 30);
  const R = (2n ** BigInt(L + a + 2)) - (2n ** BigInt(a)) - 1n;
  const target = s1Config(L + a + 2, R, 2, b,
    (2n ** BigInt(b)) - 1n, 0, 5 + 3 * b);
  const expectedSteps = 97 + 12 * (L + a) + 3 * b;
  requireCheck(c !== null && c.state === target.state &&
    c.head === target.head && sameTape(c.tape, target.tape),
    `final endpoint, L=${L}, a=${a}, b=${b}`);
  return expectedSteps;
}

const max = Number(process.argv[2] ?? 8);
if (!Number.isInteger(max) || max < 0 || max > 20)
  throw new Error("maxParameter must be an integer from 0 through 20");

let tested = 0;
let totalSteps = 0;
for (let L = 0; L <= max; ++L)
  for (let a = 0; a <= max; ++a)
    for (let b = 0; b <= max; ++b) {
      totalSteps += checkOne(L, a, b);
      ++tested;
    }

console.log(JSON.stringify({
  tested,
  parameterRange: `0 <= L,a,b <= ${max}`,
  allTenPhaseBoundariesMatched: true,
  fullS1SuccessorTapeMatched: true,
  exactStepFormula: "97 + 12*(L+a) + 3*b",
  totalStepsAcrossTests: totalSteps,
  status: "finite computational evidence only; not a universal proof"
}, null, 2));
