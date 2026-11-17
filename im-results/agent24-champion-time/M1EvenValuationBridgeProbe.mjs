#!/usr/bin/env node
// Reproducible finite-tape probe for the M1-even valuation bridge.
// This is computational evidence only; it is not a Lean proof.
//
// Source convention mirrored from S1Encoder:
//   left  = d1pow(a) ++ markerWord(1) ++ d0 ++ binDec(L,n) ++ lh
//   right = s0RightFacing(b) = [0,1,1,1,0,0] ++ d1pow(b+1)
// The transition table below is the exact TM2 table used by ChampionRootBridge.

const d0 = [0, 0, 1];
const d1 = [1, 1, 1];
const marker1 = [1, 0, 1];
const lh = [1, 1, 0, 1, 1, 1];
const d1pow = n => Array.from({ length: n }, () => d1).flat();

function binDec(L, n) {
  let p = 2 ** (L + 1) - 1 - n;
  const out = [];
  for (let i = 0; i < L; i++) {
    if (p <= 1) break;
    out.push(...(p % 2 === 0 ? d0 : d1));
    p = Math.floor(p / 2);
  }
  return out;
}

// Each transition is [writeBit, displacement, nextState]; null is halting.
const tm2 = [
  [[1, 1, 1], null],
  [[1, -1, 2], [0, 1, 5]],
  [[1, 1, 4], [0, -1, 3]],
  [[0, -1, 2], [1, 1, 1]],
  [[1, 1, 0], [1, 1, 4]],
  [[1, 1, 4], [0, 1, 3]],
];

function run(config, steps) {
  let { q, h, tape } = config;
  for (let k = 0; k < steps; k++) {
    const bit = tape.get(h) === true;
    const tr = tm2[q][bit ? 1 : 0];
    if (tr === null) throw new Error(`halted in state ${q} at head ${h}, step ${k}`);
    const [write, move, next] = tr;
    tape.set(h, write === 1);
    h += move;
    q = next;
  }
  return { q, h, tape };
}

function countLeftOnes(tape, h, cap) {
  let count = 0;
  while (count < cap && tape.get(h - 1 - count) === true) count++;
  return count;
}

function assert(condition, message) {
  if (!condition) throw new Error(message);
}

function checkCase({ L, v, qOdd, a, b }) {
  const n = (2 * qOdd + 1) * 2 ** v;
  assert(n < 2 ** L, `invalid counter n=${n} for L=${L}`);

  const left = [
    ...d1pow(a), ...marker1, ...d0, ...binDec(L, n), ...lh,
  ];
  const right = [0, 1, 1, 1, 0, 0, ...d1pow(b + 1)];
  const tape = new Map();
  left.forEach((bit, i) => tape.set(-i, bit === 1));
  right.forEach((bit, i) => tape.set(i + 1, bit === 1));

  // Existing counted_left_sweep(3*a+1): 9*a+3 steps.
  const hN = -(3 * a + 1);
  let c = run({ q: 3, h: 0, tape }, 9 * a + 3);
  assert(c.q === 3 && c.h === hN, `initial left sweep endpoint, v=${v}, n=${n}, a=${a}`);

  // Fixed 6-step state-3 -> state-1 prelude.
  c = run(c, 6);
  assert(c.q === 1 && c.h === hN && c.tape.get(hN) === false,
    `six-step prelude endpoint, v=${v}, n=${n}, a=${a}`);

  const N = 3 * (v + 1);
  assert(countLeftOnes(c.tape, hN, N + 1) === N + 1,
    `state-1 left-ones premise, v=${v}, n=${n}, a=${a}`);
  assert(c.tape.get(hN - N - 2) === false && c.tape.get(hN - N - 3) === false,
    `two-zero exit boundary, v=${v}, n=${n}, a=${a}`);
  assert(c.tape.get(hN + 1) === false &&
         c.tape.get(hN + 2) === true &&
         c.tape.get(hN + 3) === true &&
         c.tape.get(hN + 4) === true,
    `right boundary after initial sweep, v=${v}, n=${n}, a=${a}`);

  // State-1 left sweep: 3*(v+1) cycles, 9*(v+1) steps.
  c = run(c, 9 * (v + 1));
  assert(c.q === 1 && c.h === hN - N && c.tape.get(c.h) === false,
    `valuation left sweep endpoint, v=${v}, n=${n}, a=${a}`);

  // Four-step exit to state 4, then three-step setup to state 5.
  c = run(c, 4);
  assert(c.q === 4 && c.h === hN - N - 2 && c.tape.get(c.h) === false,
    `four-step exit endpoint, v=${v}, n=${n}, a=${a}`);
  c = run(c, 3);
  assert(c.q === 5 && c.h === hN - N + 1,
    `state-5 setup endpoint, v=${v}, n=${n}, a=${a}`);

  // State-5 right sweep: v+1 cycles, 3*(v+1)=N steps.
  c = run(c, 3 * (v + 1));
  assert(c.q === 5 && c.h === hN + 1 && c.tape.get(hN + 1) === false,
    `valuation right sweep endpoint, v=${v}, n=${n}, a=${a}`);

  // One-step exit to state 4; three-step q4 scan; final 3*a q4 scan.
  c = run(c, 1);
  assert(c.q === 4 && c.h === hN + 2,
    `state-5 exit endpoint, v=${v}, n=${n}, a=${a}`);
  c = run(c, 3);
  assert(c.q === 4 && c.h === hN + 5,
    `three-cell q4 scan endpoint, v=${v}, n=${n}, a=${a}`);
  c = run(c, 3 * a);
  assert(c.q === 4 && c.h === 4,
    `final q4 scan endpoint, v=${v}, n=${n}, a=${a}`);

  const total = 9 * a + 3 + 6 + 9 * (v + 1) + 4 + 3 +
    3 * (v + 1) + 1 + 3 + 3 * a;
  assert(total === 12 * a + 12 * v + 32, "prefix cost arithmetic");
  return { L, v, qOdd, n, a, b, total, endpoint: [c.q, c.h] };
}

const cases = [];
for (let v = 1; v <= 8; v++) {
  for (const qOdd of [1, 3, 5, 7, 9]) {
    for (const a of [0, 1, 2, 5, 10, 20]) {
      for (const b of [0, 2]) {
        const n = (2 * qOdd + 1) * 2 ** v;
        if (n < 2 ** 16) cases.push(checkCase({ L: 16, v, qOdd, a, b }));
      }
    }
  }
}
console.log(`PASS: ${cases.length} cases; v=1..8, q odd in {1,3,5,7,9}, a in {0,1,2,5,10,20}, b in {0,2}; every phase endpoint and total cost matched.`);
console.log("First case:", cases[0]);
console.log("Last case:", cases[cases.length - 1]);
