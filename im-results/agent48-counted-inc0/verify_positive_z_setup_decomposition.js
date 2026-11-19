// Reproduce the fixed-bridge / counted-sweep decomposition of the
// positive-z first-checkpoint setup macro.
// Transition table copied from the standard TM2 definition in
// ChampionRootBridge.lean. No dependencies are required; run with Node.js.

"use strict";

const tm2 = [
  [[1,1,1], null],
  [[1,-1,2],[0,1,5]],
  [[1,1,4],[0,-1,3]],
  [[0,-1,2],[1,1,1]],
  [[1,1,0],[1,1,4]],
  [[1,1,4],[0,1,3]]
];

const rep = (n, block) => Array.from({length:n}, () => block).flat();
const d1 = n => rep(n, [1,1,1]);
const d0 = n => rep(n, [0,0,1]);
const d010 = n => rep(n, [0,1,0]);

function run(tape, q, h, steps) {
  let minHead = h, maxHead = h;
  for (let t = 0; t < steps; t++) {
    // q4BridgeAt checks heads before each transition, not the final head.
    minHead = Math.min(minHead, h);
    maxHead = Math.max(maxHead, h);
    const transition = tm2[q][tape.has(h) ? 1 : 0];
    if (transition === null) throw new Error(`TM halted at local step ${t}`);
    const [write, move, nextState] = transition;
    if (write) tape.add(h);
    else tape.delete(h);
    h += move;
    q = nextState;
  }
  return {q, h, minHead, maxHead};
}

function windowBits(tape, h, lo, hi) {
  const out = [];
  for (let x = lo; x <= hi; x++) out.push(tape.has(h+x) ? 1 : 0);
  return out;
}

function assertArray(actual, expected, label) {
  if (actual.join("") !== expected.join(""))
    throw new Error(`${label}: expected ${expected.join("")}, got ${actual.join("")}`);
}

function bridge(tape, q, h, steps, lo, hi, startBits, headDelta, endBits, name) {
  if (q !== 3) throw new Error(`${name}: expected state 3, got ${q}`);
  assertArray(windowBits(tape,h,lo,hi), startBits, `${name} input`);
  const r = run(tape,q,h,steps);
  if (r.q !== 3 || r.h !== h+headDelta)
    throw new Error(`${name}: wrong endpoint ${JSON.stringify(r)}`);
  if (r.minHead < h+lo || r.maxHead > h+hi)
    throw new Error(`${name}: head escaped frame ${JSON.stringify(r)}`);
  assertArray(windowBits(tape,h,lo,hi), endBits, `${name} output`);
  return r;
}

function countedRightSweep(tape, q, h, n, name) {
  if (q !== 3) throw new Error(`${name}: expected state 3, got ${q}`);
  for (let i=0; i<n; i++) {
    for (let j=0; j<3; j++) {
      if (!tape.has(h+3*i+j))
        throw new Error(`${name}: missing input one at block ${i}, offset ${j}`);
    }
  }
  const r = run(tape,q,h,3*n);
  if (r.q !== 3 || r.h !== h+3*n)
    throw new Error(`${name}: wrong sweep endpoint`);
  for (let i=0; i<n; i++) {
    if (!tape.has(h+3*i) || tape.has(h+3*i+1) || tape.has(h+3*i+2))
      throw new Error(`${name}: incorrect physical 100 output at block ${i}`);
  }
  return r;
}

function sameTape(tape, head, left, right) {
  const expected = new Set();
  left.forEach((b,i) => { if (b) expected.add(head-i); });
  right.forEach((b,i) => { if (b) expected.add(head+1+i); });
  return expected.size === tape.size && [...expected].every(x => tape.has(x));
}

function verify(A,L,z) {
  if (!(A >= 1 && L >= 0 && z >= 2))
    throw new Error("this uniform B30 frame test requires A>=1, L>=0, z>=2");

  // S0 input immediately after the first counted drain:
  // left = d1pow(A) ++ markerWord(1) ++ d0 ++ d1pow(L) ++ lh
  // right = 011100 ++ d1pow(z+1).
  const ell0 = [1,0,1, 0,0,1, ...d1(L), 1,1,0,1,1,1];
  const tape = new Set();
  [...d1(A), ...ell0].forEach((b,i) => { if (b) tape.add(-i); });
  [0,1,1,1,0,0, ...d1(z+1)].forEach((b,i) => { if (b) tape.add(i+1); });

  let q=3, h=0, r;

  // First left-one scan and B8.
  r=run(tape,q,h,9*A+3); q=r.q; h=r.h;
  r=bridge(tape,q,h,8,-3,1,
    [0,0,1,0,0], -2, [1,1,0,1,0], "B8");
  q=r.q; h=r.h;

  // Second left-one scan.
  r=run(tape,q,h,9*L+15); q=r.q; h=r.h;

  // B20 ; sweep (L+1) ; B9 ; sweep (A+1) ; B6 ; sweep z ; B30.
  r=bridge(tape,q,h,20,-5,3,
    [0,0,1,1,1,0,0,1,1], 4,
    [1,1,1,0,1,1,1,0,0], "B20");
  q=r.q; h=r.h;

  r=countedRightSweep(tape,q,h,L+1,"right sweep L+1"); q=r.q; h=r.h;

  r=bridge(tape,q,h,9,-2,2,
    [0,0,1,0,1], 3, [1,1,1,0,0], "B9");
  q=r.q; h=r.h;

  r=countedRightSweep(tape,q,h,A+1,"right sweep A+1"); q=r.q; h=r.h;

  r=bridge(tape,q,h,6,-1,3,
    [0,0,0,1,1], 4, [1,1,1,0,0], "B6");
  q=r.q; h=r.h;

  if (h !== 9) throw new Error(`z sweep should start at cell 9, got ${h}`);
  r=countedRightSweep(tape,q,h,z,"right sweep z"); q=r.q; h=r.h;

  r=bridge(tape,q,h,30,-4,5,
    [0,1,0,0,1,0,0,0,0,0], -4,
    [0,0,1,1,1,0,0,1,1,1], "B30");
  q=r.q; h=r.h;

  const ell1 = [
    1,1, ...d010(A+1), 0,1,1,1,1,0,
    ...d010(L), 0,1,1,1,0,1,1,1
  ];
  const targetLeft = [...d0(z), ...ell1];
  const targetRight = [0,1,1,1,0,0, ...d1(1)];
  const expectedSteps = 12*(A+L)+3*z+97;

  if (q !== 3 || h !== 3*z+5 || !sameTape(tape,h,targetLeft,targetRight))
    throw new Error(`final S0 mismatch at (A,L,z)=(${A},${L},${z}); q=${q}, h=${h}`);

  return expectedSteps;
}

let cases = 0;
let maxSteps = 0;
for (let A=1; A<=6; A++) {
  for (let L=0; L<=5; L++) {
    for (let z=2; z<=30; z++) {
      maxSteps = Math.max(maxSteps, verify(A,L,z));
      cases++;
    }
  }
}
for (const [A,L,z] of [[7,8,31],[10,15,100],[71,76,1000]]) {
  maxSteps = Math.max(maxSteps, verify(A,L,z));
  cases++;
}
console.log(`PASS: ${cases} parameter triples; maximum simulated setup length ${maxSteps} steps`);
