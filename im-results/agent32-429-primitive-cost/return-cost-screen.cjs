'use strict';

const assert = require('node:assert/strict');
const rle = '1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA';
const letters = 'ABCDEF';
const rows = rle.split('_');
assert.equal(rows.length, 6);
const machine = rows.map((row) => [row.slice(0, 3), row.slice(3)]
  .map((word) => word === '---' ? null : {
    write: word.charAt(0) === '1',
    right: word.charAt(1) === 'R',
    state: letters.indexOf(word.charAt(2)),
  }));
for (const row of machine) assert.equal(row.length, 2);

/**
 * Predictions are numerical conjectures unless a corresponding Lean theorem
 * explicitly establishes them.
 * @param {number} u
 * @param {number} w
 */
function predicted(u, w) {
  const m = Math.floor(w / 2);
  const d = u - m;
  if (w >= 2*u+3) return {name: 'high3', next: [2*u+3,w-2*u-3], steps: 4*u*u+10*u+27, c0: 0};
  if (w === 2*u+2) return {name: 'high2', next: [0,4*u+18], steps: 4*u*u+44*u+204, c0: 2};
  if (w === 2*u+1) return {name: 'high1', next: [11,4*u+2], steps: 4*u*u+28*u+306, c0: 2};
  if (w === 2*u) return {name: 'high0', next: [0,4*u+12], steps: 4*u*u+28*u+110, c0: 2};
  if (w % 2 === 0 && d === 1) return {name: 'even1', next: [0,2*w+12], steps: 4*u*u+14*u+61, c0: 2};
  if (w % 2 === 0 && d % 2 === 0) return {name: 'evenEven', next: [11,2*u+w-2], steps: (18*u+2*w*w+13*w+522)/2, c0: 2};
  if (w % 2 === 0) return {name: 'evenOdd', next: [0,2*u+w+10], steps: (18*u+2*w*w+13*w+140)/2, c0: 2};
  if (d === 1) return {name: 'fatal', next: null, steps: 4*u*u+10*u+26, c0: 1};
  if (d === 2) return {name: 'odd2', next: [0,2*w+8], steps: 4*u*u+6*u+26, c0: 1};
  if (d % 2 === 0 && w === 1) return {name: 'oddEven1', next: [11,2*u+10], steps: 28*u+451, c0: 3};
  if (d % 2 === 0) return {name: 'oddEven', next: [d+7,2*w-4], steps: (38*u+2*w*w-w+271)/2, c0: 1};
  return {name: 'oddOdd', next: [d+3,2*w], steps: (22*u+2*w*w+7*w+125)/2, c0: 1};
}

/** @param {number} u @param {number} w @returns {Set<number>} */
function jTape(u, w) {
  const tape = new Set();
  let x = -(2*u+6);
  for (let i=0;i<5;i++) tape.add(x++);
  for (let i=0;i<u;i++) {tape.add(x++);x++;}
  tape.add(x++);
  assert.equal(x,0);
  for(let i=0;i<w+2;i++) tape.add(i);
  tape.add(w+3);
  return tape;
}

/** @param {Set<number>} tape @param {number} head @param {number} u @param {number} w */
function matchesJ(tape, head, u, w) {
  const expected = jTape(u,w);
  if (tape.size !== expected.size) return false;
  for (const x of expected) if (!tape.has(x+head)) return false;
  return true;
}

/** @param {number} u @param {number} w */
function simulate(u,w) {
  const p = predicted(u,w);
  const tape = jTape(u,w);
  let head=0,state=0,maxHead=w+3,c0=0,badC0=0;
  for (let t=0;t<=p.steps+1;t++) {
    const bit=Number(tape.has(head));
    if (state===2 && bit===0) {
      c0++;
      if (head<maxHead) badC0++;
      if (p.next!==null) assert.equal(tape.has(head+1),false,
        `nonfatal C/01: J(${u},${w}) step=${t}`);
      else assert.equal(tape.has(head+1),true,
        `fatal C/01: J(${u},${w}) step=${t}`);
    }
    if (p.next !== null && t===p.steps) {
      assert.equal(state,0,`target state J(${u},${w})`);
      assert(matchesJ(tape,head,...p.next),`target tape J(${u},${w})`);
      assert.equal(c0,p.c0,`C/0 count J(${u},${w})`);
      assert.equal(badC0,0,`nonrecord C/0 J(${u},${w})`);
      return {time:t,branch:p.name,c0,badC0,head,maxHead};
    }
    const action=machine[state][bit];
    if (action===null) {
      assert.equal(p.next,null,`unexpected halt J(${u},${w}) t=${t}`);
      assert.equal(t,p.steps,`fatal step J(${u},${w})`);
      assert.equal(state,3);
      assert.equal(bit,1);
      assert.equal(c0,p.c0);
      assert.equal(badC0,1);
      return {time:t,branch:p.name,c0,badC0,head,maxHead};
    }
    if (action.write) tape.add(head); else tape.delete(head);
    head+=action.right?1:-1;
    state=action.state;
    maxHead=Math.max(maxHead,head);
  }
  assert.fail(`predicted return/halting time exceeded: J(${u},${w})`);
}

const counts = Object.create(null);
let cases=0, largest=0;
function check(u,w) {
  assert(Number.isSafeInteger(u)&&u>=0&&Number.isSafeInteger(w)&&w>=0);
  const t=simulate(u,w);
  counts[t.branch]=(counts[t.branch]||0)+1;
  largest=Math.max(largest,t.time);
  cases++;
}
for(let u=0;u<40;u++) for(let w=0;w<82;w++) check(u,w);
let seed=0x429429;
for(let i=0;i<1000;i++) {
  seed=(1664525*seed+1013904223)>>>0;
  const u=seed%192;
  seed=(1664525*seed+1013904223)>>>0;
  const w=seed%400;
  check(u,w);
}
console.log(JSON.stringify({rle,kind:'bounded synthetic J verification only',cases,
  seed:0x429429,randomCases:1000,gridU:'[0,40)',gridW:'[0,82)',
  largestRawSteps:largest,branchCounts:counts,unboundedFormalProof:false},null,2));
