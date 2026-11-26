'use strict';
const fs = require('node:fs');
const assert = require('node:assert/strict');
const path = require('node:path');
const source = fs.readFileSync(path.join(__dirname, '../agent49-box-complement/Raw10Encoded.lean'), 'utf8');
const rows = [...source.matchAll(/^\[([0-9,]+)\],?$/gm)].map(m => m[1].split(',').map(Number));
assert.equal(rows.length, 66);
const all = Array.from({length: 25}, (_, i) => i);
const base = Array.from({length: 12}, (_, i) => i === 0 ? [8] : i === 2 ? [11] : all);
/** @param {number[][]} box @param {number[][]} cut */
function subtract(box, cut) {
  if (cut.some((vs, i) => !vs.some(v => box[i].includes(v)))) return [box];
  let prefix = box.slice();
  const out = [];
  for (let i = 0; i < 12; ++i) {
    const rejected = prefix[i].filter(v => !cut[i].includes(v));
    if (rejected.length) {
      const piece = prefix.slice();
      piece[i] = rejected;
      out.push(piece);
    }
    prefix = prefix.slice();
    prefix[i] = prefix[i].filter(v => cut[i].includes(v));
  }
  return out;
}
let original = [base];
for (const row of rows) original = original.flatMap(b => subtract(b, row.map(v => v ? [v] : all)));
assert.equal(original.length, 34);
// Exact Raw10FixedLeaves.cycleTable and haltTable; -1 = unassigned, 0 = halt.
const cycle = [8,14,11,-1,17,4,9,2,23,15,10,-1].map(v => v === -1 ? all : [v]);
const halt = [8,0,11,-1,-1,0,-1,-1,-1,-1,-1,-1].map(v => v === -1 ? all : [v]);
const refined = original.flatMap(b => subtract(b, cycle)).flatMap(b => subtract(b, halt));
/** @param {number[][]} r @param {number[][]} c */
const subset = (r,c) => r.every((vs,i) => vs.every(v => c[i].includes(v)));
const mass = b => b.reduce((n,vs) => n * BigInt(vs.length),1n);
const total = bs => bs.reduce((n,b) => n + mass(b),0n);
assert.equal(refined.length, 41);
assert.equal(total(refined), 90737503713725n);
const mapped = refined.map((b, i) => ({i, original: original.findIndex(c => subset(b,c)), mass: mass(b).toString()}));
assert(mapped.every(r => r.original >= 0));
const accepted = new Set([8,18,19,20,21,22,23,24]);
const candidate = new Set([...accepted,16,17]);
for (const [label, ids, count] of [['accepted',accepted,33],['candidate',candidate,31]]) {
  const closed = mapped.filter(r => ids.has(r.original));
  const open = mapped.filter(r => !ids.has(r.original));
  assert.equal(open.length, count);
  console.log(label, {closed, openCount: open.length, openIndices: open.map(x => x.i),
    closedMass: closed.reduce((n,r) => n + BigInt(r.mass),0n).toString()});
}
