#!/usr/bin/env node
/**
 * Exact *finite, physical transition table* set-union arithmetic for accepted
 * Raw34 nonhalting proof cylinders. No Monte Carlo, tape simulation, or
 * Lean theorem checking is done by this script. Mathematical acceptance
 * resides in the original-source Lean CI runs in results/*.md.
 *
 * All 8 undefined slots of original Raw34 have 25 physical outcomes:
 * 24 write/direction/next-state moves and HALT. A proof cylinder is a
 * conjunction of ordinary transition equalities; undefined entries are
 * true wildcards including HALT. We count union via exact recursion over
 * 25-ary decisions, with wildcard pruning and memoization.
 *
 * The depth2/depth3 data are transcribed into Lean sources
 * Raw34Depth2SideCycles, Raw34Depth3Shard00..11. Each count is BigInt.
 */
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import assert from "node:assert/strict";

const root = dirname(fileURLToPath(import.meta.url));
const d2 = JSON.parse(readFileSync(join(root,"depth2-candidate-witnesses.json"),"utf8"));
const d3 = JSON.parse(readFileSync(join(root,"depth3-candidate-witnesses.json"),"utf8"));
assert.equal(d2.second_level.length,74);
assert.equal(d3.witnesses.length,1206);

const alphabet = ["HALT"];
for(const w of "01")
  for(const dir of "LR")
    for(const state of "ABCDEF")
      alphabet.push(w+dir+state);
assert.equal(alphabet.length,25);

// Fixed Raw34 slots: A0, B0, C0, D0.
// The remaining slots are ordered to prune the proof frontier quickly.
const slotOrder = [7,5,3,1,8,9,10,11]; // D1,C1,B1,A1,E0,E1,F0,F1
function pattern(table) {
  const t=table.replaceAll("_","");
  assert.equal(t.length,36,table);
  return slotOrder.map(slot => {
    const m=t.slice(3*slot,3*slot+3);
    return m==="---" ? null : m;
  });
}
const parent=pattern("1RB---_1RC---_0RD---_1LC---_------_------");
assert.equal(parent.filter(x=>x!==null).length,0);
const withSlot=(slot,value) => {
  const p=parent.slice();
  p[slot]=value;
  return p;
};

const firstMoves="0LA 0LB 0LC 0RA 0RB 0RC 0RD 1LC 1RA 1RB 1RC".split(" ");
const firstLevel=firstMoves.map(x=>withSlot(0,x));
const depth2=d2.second_level.map(x=>pattern(x.table));
const unary=[pattern("1RB---_1RC---_0RD1LC_1LC1RD_------_------")];

const cdMoves=[];
for(const write of "01")
  for(const dir of "LR")
    for(const next of "CD")
      cdMoves.push(write+dir+next);
assert.equal(cdMoves.length,8);
const cdClosed=[];
for(const c1 of cdMoves)
  for(const d1 of cdMoves)
    cdClosed.push([d1,c1,null,null,null,null,null,null]);

const depth3=d3.witnesses.map(x=>pattern(x.table));
const bcdMoves=[];
for(const write of "01")
  for(const dir of "LR")
    for(const next of "BCD")
      bcdMoves.push(write+dir+next);
assert.equal(bcdMoves.length,12);
const bcdClosed=[];
for(const b1 of bcdMoves)
  for(const c1 of bcdMoves)
    for(const d1 of bcdMoves)
      bcdClosed.push([d1,c1,b1,null,null,null,null,null]);

// Every pattern must be an eight-slot Raw34 child with ordinary transitions.
function validate(ps) {
  for(const p of ps) {
    assert.equal(p.length,8);
    for(const x of p) assert(x===null || alphabet.includes(x),String(x));
  }
}
function exactUnion(rawPatterns) {
  validate(rawPatterns);
  const patterns=[...new Map(rawPatterns.map(p=>[JSON.stringify(p),p])).values()];
  const memo=new Map();
  const power25=Array.from({length:9},(_,i)=>25n**BigInt(i));
  const empty=(id,at)=>{
    const p=patterns[id];
    for(let i=at;i<8;i++) if(p[i]!==null) return false;
    return true;
  };
  function count(ids,idx) {
    if(ids.length===0) return 0n;
    if(idx===8) return 1n;
    // Wildcard in all remaining slots: whole successor cube is accepted.
    if(ids.some(id=>empty(id,idx))) return power25[8-idx];
    const key=idx+":"+ids.join(",");
    if(memo.has(key)) return memo.get(key);
    const unconstrained=[],by=new Map();
    for(const id of ids) {
      const v=patterns[id][idx];
      if(v===null) unconstrained.push(id);
      else {
        if(!by.has(v)) by.set(v,[]);
        by.get(v).push(id);
      }
    }
    let total=0n;
    if(by.size===0) total=25n*count(ids,idx+1);
    else for(const value of alphabet) {
      const chosen=[...unconstrained,...(by.get(value)??[])].sort((a,b)=>a-b);
      total+=count(chosen,idx+1);
    }
    memo.set(key,total);
    return total;
  }
  return {
    count: count(patterns.map((_,i)=>i),0),
    uniquePatterns:patterns.length,
    memoStates:memo.size
  };
}

const stages=[
  ["Raw34-11-side-cycles",firstLevel,67138671875n],
  ["Raw34-74-depth-two-side-cycles",depth2,85205078125n],
  ["Raw34-unary-growth",unary,85449218750n],
  ["Raw34-64-closed-CD",cdClosed,85693359375n],
  ["Raw34-1206-depth-three-side-cycles",depth3,97470703125n],
  ["Raw34-1728-closed-BCD",bcdClosed,97509765625n],
  // Three additional *source-accepted* all-time growth cylinders.
  // See Raw34TripleSweepGrowth.lean and Raw34AlternatingGrowth.lean.
  ["Raw34-two-triple-sweep-growth",[
    pattern("1RB1LD_1RC---_0RD0RA_1LC1RD_------_------"),
    pattern("1RB---_1RC---_0RD0RE_1LC1RD_---1LD_------")
  ],97529296875n],
  ["Raw34-one-alternating-growth",[
    pattern("1RB---_1RC---_0RD0LD_1LC0RE_1RD---_------")
  ],97539062500n]
];
let union=[],prev=0n;
for(const [name,ps,expected] of stages) {
  assert.equal(new Set(ps.map(JSON.stringify)).size,ps.length,name+" local duplicate");
  union.push(...ps);
  const got=exactUnion(union);
  assert.equal(got.count,expected,name);
  console.log(JSON.stringify({
    source:name,
    added: (got.count-prev).toString(),
    union: got.count.toString(),
    unique_subcube_patterns:got.uniquePatterns,
    decision_diagram_states:got.memoStates
  }));
  prev=got.count;
}
assert.equal(prev,97539062500n);
assert.equal(25n**8n-prev,55048828125n);

// This last crosswalk identifies exactly the four new BCD closed-state
// cylinders after all prior accepted cylinders. It is exact because no
// prior pattern even partially intersects these BCD 5-hole cylinders.
const older=[...firstLevel,...depth2,...unary,...cdClosed,...depth3];
const newBCD=[],partialBCD=[];
for(const x of bcdClosed) {
  const covered=older.some(y=>y.every((v,i)=>v===null||v===x[i]));
  if(covered) continue;
  const overlaps=older.filter(y=>y.every((v,i)=>
    v===null||x[i]===null||v===x[i]));
  if(overlaps.length) partialBCD.push({pattern:x,overlaps:overlaps.length});
  else newBCD.push(x);
}
assert.equal(partialBCD.length,0);
assert.equal(newBCD.length,4);
const signatures=newBCD.map(x=>`B1=${x[2]},C1=${x[1]},D1=${x[0]}`).sort();
assert.deepEqual(signatures,[
  "B1=0LB,C1=1LB,D1=1RD",
  "B1=0LC,C1=1LB,D1=1RD",
  "B1=1LC,C1=1LB,D1=1RD",
  "B1=1LD,C1=0RB,D1=1RD"
]);
assert.equal(BigInt(newBCD.length)*25n**5n,39062500n);
console.log("FOUR_ADDITIONAL_BCD "+JSON.stringify(signatures));
console.log("PASS: exact physical-table Raw34 proved-union size 97,539,062,500 / 152,587,890,625; complement 55,048,828,125 (NOT proven halting)");
