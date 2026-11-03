'use strict';
const assert = require('node:assert/strict');

/** @typedef {null | [number, number, number]} Action */
/** @typedef {{state:number, head:number, tape:Map<number, number>}} Config */
const seed = 20261103;
const samplesPerAction = 400;
const stepBound = 96;
const slots = Array.from({length:12}, (_,i) => [Math.floor(i/2), i%2]);
/** @type {Action[]} */
const actions = [null];
for (let q=0;q<6;q++) for (const w of [0,1]) for (const d of [-1,1]) actions.push([w,d,q]);
let state = seed;
function next32() {
  state ^= state << 13;
  state ^= state >>> 17;
  state ^= state << 5;
  return state >>> 0;
}
function randomChoice() { return actions[next32() % actions.length]; }
function key(q,b) { return 2*q+b; }
function randomTable(first) {
  const table = Array.from({length:12}, () => randomChoice());
  table[0] = first;
  return table;
}
function transform(table) {
  const a = table[0];
  if (a === null) return {table:table.slice(), perm:[0,1,2,3,4,5], flip:1};
  const [w, d, q] = a;
  const perm = Array.from({length:6}, (_,s) => q===0 ? s : s===q ? 1 : s===1 ? q : s);
  const out = Array(12);
  for (const [s,b] of slots) {
    const t = table[key(s,b)];
    out[key(perm[s],b)] = t===null ? null : [t[0],t[1]*d,perm[t[2]]];
  }
  assert.deepEqual(out[0], [w,1,q===0?0:1]);
  assert.equal(perm[0],0);
  return {table:out,perm,flip:d};
}
function step(table,c) {
  const t = table[key(c.state,c.tape.get(c.head) ?? 0)];
  if (t===null) return null;
  const tape = new Map(c.tape);
  if (t[0]) tape.set(c.head,1);
  else tape.delete(c.head);
  return {state:t[2],head:c.head+t[1],tape};
}
function assertMapped(a,b,perm,flip) {
  assert.equal(b.state,perm[a.state]);
  assert.ok(b.head===a.head*flip);
  assert.deepEqual(Array.from(b.tape).sort((x,y)=>x[0]-y[0]),
    Array.from(a.tape,([x,y])=>[x===0?0:x*flip,y]).sort((x,y)=>x[0]-y[0]));
}
function check(table) {
  const norm=transform(table);
  let a={state:0,head:0,tape:new Map()};
  let b={state:0,head:0,tape:new Map()};
  for (let i=0;i<=stepBound;i++) {
    assertMapped(a,b,norm.perm,norm.flip);
    const na=step(table,a);
    const nb=step(norm.table,b);
    assert.equal(na===null,nb===null);
    if (na===null) return i+1;
    a=na;b=nb;
  }
  return null;
}
let trials=0, halts=0, maxScore=0;
for (const first of actions) {
  for (let j=0;j<samplesPerAction;j++) {
    const n=check(randomTable(first));
    trials++;
    if(n!==null) {halts++;maxScore=Math.max(maxScore,n);}
  }
}
for (const first of [[0,1,0],[0,-1,0],[1,1,0],[1,-1,0]]) {
  const table = Array(12).fill(null);
  table[0]=first;
  assert.equal(check(table),null);
  let c={state:0,head:0,tape:new Map()};
  for(let i=0;i<10000;i++) {
    c=step(table,c);
    assert.notEqual(c,null);
  }
}
// Independently check the 28 raw write/direction/halt-destination encodings
// against the 25 canonical outcomes, preserving the final attempted step.
const rawActions=[];
for (let q=0;q<=6;q++) for(const w of [0,1]) for(const d of [-1,1]) rawActions.push([w,d,q]);
let rawHalts=0;
for(let sample=0;sample<10000;sample++) {
  const rawTable=Array.from({length:12},()=>rawActions[next32()%28]);
  const canonical=rawTable.map(([w,d,q])=>q===6?null:[w,d,q]);
  let raw={state:0,head:0,tape:new Map()};
  let std={state:0,head:0,tape:new Map()};
  for(let n=0;n<stepBound;n++) {
    assert.deepEqual(raw,std);
    const t=rawTable[key(raw.state,raw.tape.get(raw.head)??0)];
    const next=step(canonical,std);
    if(t[2]===6) {
      assert.equal(next,null);
      rawHalts++;
      break;
    }
    assert.notEqual(next,null);
    const tp=new Map(raw.tape);
    if(t[0]) tp.set(raw.head,1); else tp.delete(raw.head);
    raw={state:t[2],head:raw.head+t[1],tape:tp};
    std=next;
  }
}
console.log(JSON.stringify({seed,trials,actions:actions.length,stepBound,halts,maxScore,driftCases:4,driftSteps:10000,rawTrials:10000,rawActions:28,rawHalts,ok:true}));
