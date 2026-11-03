'use strict';
const assert = require('node:assert/strict');
/** @typedef {{q:number,head:number,ones:Set<number>}} Config */
const RLE='1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD';
const parts=RLE.split('_');
assert.equal(parts.length,6);
const table=parts.map(pair=>{
  assert.equal(pair.length,6);
  return [pair.slice(0,3),pair.slice(3)].map(token=>{
    if(token==='---')return null;
    assert.match(token,/^[01][LR][A-F]$/);
    return {write:Number(token[0]),move:token[1]==='R'?1:-1,next:token.charCodeAt(2)-65};
  });
});
/** @param {Config} c @returns {Config} */
function clone(c){return {q:c.q,head:c.head,ones:new Set(c.ones)};}
/** @param {Config} c @returns {number} */
function read(c){return Number(c.ones.has(c.head));}
/** @param {Config} c @returns {boolean} True iff one instruction executes. */
function rawStep(c){
  const r=table[c.q][read(c)];
  if(r===null)return false;
  if(r.write)c.ones.add(c.head);else c.ones.delete(c.head);
  c.head+=r.move;c.q=r.next;return true;
}
/** Independently expanded D/0 return, preserving exact physical tape.
 * @param {Config} c @returns {{moves:number,halt:boolean,branch:string}} */
function macroStep(c){
  if(c.q!==3||read(c)){
    assert.ok(rawStep(c));return {moves:1,halt:false,branch:'ordinary'};
  }
  const p=c.head,l1=c.ones.has(p-1),l2=c.ones.has(p-2);
  c.ones.delete(p);
  c.ones.add(p-1);
  if(l1&&l2){
    c.head=p-2;c.q=0;return {moves:2,halt:true,branch:'D/0 left11'};
  }
  c.q=1;
  if(l1){
    c.ones.add(p-2);c.head=p-1;
    return {moves:3,halt:false,branch:'D/0 left01'};
  }
  c.ones.add(p);c.head=p+1;
  return {moves:3,halt:false,branch:'D/0 left_0'};
}
/** @param {Config} a @param {Config} b @param {string} where */
function compare(a,b,where){
  assert.equal(a.q,b.q,where+' state');
  assert.equal(a.head,b.head,where+' head');
  assert.equal(a.ones.size,b.ones.size,where+' ones count');
  for(const x of a.ones)assert.ok(b.ones.has(x),where+' tape bit '+x);
}
let checks=0;
for(let i=0;i<256;i++){
  const bits=new Set();
  const l1=Boolean(i&1),l2=Boolean(i&2);
  if(l1)bits.add(-1);if(l2)bits.add(-2);
  for(let j=0;j<6;j++)if((i >>> (j%6))&1)bits.add(j+2);
  const slow={q:3,head:0,ones:new Set(bits)};
  const quick=clone(slow),m=macroStep(quick);
  for(let j=0;j<m.moves;j++)assert.ok(rawStep(slow));
  compare(slow,quick,'synthetic-'+i);
  assert.equal(table[slow.q][read(slow)]===null,m.halt,'synthetic-'+i+' stop');
  checks++;
}
const raw={q:0,head:0,ones:new Set()};
assert.ok(rawStep(raw));
const fast=clone(raw);
let rawSteps=1,macroCalls=0,fullChecks=0;
const branches=new Map(),unusual=[];
while(rawSteps<2_000_000){
  const pos=fast.head,m=macroStep(fast);
  branches.set(m.branch,1+(branches.get(m.branch)||0));
  for(let i=0;i<m.moves;i++)assert.ok(rawStep(raw),'unexpected halt inside macro');
  rawSteps+=m.moves;macroCalls++;
  assert.equal(raw.q,fast.q,'step '+rawSteps+' state');
  assert.equal(raw.head,fast.head,'step '+rawSteps+' head');
  assert.equal(m.halt,table[raw.q][read(raw)]===null);
  if(m.halt)throw Error('Unexpected authentic blank-root halt');
  if(m.branch==='D/0 left01'&&unusual.length<25)unusual.push({rawSteps,position:pos});
  if(macroCalls<100||macroCalls%5000===0){compare(raw,fast,'step '+rawSteps);fullChecks++;}
}
compare(raw,fast,'final');
console.log('PASS source table',RLE);
console.log('PASS synthetic D/0 full-tape cases',checks);
console.log('PASS authentic blank-root raw steps',rawSteps);
console.log('macroCalls',macroCalls,'fullChecks',fullChecks);
console.log('branches',Object.fromEntries(branches));
console.log('first rare D/0 left01 returns',unusual.slice(0,12));
console.log('final',{state:'ABCDEF'[raw.q],head:raw.head,markedCells:raw.ones.size});
console.log('No claim of infinite nonhalting: finite checks only');
