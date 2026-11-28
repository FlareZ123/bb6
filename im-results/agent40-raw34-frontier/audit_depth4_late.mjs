#!/usr/bin/env node
/**
 * Reconstruct the 535 source-checkable first-new-query Raw34 halters.
 * All slots are literal original six-state physical moves; 0 means partial
 * wildcard, 1 HALT and 2..25 the 24 ordinary moves.  Halters at depth-three
 * and earlier are intentionally not counted again.
 *
 * This output provides an independently rerunnable finite source audit, not a
 * substitute for the Lean all-completion proof in five linked shard modules.
 */
import assert from "node:assert/strict";
import {readFileSync} from "node:fs";
import {dirname,join} from "node:path";
import {fileURLToPath} from "node:url";
const dir=dirname(fileURLToPath(import.meta.url));
const root=[21,0,22,0,11,0,16,0,0,0,0,0];
const names=["HALT"];
for(const w of "01")for(const d of "LR")for(const q of "ABCDEF")
 names.push(w+d+q);
const codeOf=new Map(names.map((x,i)=>[x,i+1]));
assert.equal(codeOf.get("1RD"),23);
function sim(p,max=32){
 let q=0,h=0,ones=new Set();
 for(let t=0;t<=max;t++){
  const slot=2*q+(ones.has(h)?1:0),action=p[slot];
  if(action===0)return {type:"unknown",slot,t};
  if(action===1)return {type:"halt",t};
  const x=action-2;
  x>=12?ones.add(h):ones.delete(h);
  q=x%6;h+=(x%12>=6)?1:-1;
 }
 return {type:"long"};
}
const W=[],parents=new Map(),hist=new Map(),unknowns=new Map();
for(let D1=1;D1<=25;D1++){
 if(D1===codeOf.get("1RD"))continue;
 for(let C1=1;C1<=25;C1++)for(let B1=1;B1<=25;B1++){
  const p=root.slice();
  p[7]=D1;p[5]=C1;p[3]=B1;
  const f=sim(p);
  if(f.type!=="unknown")continue;
  assert([1,8,9,10,11].includes(f.slot),"first query not in remaining source");
  unknowns.set(f.slot,1+(unknowns.get(f.slot)||0));
  for(let a=1;a<=25;a++){
   p[f.slot]=a;
   const outcome=sim(p);
   if(outcome.type==="halt"&&outcome.t>=9){
    W.push({codes:p.slice(),n:outcome.t});
    hist.set(outcome.t,1+(hist.get(outcome.t)||0));
    const k=names[D1-1];parents.set(k,1+(parents.get(k)||0));
   }
   p[f.slot]=0;
  }
 }
}
assert.equal(W.length,535);
assert.equal(new Set(W.map(x=>x.codes.join(","))).size,535);
assert.equal(W.every(w=>w.codes.slice(0,12).filter(x=>x!==0).length===8),true);
// 4 original fixed slots + D1,C1,B1 + first newly queried slot
const pair=(a,b)=>a.some((v,i)=>v!==0&&b[i]!==0&&v!==b[i]);
for(let i=0;i<W.length;i++)for(let j=i+1;j<W.length;j++)
 assert(pair(W[i].codes,W[j].codes),"overlap among depth4 halters: "+i+","+j);
const late=readFileSync(join(dir,"Raw34LateThreeSlotHalters.lean"),"utf8");
const parse=s=>[...s.matchAll(/⟨\[([\d,\s]+)\], \.halt (\d+)⟩/g)]
  .map(m=>({codes:m[1].split(",").map(x=>Number(x.trim())),n:Number(m[2])}));
const earlier=parse(late);assert.equal(earlier.length,5);
for(const w of W)for(const v of earlier)assert(pair(w.codes,v.codes));
const files=Array.from({length:5},(_,i)=>join(dir,`Raw34Depth4HalterShard${String(i).padStart(2,"0")}.lean`));
const actual=files.flatMap(p=>parse(readFileSync(p,"utf8")));
assert.equal(actual.length,W.length);
for(let i=0;i<W.length;i++)
 assert.deepEqual(actual[i],W[i],"Lean source list mismatch at witness "+i);
const volume=BigInt(W.length)*25n**4n;
assert.equal(volume,208984375n);
const combinedNew=volume+BigInt(earlier.length)*25n**5n;
assert.equal(combinedNew,257812500n);
const initialResidual=5582309901n,remaining=initialResidual-combinedNew;
assert.equal(remaining,5324497401n);
console.log(JSON.stringify({
 status:"Exact original-source first-query census and disjoint physical cylinders",
 root:"1RB---_1RC---_0RD---_1LC---_------_------",
 depth4HaltingWitnesses:W.length,
 depth4NewPhysicalCompletions:String(volume),
 otherNewDepth3Halters:earlier.length,
 combinedNewPhysicalCompletions:String(combinedNew),
 unchangedOldBankResidual:String(initialResidual),
 newResidualAfterLeanAcceptance:String(remaining),
 firstUnknownSlotHistogram:Object.fromEntries(unknowns),
 queriedHaltTimeHistogram:Object.fromEntries(hist),
 D1Counts:Object.fromEntries(parents),
 physicalOutcomesPerFreeSlot:25,
 sourceAcceptable:"Lean must compile all_halt and audit axioms on five shards"
},null,2));
