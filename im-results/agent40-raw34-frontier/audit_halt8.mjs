#!/usr/bin/env node
/* Exact 25-action physical-cylinder audit of 109 source-checked Raw34
   ≤7-step HALT witnesses excluding D1=1RD. Verify disjointness and mass
   independently of source-checked Lean all_sound theorem. */
import assert from "node:assert/strict";
import {readFileSync} from "node:fs";
import {dirname,join} from "node:path";
import {fileURLToPath} from "node:url";
const path=join(dirname(fileURLToPath(import.meta.url)),"Raw34OtherD1Halt8.lean");
const src=readFileSync(path,"utf8");
const re=/⟨\[([\d,\s]+)\], \.halt (\d+)⟩/g;
const W=[...src.matchAll(re)].map(m=>({
 codes:m[1].split(",").map(x=>Number(x.trim())),t:Number(m[2])
}));
assert.equal(W.length,109);
const code=(w,r,q)=>2+(w*2+r)*6+q;
const root=[[0,code(1,1,1)],[2,code(1,1,2)],
            [4,code(0,1,3)],[6,code(1,0,2)]];
const free=[1,3,5,7,8,9,10,11];
const powers=Array.from({length:9},(_,i)=>25n**BigInt(i));
let mass=0n;const hist={};
for(const w of W){
 assert.equal(w.codes.length,12);
 assert(w.t>=0&&w.t<8);
 assert(w.codes.every(c=>Number.isInteger(c)&&c>=0&&c<=25));
 for(const [i,v] of root)assert.equal(w.codes[i],v);
 assert(w.codes[7]!==0&&w.codes[7]!==code(1,1,3));
 mass+=powers[free.filter(i=>w.codes[i]===0).length];
 hist[w.t]=(hist[w.t]??0)+1;
}
for(let i=0;i<W.length;i++)for(let j=i+1;j<W.length;j++){
 let conflict=false;
 for(let slot=0;slot<12;slot++){
  const a=W[i].codes[slot],b=W[j].codes[slot];
  if(a&&b&&a!==b){conflict=true;break;}
 }
 assert(conflict,"overlapping pair "+i+" "+j);
}
assert.equal(mass,9970703125n);
console.log(JSON.stringify({
 result:"exact disjoint physical halting cylinders; Lean source theorem checked separately",
 sourceTheorem:"BB6.Agent40Raw34Halt8.all_sound",
 witnessCount:W.length,timeHistogram:hist,
 disjointPairChecks:W.length*(W.length-1)/2,
 totalHaltingPhysical:String(mass),
 remainingOutOfOtherD1:String(24n*powers[7]-mass)
},null,2));
