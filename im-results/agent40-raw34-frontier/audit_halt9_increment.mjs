#!/usr/bin/env node
/* Exact source-witness audit of the 958 NEW eight-step Raw34 halters.
   Check pairwise disjointness within this source family and against 109
   previously source-submitted halters that stop within seven steps. */
import assert from "node:assert/strict";
import {readFileSync} from "node:fs";
import {dirname,join} from "node:path";
import {fileURLToPath} from "node:url";
const dir=dirname(fileURLToPath(import.meta.url));
function read(file){
 const s=readFileSync(join(dir,file),"utf8");
 return [...s.matchAll(/⟨\[([\d,\s]+)\], \.halt (\d+)⟩/g)]
   .map(m=>({codes:m[1].split(",").map(x=>Number(x.trim())),t:Number(m[2])}));
}
const old=read("Raw34OtherD1Halt8.lean"),newer=read("Raw34OtherD1Halt9New.lean");
assert.equal(old.length,109);assert.equal(newer.length,958);
const code=(w,r,q)=>2+(w*2+r)*6+q;
const fixed=new Map([[0,code(1,1,1)],[2,code(1,1,2)],
 [4,code(0,1,3)],[6,code(1,0,2)]]);
const free=[1,3,5,7,8,9,10,11],pow=Array.from({length:9},(_,i)=>25n**BigInt(i));
function audit(w,expect){
 assert.equal(w.codes.length,12);
 assert.equal(w.t,expect);
 assert(w.codes.every(c=>Number.isInteger(c)&&c>=0&&c<=25));
 for(const [i,c] of fixed)assert.equal(w.codes[i],c);
 assert(w.codes[7]!==0&&w.codes[7]!==code(1,1,3));
 return pow[free.filter(i=>w.codes[i]===0).length];
}
let mass=0n;for(const w of newer)mass+=audit(w,8);
assert.equal(mass,1105468750n);
function disjoint(a,b){
 for(let i=0;i<12;i++)
  if(a.codes[i]&&b.codes[i]&&a.codes[i]!==b.codes[i])return true;
 return false;
}
for(let i=0;i<newer.length;i++){
 for(let j=i+1;j<newer.length;j++)
  assert(disjoint(newer[i],newer[j]),"new/new overlap "+i+" "+j);
 for(let j=0;j<old.length;j++)
  assert(disjoint(newer[i],old[j]),"new/old overlap "+i+" "+j);
}
const total=mass+9970703125n;
assert.equal(total,11076171875n);
console.log(JSON.stringify({
 status:"exact disjoint source-witness physical-table audit",
 source:"BB6.Agent40Raw34Halt9New.all_sound",
 existingHalt8:old.length,additionalHalt9:newer.length,
 additionalHalt9Physical:String(mass),
 totalHalt8PlusHalt9Physical:String(total),
 checkedDisjointPairs:newer.length*(newer.length-1)/2+newer.length*old.length,
 excluding:"D1=1RD"
},null,2));
