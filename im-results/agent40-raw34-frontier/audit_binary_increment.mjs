#!/usr/bin/env node
/**
 * Exact physical-table complement audit for one source-certified Raw34 binary
 * odometer child against the original Agent50 3087 cylinders and the nine
 * closed-state graph families accepted in CI 46097387657.
 *
 * The binary child has exact three fixed unknown slots D1=1RE,C1=0LC,E0=1RD.
 * All other five slots remain completely unrestricted, even if HALT.
 * This script calculates cardinality with BigInt by a complete recursive
 * 25-action partition. No Turing simulation and no unproved dynamics.
 */
import assert from "node:assert/strict";
import {readFileSync} from "node:fs";
import {dirname,join} from "node:path";
import {fileURLToPath} from "node:url";

const root=join(dirname(fileURLToPath(import.meta.url)),"../agent50-raw34-firsthole");
const depth2=JSON.parse(readFileSync(join(root,"depth2-candidate-witnesses.json"),"utf8")).second_level;
const depth3=JSON.parse(readFileSync(join(root,"depth3-candidate-witnesses.json"),"utf8")).witnesses;
assert.equal(depth2.length,74);
assert.equal(depth3.length,1206);

const alphabet=["HALT"];
for(const w of "01") for(const dir of "LR") for(const q of "ABCDEF") alphabet.push(w+dir+q);
assert.equal(alphabet.length,25);

const slots=[7,5,3,1,8,9,10,11]; // D1, C1, B1, A1, E0, E1, F0, F1
function parse(table) {
  const t=table.replaceAll("_","");
  assert.equal(t.length,36,table);
  const fixed=new Map([[0,"1RB"],[2,"1RC"],[4,"0RD"],[6,"1LC"]]);
  for(const [index,action] of fixed) assert.equal(t.slice(index*3,index*3+3),action,table);
  return slots.map(i=>{
    const x=t.slice(i*3,i*3+3);
    assert(x==="---"||alphabet.includes(x),"invalid physical action "+x);
    return x==="---"?null:x;
  });
}
const old=[];
const add=p=>old.push(p);
"0LA 0LB 0LC 0RA 0RB 0RC 0RD 1LC 1RA 1RB 1RC".split(" ").forEach(x=>add([x,null,null,null,null,null,null,null]));
depth2.forEach(x=>add(parse(x.table)));
add(parse("1RB---_1RC---_0RD1LC_1LC1RD_------_------"));
const cd=[];
for(const w of "01")for(const d of "LR")for(const q of "CD")cd.push(w+d+q);
for(const c1 of cd)for(const d1 of cd)add([d1,c1,null,null,null,null,null,null]);
depth3.forEach(x=>add(parse(x.table)));
const bcd=[];
for(const w of "01")for(const d of "LR")for(const q of "BCD")bcd.push(w+d+q);
for(const b1 of bcd)for(const c1 of bcd)for(const d1 of bcd)
  add([d1,c1,b1,null,null,null,null,null]);
for(const table of [
  "1RB1LD_1RC---_0RD0RA_1LC1RD_------_------",
  "1RB---_1RC---_0RD0RE_1LC1RD_---1LD_------",
  "1RB---_1RC---_0RD0LD_1LC0RE_1RD---_------",
])add(parse(table));
assert.equal(old.length,3087);
// Overlap between already accepted certificate families is expected: 3,087
// source patterns contain 2,876 distinct literal patterns. The recursive
// union calculator handles both duplication and proper cylinder overlap.
assert.equal(new Set(old.map(JSON.stringify)).size,2876);



const binary = parse("1RB---_1RC---_0RD0LC_1LC1RE_1RD---_------");
assert.deepEqual(binary,["1RE","0LC",null,null,"1RD",null,null,null]);
const names=["D1","C1","B1","A1","E0","E1","F0","F1"];
const family=["CDE","CDF","CDEF","BCDE","BCDF","BCDEF",
              "ABCD","ABCDE","ABCDF"].map((S,k)=>({
  S,bit:1<<k,
  slots:names.map((v,i)=>S.includes(v[0])?i:-1).filter(i=>i>=0)
}));
const allow=names.map((_,i)=>binary[i]===null?alphabet:[binary[i]]);
const suffixVolume=Array.from({length:9},(_,i)=>
  allow.slice(i).reduce((z,v)=>z*BigInt(v.length),1n));
assert.equal(suffixVolume[0],25n**5n);

function shift(mask,i,a){
 for(const f of family){
  if((mask&f.bit)!==0 && f.slots.includes(i) &&
     (a==="HALT" || !f.S.includes(a[2])))mask &= ~f.bit;
 }
 return mask;
}
const freeCache=new Map(),oldCache=new Map();
function graphNotCoveredFree(at,mask){
 if(at===8)return mask===0?1n:0n;
 const key=at+":"+mask;
 if(freeCache.has(key))return freeCache.get(key);
 if(mask===0)return suffixVolume[at];
 let sum=0n;
 for(const a of allow[at])sum+=graphNotCoveredFree(at+1,shift(mask,at,a));
 freeCache.set(key,sum);
 return sum;
}
function outsideOldAndGraph(ids,at,mask){
 if(ids.some(id=>old[id].slice(at).every(v=>v===null)))return 0n;
 if(mask===0 && ids.length===0)return suffixVolume[at];
 if(ids.length===0)return graphNotCoveredFree(at,mask);
 if(at===8)return mask===0?1n:0n;
 const key=at+":"+mask+":"+ids.join(",");
 if(oldCache.has(key))return oldCache.get(key);
 const free=[],by=new Map();
 for(const id of ids){
  const v=old[id][at];
  if(v===null)free.push(id);
  else {
   if(!by.has(v))by.set(v,[]);
   by.get(v).push(id);
  }
 }
 let sum=0n;
 for(const a of allow[at]){
  const nextIds=[...free,...(by.get(a)??[])].sort((a,b)=>a-b);
  sum+=outsideOldAndGraph(nextIds,at+1,shift(mask,at,a));
 }
 oldCache.set(key,sum);
 return sum;
}
const newMass=outsideOldAndGraph(old.map((_,i)=>i),0,(1<<family.length)-1);
const full=suffixVolume[0],already=full-newMass;
assert.equal(full,9765625n);
assert.equal(newMass,1790125n);
assert.equal(already,7975500n);
const parentNonhaltBefore=123226284000n;
const parentNonhaltAfter=parentNonhaltBefore+newMass;
assert.equal(parentNonhaltAfter,123228074125n);
assert.equal(25n**8n-parentNonhaltAfter,29359816500n);
console.log(JSON.stringify({
  status:"exact 25-action physical-table union arithmetic",
  sourceBinaryTheorem:"BB6.Agent40Raw34BinaryCounter.all_time_never",
  sourceGraphTheorem:"BB6.Agent40Raw34GraphClosed.never_of_mask",
  child:"1RB---_1RC---_0RD0LC_1LC1RE_1RD---_------",
  childTotal:String(full),
  binaryAlreadyInPriorNonhaltingUnion:String(already),
  binaryAdditionalBeyondPriorUnion:String(newMass),
  oldPlusNineGraphSourceAcceptedPhysicalMass:String(parentNonhaltBefore),
  newRaw34NonhaltingPhysicalMassIfBinaryAccepted:String(parentNonhaltAfter),
  remainderOutsideNonhaltingPortfolio:String(25n**8n-parentNonhaltAfter),
  countRecursionStates:oldCache.size,
  countTailStates:freeCache.size
},null,2));
