#!/usr/bin/env node
/**
 * Exact physical-table arithmetic for a three-family Raw34 closed-state union
 * {C,D,E}, {C,D,F}, and {C,D,E,F}. This is not a
 * substitute for Lean source acceptance of Raw34ClosedCDE.all_cde.
 *
 * Root: 1RB---_1RC---_0RD---_1LC---_------_------
 * Slots (in physical first-hole order): D1,C1,B1,A1,E0,E1,F0,F1
 * Each slot has 25 distinct total-machine actions (HALT included).
 * New source family: C1,D1,E0,E1 each have successor in C,D,E.
 * Other four slots remain true wildcards (HALT permitted).
 *
 * We compute the exact set difference with the union of all independently
 * proved earlier cylinders, including three polynomial growth parents.
 * The count recursion tests actual literal source patterns, memoizes
 * branch states and never samples executions or projects quotient states.
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
assert.equal(new Set(old.map(JSON.stringify)).size,old.length);


const families=[
  {name:"CDE",mask:1,slots:[0,1,4,5]},
  {name:"CDF",mask:2,slots:[0,1,6,7]},
  {name:"CDEF",mask:4,slots:[0,1,4,5,6,7]},
];
// An action is literally HALT or a three-character write/direction/state
// instruction. The matching rules are slot-wise, not quotient-based.
function nextMask(mask,slot,action){
  for(const f of families){
    if((mask&f.mask)!==0 && f.slots.includes(slot) &&
       (action==="HALT"||!f.name.includes(action[2])))
      mask &= ~f.mask;
  }
  return mask;
}
function zeros(){return Array(8).fill(0n);}
const freeMemo=new Map(),memo=new Map();

// Count all future completions with *no older theorem available*.
// A counter is partitioned by the exact mask of closed-state families
// remaining satisfied, not merely by whether at least one succeeded.
function freeSuffix(at,mask){
  if(mask===0)return zeros();
  if(at===8){
    const x=zeros();x[mask]=1n;return x;
  }
  const key=at+":"+mask;
  if(freeMemo.has(key))return freeMemo.get(key);
  const out=zeros();
  for(const action of alphabet){
    const v=freeSuffix(at+1,nextMask(mask,at,action));
    for(let k=1;k<8;k++)out[k]+=v[k];
  }
  freeMemo.set(key,out);
  return out;
}

// Every older certificate pattern either constrains one of the remaining
// slots or is immediately universal on the present subtree. If a current
// branch has no old compatible certificate, freeSuffix counts it exactly.
function outsideOld(ids,at,mask){
  if(mask===0)return zeros();
  if(ids.some(id=>old[id].slice(at).every(v=>v===null)))return zeros();
  if(ids.length===0)return freeSuffix(at,mask);
  assert(at<8,"unmatched fully specified prior certificate");
  const key=at+":"+mask+":"+ids.join(",");
  if(memo.has(key))return memo.get(key);
  const wild=[],by=new Map();
  for(const id of ids){
    const v=old[id][at];
    if(v===null)wild.push(id);
    else{
      if(!by.has(v))by.set(v,[]);
      by.get(v).push(id);
    }
  }
  const counts=zeros();
  for(const action of alphabet){
    const next=nextMask(mask,at,action);
    if(next===0)continue;
    const sub=outsideOld([...wild,...(by.get(action)??[])].sort((a,b)=>a-b),at+1,next);
    for(let k=1;k<8;k++)counts[k]+=sub[k];
  }
  memo.set(key,counts);
  return counts;
}
const cells=outsideOld(old.map((_,i)=>i),0,7);
const fresh=cells.reduce((s,x)=>s+x,0n);
const individual=Object.fromEntries(families.map(f=>[
  f.name,cells.filter((_,mask)=>(mask&f.mask)!==0).reduce((s,x)=>s+x,0n),
]));
assert.equal(individual.CDE,867187500n);
assert.equal(individual.CDF,3375000000n);
assert.equal(individual.CDEF,4433920000n);
assert.deepEqual(cells.map(String),[
  "0","511987500","1992600000","0","2696320000",
  "355200000","1382400000","0"
]);
assert.equal(fresh,6938507500n);
const before=97539062500n,after=before+fresh,left=25n**8n-after;
assert.equal(after,104477570000n);
assert.equal(left,48110320625n);
const output={
  status:"Exact physical-table set union; source-proof acceptance must be checked independently",
  root:"1RB---_1RC---_0RD---_1LC---_------_------",
  priorAcceptedCylinderCount:old.length,
  newClosedComponents:families.map(f=>f.name),
  individualFreshRelativeToOld:Object.fromEntries(
    Object.entries(individual).map(([k,v])=>[k,String(v)])),
  disjointFreshByExactMembershipMask:Object.fromEntries(
    cells.map((value,mask)=>[mask,String(value)])),
  newCombinedAdditionalCompletions:String(fresh),
  priorNonhaltingCertifiedUnion:String(before),
  combinedCertifiedUnionIfAllLeanAccepted:String(after),
  remainingOutsideTheseTheoremsIfAccepted:String(left),
  memoStates:memo.size,
  futureMaskStates:freeMemo.size,
};
console.log(JSON.stringify(output,null,2));
