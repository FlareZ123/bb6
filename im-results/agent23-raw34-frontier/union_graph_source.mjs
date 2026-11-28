#!/usr/bin/env node
/**
 * Raw34 D1=1RD exact 25-outcome, certificate-sensitive physical union.
 *
 * Original-source Lean certified components:
 * - 3087 Agent50 old cylinders (165 disjoint residual prefix cylinders);
 * - 12 original-source finite-halting leaves;
 * - 1744 source-checked side cycles + 153 source-checked halters;
 * - one F-bridge growth all-time nonhalting cylinder;
 * - 149+539 second-depth side cycles and 10+58 second-depth halters;
 * - Agent40's source theorem never_of_mask, applied to all ten graph
 *   closed-control state sets other than CD/BCD (already in old source).
 *
 * All physical-table unions and 25-ary residual counts below are pure
 * finite combinatorial arithmetic. This is NOT an aggregate Lean Cover.
 * Run: node union_graph_source.mjs
 */
import assert from "node:assert/strict";
import {readFileSync} from "node:fs";
import {dirname,resolve} from "node:path";
import {fileURLToPath} from "node:url";
const here=dirname(fileURLToPath(import.meta.url));
const input=name=>JSON.parse(readFileSync(resolve(here,name),"utf8"));
const M=input("D1-1RD-proof-frontier.json");
const N=input("one-step-refine.json");
const D=input("depth2-C1-0RF.json");
const H=input("depth2-highmass-other.json");
const names=M.slotOrder,alphabet=M.alphabet,slots=[7,5,3,1,8,9,10,11];
assert.deepEqual(names,["D1","C1","B1","A1","E0","E1","F0","F1"]);
assert.equal(alphabet.length,25);
assert.equal(M.summary.provedNeverHalting,"3320312500");
assert.equal(M.open.length,165);
assert.equal(N.refined.length,3825);
assert.deepEqual(N.counts,{halt:153,side:1744,open:1844,timeout:84});
assert.equal(D.all.length,250);
assert.equal(H.records.length,1450);
const pw=Array.from({length:9},(_,i)=>25n**BigInt(i));
const bits=v=>{let n=0;for(;v;v>>=1)n+=v&1;return n;};
const key=(i,slot,act)=>i+"/"+slot+"/"+act;

function graphEngine(stateSets){
 const fam=stateSets.map((set,i)=>({
  set,flag:1<<i,
  req:names.map((name,k)=>set.includes(name[0])?k:-1).filter(k=>k>=0)
 }));
 assert(fam.every(f=>f.set.includes("C")&&f.set.includes("D")));
 for(const f of fam)for(const [a,b] of [["A","B"],["B","C"],["C","D"],["D","C"]])
  if(f.set.includes(a))assert(f.set.includes(b));
 const all=(1<<fam.length)-1,cache=new Map();
 function update(mask,slot,action){
  for(const f of fam)
   if((mask&f.flag)&&f.req.includes(slot)&&
      (action==="HALT"||!f.set.includes(action[2])))
    mask&=~f.flag;
  return mask;
 }
 function count(mask,fixed){
  if(!mask)return 0n;
  const mass=pw[8-bits(fixed)];
  if(fam.some(f=>(mask&f.flag)&&f.req.every(k=>(fixed&(1<<k))!==0)))
   return mass;
  const memoKey=mask+":"+fixed;
  if(cache.has(memoKey))return cache.get(memoKey);
  const slotsLeft=names.map((_,i)=>i).filter(i=>
    !(fixed&(1<<i))&&fam.some(f=>(mask&f.flag)&&f.req.includes(i)));
  assert(slotsLeft.length);
  slotsLeft.sort((a,b)=>
    fam.filter(f=>(mask&f.flag)&&f.req.includes(b)).length-
    fam.filter(f=>(mask&f.flag)&&f.req.includes(a)).length||a-b);
  const next=slotsLeft[0];
  let covered=0n;
  for(const action of alphabet)
   covered+=count(update(mask,next,action),fixed|(1<<next));
  assert(covered<=mass);
  cache.set(memoKey,covered);
  return covered;
 }
 function decisions(dec){
  assert.equal(dec.length,8);
  let mask=all,fixed=0;
  for(let i=0;i<8;i++){
   const a=dec[i];
   if(a===null)continue;
   assert(alphabet.includes(a));
   fixed|=1<<i;mask=update(mask,i,a);
  }
  return count(mask,fixed);
 }
 function encoded(code){
  assert.equal(code.length,12);
  let mask=all,fixed=0;
  for(let i=0;i<8;i++){
   const v=code[slots[i]];
   if(v===0)continue;
   assert(Number.isInteger(v)&&v>=1&&v<=25);
   const a=v===1?"HALT":alphabet[v-1];
   fixed|=1<<i;mask=update(mask,i,a);
  }
  return count(mask,fixed);
 }
 return {decisions,encoded,cache};
}

const graph9=graphEngine(["CDE","CDF","CDEF","BCDE","BCDF","BCDEF","ABCD","ABCDE","ABCDF"]);
const graph10=graphEngine(["CDE","CDF","CDEF","BCDE","BCDF","BCDEF","ABCD","ABCDE","ABCDF","ABCDEF"]);
const first=Array.from({length:165},()=>[]);
for(const x of N.refined)first[x.parentIndex].push(x);
const firstSlot=new Map(N.refined.map(x=>[x.parentIndex+"/"+x.action,x.slot]));
const second=new Map();
function add(k,record){if(!second.has(k))second.set(k,[]);second.get(k).push(record);}
for(const x of D.all)add(key(x.parentIndex,x.firstSlot,x.firstAction),x);
for(const x of H.records){
 const s=firstSlot.get(x.sourceParentIndex+"/"+x.first);
 assert(s,"missing first queried slot");
 add(key(x.sourceParentIndex,s,x.first),x);
}
assert.equal(second.size,68);
for(const [k,rows] of second){
 assert.equal(rows.length,25,k);
 const actions=rows.map(x=>x.secondAction??x.second);
 assert.equal(new Set(actions).size,25);
 assert.deepEqual([...actions].sort(),[...alphabet].sort());
}
const byC={};
let initial12=0n,oneStep=0n,bridge=0n,twoStep=0n,graph9Only=0n,graph10Only=0n;
let firstWithoutDepth2=0,withDepth2=0,graphPhysicalLeafRows=0;
for(let i=0;i<165;i++){
 const L=M.open[i],children=first[i];
 assert.equal(L.decisions[0],"1RD");
 if(!children.length){
  initial12+=BigInt(L.mass);
  continue;
 }
 assert.equal(children.length,25,i);
 assert.equal(new Set(children.map(x=>x.action)).size,25);
 assert.equal(children.reduce((s,x)=>s+BigInt(x.mass),0n),BigInt(L.mass));
 for(const child of children){
  const mass=BigInt(child.mass),kind=child.kind;
  assert(["side","halt","open","timeout"].includes(kind));
  if(kind==="side"||kind==="halt"){oneStep+=mass;continue;}
  // The F-bridge nonhalt 4n+3 pump has F1=1LD as first unknown.
  if(i===68&&child.slot==="F1"&&child.action==="1LD"){
   assert.equal(mass,9765625n);
   bridge+=mass;
   continue;
  }
  const c1=L.decisions[1],k=key(i,child.slot,child.action);
  if(!byC[c1])byC[c1]={r9:0n,r10:0n};
  const deep=second.get(k);
  if(!deep){
   firstWithoutDepth2++;
   const path=Array(8).fill(null);
   L.decisions.forEach((x,j)=>{path[j]=x;});
   const slot=names.indexOf(child.slot);
   assert(slot>=0&&path[slot]===null);
   path[slot]=child.action;
   const g9=graph9.decisions(path),g10=graph10.decisions(path);
   assert(g10>=g9);
   graph9Only+=g9;graph10Only+=g10;
   byC[c1].r9+=mass-g9;byC[c1].r10+=mass-g10;
   graphPhysicalLeafRows++;
  }else{
   withDepth2++;
   assert.equal(deep.reduce((s,x)=>s+BigInt(x.mass),0n),mass);
   const childCodes=x=>{
    const d=Array(8).fill(null);
    for(let j=0;j<8;j++)d[j]=x.codes[slots[j]]===0?null:
      x.codes[slots[j]]===1?"HALT":alphabet[x.codes[slots[j]]-1];
    for(let j=0;j<L.decisions.length;j++)
      if(L.decisions[j]!==null)assert.equal(d[j],L.decisions[j]);
    assert.equal(d[names.indexOf(child.slot)],child.action);
    return d;
   };
   for(const x of deep){
    childCodes(x);
    const m=BigInt(x.mass),q=x.kind??x.result?.kind;
    assert(["side","halt","open","timeout"].includes(q));
    if(q==="side"||q==="halt"){twoStep+=m;continue;}
    const g9=graph9.encoded(x.codes),g10=graph10.encoded(x.codes);
    assert(g10>=g9);
    graph9Only+=g9;graph10Only+=g10;
    byC[c1].r9+=m-g9;byC[c1].r10+=m-g10;
    graphPhysicalLeafRows++;
   }
  }
 }
}
assert.equal(initial12,351562500n);
assert.equal(oneStep,1031640625n);
assert.equal(bridge,9765625n);
assert.equal(twoStep,295312500n);
assert.equal(withDepth2,68);
assert.equal(firstWithoutDepth2,1859);
const earlier=3320312500n,newCertificates=initial12+oneStep+bridge+twoStep;
const sourceTotal=earlier+newCertificates;
assert.equal(sourceTotal,5008593750n);
const graph9Total=sourceTotal+graph9Only,graph10Total=sourceTotal+graph10Only;
const branch=6103515625n,open9=branch-graph9Total,open10=branch-graph10Total;
assert.equal(graph9Only,657006125n);
assert.equal(graph10Only,984524333n);
assert.equal(open9,437915750n);
assert.equal(open10,110397542n);
const output={
 status:"Exact finite physical-table arithmetic; NOT a Lean-consumed aggregate Cover",
 originalRoot:"1RB---_1RC---_0RD---_1LC---_------_------",
 branch:"D1=1RD",
 total:branch.toString(),
 sourceCertified:{
  old:earlier.toString(),new12:initial12.toString(),
  newOneStep:oneStep.toString(),newFBridge:bridge.toString(),
  newSecondStep:twoStep.toString(),total:sourceTotal.toString()
 },
 graphClosed9:{
  source:"BB6.Agent40Raw34GraphClosed.never_of_mask",
  newBeyondTheseSources:graph9Only.toString(),
  aggregateClassified:graph9Total.toString(),
  remaining:open9.toString()
 },
 graphClosed10IncludingNoHalt:{
  source:"BB6.Agent40Raw34GraphClosed.never_of_mask with S=ABCDEF added",
  newBeyondTheseSources:graph10Only.toString(),
  additionalNoHaltBeyond9:(graph10Only-graph9Only).toString(),
  aggregateClassified:graph10Total.toString(),
  remaining:open10.toString()
 },
 refinementNodes:{oldOpenLeaves:165,firstStageChildren:3825,
  secondDepthParents:withDepth2,firstStageResidualWithoutDepth2:firstWithoutDepth2,
  residualGraphDAGCubeVisits:graphPhysicalLeafRows,
  graph9MemoStates:graph9.cache.size,graph10MemoStates:graph10.cache.size},
 residualByC1:Object.fromEntries(Object.entries(byC).map(([k,v])=>[
  k,{afterGraph9:v.r9.toString(),afterGraph10:v.r10.toString()}]))
};
console.log(JSON.stringify(output,null,2));
