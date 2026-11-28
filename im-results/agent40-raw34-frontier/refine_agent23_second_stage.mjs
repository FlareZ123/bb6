#!/usr/bin/env node
/**
 * Exact 25-valued graph-closed refinement of the CURRENT Agent23 Raw34
 * D1=1RD source-proved second-stage frontier (28 November 2026).
 *
 * Source portfolio independently accepted:
 * - 3,087 old Raw34 nonhalting cylinders
 * - twelve assigned-HALT <=18 cylinders
 * - 153 new <=32 halting children and 1,744 oriented side-cycle children
 * - one additional F-bridge all-time growth five-hole cylinder
 *
 * We do not reconstruct those source proofs or re-run simulations. Instead
 * read Agent23's actual disjoint frontier JSON and intersect exactly the
 * still-unclassified child cylinders with the single Lean theorem
 * BB6.Agent40Raw34GraphClosed.never_of_mask.
 *
 * Every source-held child remains out of the open partition. The DAG uses
 * state-set masks and literal 25-action splits, not a quotient heuristic.
 *
 * Usage:
 *   node im-results/agent40-raw34-frontier/refine_agent23_second_stage.mjs \
 *        > /tmp/raw34-current-d1rd-graph-refinement.json
 */
import assert from "node:assert/strict";
import {readFileSync} from "node:fs";
import {dirname,join} from "node:path";
import {fileURLToPath} from "node:url";
const base=join(dirname(fileURLToPath(import.meta.url)),"../agent23-raw34-frontier");
const parent=JSON.parse(readFileSync(join(base,"D1-1RD-proof-frontier.json"),"utf8"));
const stage=JSON.parse(readFileSync(join(base,"one-step-refine.json"),"utf8"));
assert.equal(parent.parent,"1RB---_1RC---_0RD---_1LC---_------_------");
assert.equal(parent.branch,"D1=1RD");
assert.equal(parent.open.length,165);
assert.equal(stage.refined.length,3825);
assert.deepEqual(stage.counts,{halt:153,side:1744,open:1844,timeout:84});
const slots=parent.slotOrder,alphabet=parent.alphabet;
assert.deepEqual(slots,["D1","C1","B1","A1","E0","E1","F0","F1"]);
assert.equal(alphabet.length,25);
const powers=Array.from({length:9},(_,i)=>25n**BigInt(i));
const bits=n=>{let x=0;for(;n;n>>=1)x+=n&1;return x;};

const closedFamilies=["CDE","CDF","CDEF","BCDE","BCDF","BCDEF","ABCD","ABCDE","ABCDF"]
  .map((S,i)=>({
    S,flag:1<<i,
    stateMask:[...S].reduce((v,q)=>v|(1<<"ABCDEF".indexOf(q)),0),
    rows:slots.map((name,j)=>S.includes(name[0])?j:-1).filter(x=>x>=0),
  }));
const allMask=(1<<closedFamilies.length)-1;
function nextMask(mask,slot,action){
  for(const f of closedFamilies){
    if(mask&f.flag && f.rows.includes(slot) &&
      (action==="HALT"||!f.S.includes(action[2])))
      mask&=~f.flag;
  }
  return mask;
}
const memo=new Map(),nodes=[];
function value(id){return BigInt(nodes[id].graphProved);}
function make(mask,fixed){
  const key=mask+":"+fixed;
  if(memo.has(key))return memo.get(key);
  const mass=powers[8-bits(fixed)];
  const witness=closedFamilies.find(f=>mask&f.flag && f.rows.every(i=>fixed&(1<<i)));
  let node;
  if(witness){
    node={type:"closed_control",S:witness.S,stateMask:witness.stateMask,
      theorem:"BB6.Agent40Raw34GraphClosed.never_of_mask",
      mass:String(mass),graphProved:String(mass)};
  }else if(!mask){
    node={type:"outside_graph_portfolio",mass:String(mass),graphProved:"0"};
  }else{
    const choices=slots.map((_,i)=>i).filter(i=>
      !(fixed&(1<<i)) && closedFamilies.some(f=>mask&f.flag&&f.rows.includes(i)));
    assert(choices.length);
    choices.sort((a,b)=>closedFamilies.filter(f=>mask&f.flag&&f.rows.includes(b)).length-
      closedFamilies.filter(f=>mask&f.flag&&f.rows.includes(a)).length || a-b);
    const slot=choices[0],successors=[];
    let proved=0n;
    for(const action of alphabet){
      const id=make(nextMask(mask,slot,action),fixed|(1<<slot));
      successors.push(id);proved+=value(id);
    }
    assert(proved<=mass);
    node={type:"split",slot:slots[slot],slotIndex:slot,cases:successors,
      mass:String(mass),graphProved:String(proved)};
  }
  const id=nodes.length;
  nodes.push(node);memo.set(key,id);return id;
}
const already=new Map([
  ["halt","97265625"],
  ["side","934375000"]
]);
const sourceGrowth={
  parentIndex:68,slot:"F1",action:"1LD",
  table:"1RB---_1RC---_0RD0RF_1LC1RD_------_---1LD",
  source:"BB6.Agent23Raw34TripleSweepGrowthF.never",
};
let accounted=0n,graph=0n,outside=0n;
const roots=[];
const perKind={open:{n:0,graph:0n,outside:0n},timeout:{n:0,graph:0n,outside:0n}};
let totalGrowth=0n;
for(const entry of stage.refined){
  if(entry.kind==="halt"||entry.kind==="side")continue;
  if(entry.parentIndex===sourceGrowth.parentIndex &&
     entry.slot===sourceGrowth.slot &&entry.action===sourceGrowth.action){
    assert.equal(entry.kind,"timeout");
    totalGrowth+=BigInt(entry.mass);
    continue;
  }
  assert(entry.kind==="open"||entry.kind==="timeout");
  const prefix=parent.open[entry.parentIndex].decisions;
  assert(prefix!==undefined);
  const actions=Array(8).fill(null);
  for(let i=0;i<prefix.length;i++)actions[i]=prefix[i];
  const slot=slots.indexOf(entry.slot);
  assert(slot>=0&&actions[slot]===null);
  actions[slot]=entry.action;
  let mask=allMask,fixed=0;
  for(let i=0;i<8;i++){
    const action=actions[i];
    if(action===null)continue;
    assert(alphabet.includes(action));
    fixed|=1<<i;mask=nextMask(mask,i,action);
  }
  const mass=powers[8-bits(fixed)];
  assert.equal(mass,BigInt(entry.mass));
  const node=make(mask,fixed),extra=value(node);
  assert(extra<=mass);
  graph+=extra;outside+=mass-extra;accounted+=mass;
  perKind[entry.kind].n++;
  perKind[entry.kind].graph+=extra;
  perKind[entry.kind].outside+=mass-extra;
  roots.push({parentIndex:entry.parentIndex,slot:entry.slot,action:entry.action,
    earlierStatus:entry.kind,
    sourceMass:String(mass),graphProved:String(extra),
    outsideGraph:String(mass-extra),dagRef:node});
}
assert.equal(totalGrowth,9765625n);
assert.equal(roots.length,1927);
assert.equal(accounted,1390234375n);
assert.equal(graph,879004125n);
assert.equal(outside,511230250n);
assert.equal(nodes.length,63);
const oldAndAgent23=4713281250n;
const newAcceptedAndGraph=oldAndAgent23+graph;
assert.equal(newAcceptedAndGraph,5592285375n);
assert.equal(newAcceptedAndGraph+outside,6103515625n);
console.log(JSON.stringify({
  status:"exact physical-table refinement, supported by original-source accepted independent theorems; aggregate Lean Cover not asserted",
  parent:parent.parent,branch:parent.branch,
  sourceFrontier:"../agent23-raw34-frontier/one-step-refine.json",
  sourceOldFrontier:"../agent23-raw34-frontier/D1-1RD-proof-frontier.json",
  oldAndAgent23ProvedBothHaltAndDiverge:String(oldAndAgent23),
  newGraphSourceTheorem:"BB6.Agent40Raw34GraphClosed.never_of_mask",
  newlyGraphProvedDisjointFromOldAndAgent23:String(graph),
  combinedKnownPhysicalTables:String(newAcceptedAndGraph),
  physicalTablesOutsideThisCombinedPortfolio:String(outside),
  totalBranchPhysicalTables:"6103515625",
  excludedPriorGrowthSource:sourceGrowth,
  excludedPriorGrowthPhysicalMass:String(totalGrowth),
  testedOpenSourceChildCylinders:roots.length,
  decisionDagNodes:nodes.length,
  byOldStatus:Object.fromEntries(
    Object.entries(perKind).map(([k,v])=>[k,{
      n:v.n,graphProved:String(v.graph),outside:String(v.outside)
    }])),
  alphabet,slots,
  families:closedFamilies.map(({S,stateMask,rows})=>({
    S,stateMask,requiredRows:rows.map(i=>slots[i])
  })),
  roots,nodes,
},null,2));
