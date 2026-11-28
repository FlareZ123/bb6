#!/usr/bin/env node
/**
 * The exact, source-labeled graph-closure refinement of Agent23's
 * D1=1RD Raw34 165-open-cylinder frontier.
 *
 * This does NOT rebuild the 3,087 previously accepted Lean certificates,
 * re-run their proof enumeration, or mistake a physical table for a
 * canonical quotient obligation. We reuse Agent23's disjoint prefix
 * frontier as input; its original 124 covered leaves remain untouched.
 *
 * Every covered terminal identifies one finite control set S, the state
 * bitmask, and the source proposition that must justify it:
 *
 *   BB6.Agent40Raw34GraphClosed.never_of_mask
 *
 * Branching is exact over all 25 physical actions including HALT.
 * This output is a finite combinatorial certificate *candidate*, not
 * itself a kernel-accepted graph-frontier composition theorem.
 *
 * Usage:
 *   node im-results/agent40-raw34-frontier/refine_agent23_d1rd.mjs \
 *      > /tmp/raw34-d1-1rd-graph-frontier.json
 */
import assert from "node:assert/strict";
import {readFileSync} from "node:fs";
import {dirname,join} from "node:path";
import {fileURLToPath} from "node:url";

const repoRel="../agent23-raw34-frontier/D1-1RD-proof-frontier.json";
const input=JSON.parse(readFileSync(join(dirname(fileURLToPath(import.meta.url)),repoRel),"utf8"));
assert.equal(input.parent,"1RB---_1RC---_0RD---_1LC---_------_------");
assert.equal(input.branch,"D1=1RD");
assert.equal(input.summary.provedNeverHalting,"3320312500");
assert.equal(input.summary.notCoveredByTheseProofs,"2783203125");
assert.equal(input.open.length,165);
assert.equal(input.sourceProofs,3087);

const names=["D1","C1","B1","A1","E0","E1","F0","F1"];
const alphabet=input.alphabet;
assert.equal(alphabet.length,25);
assert.equal(new Set(alphabet).size,25);
assert(alphabet.includes("HALT"));
const families=[
  "CDE","CDF","CDEF","BCDE","BCDF","BCDEF",
  "ABCD","ABCDE","ABCDF",
].map((stateSet,i)=>({
  stateSet,flag:1<<i,
  controlMask:[...stateSet].reduce((mask,s)=>mask|(1<<("ABCDEF".indexOf(s))),0),
  requiredSlots:names.map((name,k)=>stateSet.includes(name[0])?k:-1).filter(k=>k>=0)
}));
// The four fixed Raw34 transitions A0→B,B0→C,C0→D,D0→C
// are ordinary. Each S includes D and is closed under those transitions
// whenever their source state is in S.
for(const {stateSet} of families){
  assert(stateSet.includes("C")&&stateSet.includes("D"));
  for(const [a,b] of [["A","B"],["B","C"],["C","D"],["D","C"]])
    if(stateSet.includes(a))assert(stateSet.includes(b));
}

const allFlags=(1<<families.length)-1;
const powers=Array.from({length:9},(_,n)=>25n**BigInt(n));
const bitcount=x=>{let n=0;for(;x;x>>=1)n+=x&1;return n;};
function refineMask(mask,slot,action){
  for(const f of families){
    if((mask&f.flag)!==0&&f.requiredSlots.includes(slot)&&
       (action==="HALT"||!f.stateSet.includes(action[2])))
      mask &= ~f.flag;
  }
  return mask;
}
const memo=new Map(),nodes=[];
function countOf(id){const n=nodes[id];return [BigInt(n.covered),BigInt(n.notYetCovered)];}
function solve(mask,fixed){
  const key=mask+":"+fixed;
  if(memo.has(key))return memo.get(key);
  const mass=powers[8-bitcount(fixed)];
  const exact=families.find(f=>(mask&f.flag)!==0&&
    f.requiredSlots.every(i=>(fixed&(1<<i))!==0));
  let node;
  if(exact){
    node={
      kind:"graph-covered",
      states:exact.stateSet,
      stateMask:exact.controlMask,
      sourceTheorem:"BB6.Agent40Raw34GraphClosed.never_of_mask",
      sourceHypotheses:"compatible Raw34 root; all S rows fixed ordinary and with next∈S",
      freeSlots:8-bitcount(fixed),
      covered:String(mass),
      notYetCovered:"0"
    };
  }else if(mask===0){
    node={kind:"not-covered-by-these-certificates",
      freeSlots:8-bitcount(fixed),covered:"0",notYetCovered:String(mass)};
  }else{
    const candidates=names.map((_,i)=>i).filter(i=>
      (fixed&(1<<i))===0 &&
      families.some(f=>(mask&f.flag)!==0&&f.requiredSlots.includes(i)));
    assert(candidates.length>0,"no decisive missing graph slot");
    // Splitting highly constrained transitions first maximizes early pruning;
    // exact counts are independent of this heuristic.
    candidates.sort((a,b)=>
      families.filter(f=>(mask&f.flag)&&f.requiredSlots.includes(b)).length-
      families.filter(f=>(mask&f.flag)&&f.requiredSlots.includes(a)).length||a-b);
    const slot=candidates[0],cases=[];
    let covered=0n,notYetCovered=0n;
    for(const action of alphabet){
      const ref=solve(refineMask(mask,slot,action),fixed|(1<<slot));
      const [c,n]=countOf(ref);
      cases.push(ref);
      covered+=c;notYetCovered+=n;
    }
    assert.equal(covered+notYetCovered,mass,
      "invalid physical 25-way split");
    node={kind:"split",slot:names[slot],index:slot,cases,
          covered:String(covered),notYetCovered:String(notYetCovered)};
  }
  const index=nodes.length;
  nodes.push(node);memo.set(key,index);
  return index;
}

const roots=[];let totalCovered=0n,totalOpen=0n;
let zeroClosureRoots=0,allClosureRoots=0,partialClosureRoots=0;
for(let i=0;i<input.open.length;i++){
  const cylinder=input.open[i];
  const decisions=Array(8).fill(null);
  for(let slot=0;slot<cylinder.decisions.length;slot++)
    decisions[slot]=cylinder.decisions[slot];
  assert.equal(decisions[0],"1RD");
  let fixed=0,mask=allFlags;
  for(let slot=0;slot<8;slot++){
    const action=decisions[slot];
    if(action===null)continue;
    assert(alphabet.includes(action),"unknown source physical action");
    fixed|=1<<slot;
    mask=refineMask(mask,slot,action);
  }
  assert.equal(BigInt(cylinder.mass),powers[8-bitcount(fixed)],
    "inconsistent predecessor subcube mass");
  const entry=solve(mask,fixed);
  const [covered,notYetCovered]=countOf(entry);
  assert.equal(covered+notYetCovered,BigInt(cylinder.mass));
  if(covered===0n)zeroClosureRoots++;
  else if(notYetCovered===0n)allClosureRoots++;
  else partialClosureRoots++;
  roots.push({
    originalOpenIndex:i,
    decisions,
    originalMass:cylinder.mass,
    explicitHalts:cylinder.explicitHalts??[],
    dagRef:entry,
    graphCovered:String(covered),
    notYetCovered:String(notYetCovered),
  });
  totalCovered+=covered;totalOpen+=notYetCovered;
}
assert.equal(totalCovered+totalOpen,2783203125n);
assert.equal(totalCovered,1636963000n);
assert.equal(totalOpen,1146240125n);
assert.equal(nodes.length,92);
assert.deepEqual([zeroClosureRoots,allClosureRoots,partialClosureRoots],[12,0,153]);
assert.equal(3320312500n+totalCovered+totalOpen,6103515625n);

const out={
  status:"exact finite physical partition; original source Lean graph theorem acceptance separate",
  parent:input.parent,branch:input.branch,
  predecessorManifest:repoRel,
  sourceGraphTheorem:"BB6.Agent40Raw34GraphClosed.never_of_mask",
  provenNeverHaltsInPredecessor:"3320312500",
  graphClosedNewSubcubes:String(totalCovered),
  totalClosedIfSourceAccepted:String(3320312500n+totalCovered),
  notYetClassifiedByThisNonhaltingPortfolio:String(totalOpen),
  originalOpenRoots:input.open.length,
  graphFullyExcludesRoots:zeroClosureRoots,
  graphPartiallyRefinesRoots:partialClosureRoots,
  graphEntirelyCoversRoots:allClosureRoots,
  disjointDagNodeCount:nodes.length,
  slotOrder:names,alphabet,
  families:families.map(({stateSet,controlMask,requiredSlots})=>({
    stateSet,controlMask,requiredSlots:requiredSlots.map(i=>names[i])
  })),
  roots,nodes
};
console.log(JSON.stringify(out,null,2));
