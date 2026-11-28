#!/usr/bin/env node
/**
 * Exact source split plan for the Raw34 F subparent D1=0LF, F0=0LA.
 *
 * The plan exhaustively follows the genuine first-undefined query through
 * six assigned free transitions.  Side cycles use the original fast checker;
 * finite halts use finiteHaltCheck; every unresolved leaf remains an explicit
 * literal residual row.  Raw34Plan.check_explicit_residual turns the Boolean
 * plan check into a source-level Cover theorem.
 */
import assert from "node:assert/strict";
import {mkdirSync,writeFileSync} from "node:fs";
import {join} from "node:path";
const args=process.argv.slice(2);
function opt(name,def){const i=args.indexOf(name);return i<0?def:args[i+1];}
const output=opt("--output","/tmp/a50-raw34-pair-plan");
mkdirSync(output,{recursive:true});

const alphabet=["HALT"];
for(const w of "01")for(const d of "LR")for(const q of "ABCDEF")alphabet.push(w+d+q);
const root=[21,0,22,0,11,0,16,0,0,0,0,0];
const dCode=alphabet.indexOf("0LF")+1;
const f0Code=alphabet.indexOf("0LA")+1;
assert.equal(dCode,7);assert.equal(f0Code,2);
const parentCodes=root.slice();parentCodes[7]=dCode;parentCodes[10]=f0Code;

function trace(p,cap=100){
 let q=0,h=0,ones=new Set(),hist=[];
 for(let t=0;t<=cap;t++){
  hist.push({q,h,ones:new Set(ones)});
  const slot=2*q+(ones.has(h)?1:0),action=p[slot];
  if(action===0||action===1)return {kind:action===0?"unknown":"halt",slot,hist,t};
  const v=action-2;v>=12?ones.add(h):ones.delete(h);q=v%6;h+=v%12>=6?1:-1;
 }
 return {kind:"long",hist};
}
function sideWitness(hist,maxEntry=60,maxPeriod=30){
 const max=Math.min(hist.length,maxEntry);
 for(let entry=0;entry<max;entry++)
 for(let j=entry+1;j<Math.min(hist.length,entry+maxPeriod+1);j++){
  const a=hist[entry],b=hist[j],delta=b.h-a.h;if(a.q!==b.q)continue;
  for(const right of [true,false]){
   if(right?delta<0:delta>0)continue;
   let boundary=right?Infinity:-Infinity;
   for(let t=entry;t<j;t++)
    boundary=right?Math.min(boundary,hist[t].h):Math.max(boundary,hist[t].h);
   let ok=true;
   for(const x of a.ones)
    if((right?x>=boundary:x<=boundary)&&!b.ones.has(x+delta)){ok=false;break;}
   if(!ok)continue;
   for(const y of b.ones)
    if((right?y-delta>=boundary:y-delta<=boundary)&&!a.ones.has(y-delta)){ok=false;break;}
   if(ok)return {entry,period:j-entry,right,boundary};
  }
 }
 return null;
}
function leanSlot(slot){
 const q=Math.floor(slot/2),bit=(slot&1)===1;
 return `(⟨${q}, by decide⟩, ${bit})`;
}
function leanInt(x){return x<0?`(${x})`:String(x);}

const p=parentCodes.slice(),nodes=[],rows=[],stats={};
function inc(k){stats[k]=(stats[k]??0)+1;}
function pushNode(text){const i=nodes.length;nodes.push(text);return i;}
function residual(depth,kind){
 const j=rows.length;rows.push(p.slice());inc(kind+depth);return pushNode(`.residual ${j}`);
}
function build(depth){
 const r=trace(p),w=sideWitness(r.hist);
 if(w){
  inc("cycle"+depth);
  return pushNode(`.leaf (.side ${w.entry} ${w.period} ${w.right} ${leanInt(w.boundary)})`);
 }
 if(r.kind==="halt"){
  assert(r.t+1<=128);inc("halt"+depth);
  return pushNode(`.leaf (.halt ${r.t})`);
 }
 if(r.kind==="long"){
  const rr=trace(p,1000),ww=sideWitness(rr.hist,500,200);
  if(ww){
   inc("extendedCycle"+depth);
   return pushNode(`.leaf (.side ${ww.entry} ${ww.period} ${ww.right} ${leanInt(ww.boundary)})`);
  }
  return residual(depth,"longResidual");
 }
 if(depth>=6)return residual(depth,"openResidual");
 assert.equal(p[r.slot],0);
 const children=[];
 for(let code=1;code<=25;code++){
  p[r.slot]=code;children.push(build(depth+1));
 }
 p[r.slot]=0;
 return pushNode(`.split ${leanSlot(r.slot)} [${children.join(",")}]`);
}
const rootIndex=build(2);
assert.equal(nodes.length,39676);
assert.equal(rows.length,12356);
assert.deepEqual(stats,{
 halt3:1,cycle3:12,halt4:12,cycle4:144,halt5:143,cycle5:1944,
 halt6:1431,cycle6:21688,openResidual6:11571,longResidual6:732,
 longResidual5:52,extendedCycle6:353,extendedCycle5:5,longResidual4:1
});
assert.equal(rootIndex,nodes.length-1);

const source=`import Raw34Plan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent50Raw34PairDepth6
open BB6Coverage BB6.Agent50Raw34Plan

def parent : PartialMachine := table [${parentCodes.join(",")}]
def residualRows : List (List Nat) := [
${rows.map(r=>`  [${r.join(",")}]`).join(",\n")}
]
def nodes : Array Node := #[
${nodes.map(n=>`  ${n}`).join(",\n")}
]
theorem node_count : nodes.size = ${nodes.length} := by decide
theorem residual_count : residualRows.length = ${rows.length} := by decide
theorem checked : check nodes residualRows 128 5 ${rootIndex} parent = true := by
  decide +kernel
theorem cover :
    Cover (fun m => DecidedBelow 128 m ∨ ExplicitResidual residualRows m) parent :=
  check_explicit_residual nodes residualRows 128 5 ${rootIndex} parent checked
#print axioms node_count
#print axioms residual_count
#print axioms checked
#print axioms cover
end BB6.Agent50Raw34PairDepth6
`;
writeFileSync(join(output,"Raw34PairDepth6Plan.lean"),source);
writeFileSync(join(output,"residualRows.json"),JSON.stringify(rows)+"\\n");
const report={
 parentCodes,d1:"0LF",f0:"0LA",physicalParentCompletions:String(25n**6n),
 nodeCount:nodes.length,residualCount:rows.length,rootIndex,
 bound:128,maxAssignedFreeTransitions:6,stats,
 theorem:"BB6.Agent50Raw34PairDepth6.cover",
 interpretation:"Every completion of this literal Raw34 subparent is DecidedBelow 128 or extends one of the explicit residualRows; Lean checker is authoritative."
};
writeFileSync(join(output,"manifest.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify(report,null,2));
