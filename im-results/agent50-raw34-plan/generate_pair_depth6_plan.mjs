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
const rootShards=args.includes("--root-shards");
mkdirSync(output,{recursive:true});

const alphabet=["HALT"];
for(const w of "01")for(const d of "LR")for(const q of "ABCDEF")alphabet.push(w+d+q);
// BB6Coverage.choices is HALT followed by state-major
// 0Lq,0Rq,1Lq,1Rq for q=A..F.  Plan child arrays must use that order
// even though physical source codes themselves are write/direction-major.
const choiceCodes=[1];
for(let q=0;q<6;q++)choiceCodes.push(2+q,8+q,14+q,20+q);
assert.equal(choiceCodes.length,25);
const root=[21,0,22,0,11,0,16,0,0,0,0,0];
const d1Action=opt("--d1","0LF");
const f0Action=opt("--f0","0LA");
assert(["0LA","0LD"].includes(f0Action),"currently source-gated for F0=0LA or 0LD");
assert.equal(d1Action,"0LF","currently source-gated for D1=0LF");
const dCode=alphabet.indexOf(d1Action)+1;
const f0Code=alphabet.indexOf(f0Action)+1;
assert.equal(dCode,7);assert(f0Code>0);
const parentCodes=root.slice();parentCodes[7]=dCode;parentCodes[10]=f0Code;
const namespaceName=f0Action==="0LA"
  ?"BB6.Agent50Raw34PairDepth6"
  :"BB6.Agent40Raw34PairD1LF_F0LDDepth6";
const easyMode=f0Action==="0LD";
const contiguousCodes=[21,14,22,21,11,0,16,7,0,0,5,14];
const alternatingCodes=[21,7,22,20,11,0,16,7,0,0,5,14];
const sameCodes=(a,b)=>a.length===b.length&&a.every((x,i)=>x===b[i]);
const certLeaf=cert=>easyMode?`.leaf (.base (${cert}))`:`.leaf (${cert})`;

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
const closedFiveStates=new Set([0,1,2,3,5]);
function closesWithoutE(p){
 for(const q of closedFiveStates)for(const bit of [0,1]){
  const action=p[2*q+bit];
  if(action<=1)return false;
  if(!closedFiveStates.has((action-2)%6))return false;
 }
 return true;
}

const p=parentCodes.slice(),nodes=[],rows=[],stats={};
let topChildren=null,topSlot=null;
function inc(k){stats[k]=(stats[k]??0)+1;}
function pushNode(text){const i=nodes.length;nodes.push(text);return i;}
function residual(depth,kind){
 const j=rows.length;rows.push(p.slice());inc(kind+depth);return pushNode(`.residual ${j}`);
}
function build(depth){
 if(easyMode&&sameCodes(p,contiguousCodes)){
  inc("contiguousGrowth"+depth);return pushNode(".leaf .contiguous");
 }
 if(easyMode&&sameCodes(p,alternatingCodes)){
  inc("alternatingGrowth"+depth);return pushNode(".leaf .alternating");
 }
 const r=trace(p),w=sideWitness(r.hist);
 if(w){
  inc("cycle"+depth);
  return pushNode(certLeaf(`.side ${w.entry} ${w.period} ${w.right} ${leanInt(w.boundary)}`));
 }
 if(r.kind==="halt"){
  assert(r.t+1<=128);inc("halt"+depth);
  return pushNode(certLeaf(`.halt ${r.t}`));
 }
 if(r.kind==="long"){
  const rr=trace(p,1000),ww=sideWitness(rr.hist,500,200);
  if(ww){
   inc("extendedCycle"+depth);
   return pushNode(certLeaf(`.side ${ww.entry} ${ww.period} ${ww.right} ${leanInt(ww.boundary)}`));
  }
  if(f0Action==="0LD"&&closesWithoutE(p)){
   inc("closed"+depth);
   return pushNode(certLeaf(".closed 0 [0,1,2,3,5]"));
  }
  return residual(depth,"longResidual");
 }
 if(depth>=6)return residual(depth,"openResidual");
 assert.equal(p[r.slot],0);
 const children=[];
 for(const code of choiceCodes){
  p[r.slot]=code;children.push(build(depth+1));
 }
 p[r.slot]=0;
 if(depth===2){topChildren=children.slice();topSlot=r.slot;}
 return pushNode(`.split ${leanSlot(r.slot)} [${children.join(",")}]`);
}
const rootIndex=build(2);
const expected=f0Action==="0LA"?{
 nodes:39676,rows:12356,stats:{
  halt3:1,cycle3:12,halt4:12,cycle4:144,halt5:143,cycle5:1944,
  halt6:1431,cycle6:21688,openResidual6:11571,longResidual6:732,
  longResidual5:52,extendedCycle6:353,extendedCycle5:5,longResidual4:1
 }
}:{
 nodes:16976,rows:4274,stats:{
  halt3:1,cycle3:17,halt4:7,halt5:67,cycle5:1002,
  halt6:604,cycle6:10155,longResidual6:40,openResidual6:4234,
  cycle4:101,extendedCycle6:25,closed6:42,
  contiguousGrowth5:1,alternatingGrowth5:1
 }
};
assert.equal(nodes.length,expected.nodes);
assert.equal(rows.length,expected.rows);
assert.deepEqual(stats,expected.stats);
assert.equal(rootIndex,nodes.length-1);


if(rootShards){
 assert(easyMode,"root sharding is currently implemented for the F0=0LD easy plan");
 assert(topChildren&&topChildren.length===25);
 assert.equal(topSlot,11);
 assert.equal(topChildren.at(-1),nodes.length-2);

 const dataModule="Raw34PairD1LF_F0LDDepth6Data";
 const dataNs="BB6.Agent40Raw34PairD1LF_F0LDDepth6Data";
 const dataSource=`import Raw34Plan
import Raw34QuadraticPairGrowth
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace ${dataNs}
open BB6Coverage BB6.Agent50Raw34Plan

inductive EasyCert where
  | base (cert : Cert)
  | contiguous
  | alternating

def easyCheck (p : PartialMachine) : EasyCert → Bool
  | .base cert => certCheck 128 p cert
  | .contiguous => sameTable p BB6.Agent40Raw34PairQuadratic.contiguous
  | .alternating => sameTable p BB6.Agent40Raw34PairQuadratic.alternating

abbrev EasyNode := PlanNode EasyCert
def parent : PartialMachine := table [${parentCodes.join(",")}]
def rootSlot : Slot := ${leanSlot(topSlot)}
def residualRows : List (List Nat) := [
${rows.map(r=>`  [${r.join(",")}]`).join(",\n")}
]
abbrev Good (m : Machine) : Prop :=
  DecidedBelow 128 m ∨ ExplicitResidual residualRows m

theorem easy_sound (p : PartialMachine) (cert : EasyCert)
    (h : easyCheck p cert = true) : Cover Good p := by
  cases cert with
  | base c =>
      apply Cover.leaf
      intro m hm
      exact Or.inl ((cert_sound 128 p c h).sound m hm)
  | contiguous =>
      have hp : p = BB6.Agent40Raw34PairQuadratic.contiguous :=
        sameTable_sound p _ h
      subst p
      apply Cover.leaf
      intro m hm
      exact Or.inl (Or.inl (BB6.Agent40Raw34PairQuadratic.contiguous_never m hm))
  | alternating =>
      have hp : p = BB6.Agent40Raw34PairQuadratic.alternating :=
        sameTable_sound p _ h
      subst p
      apply Cover.leaf
      intro m hm
      exact Or.inl (Or.inl (BB6.Agent40Raw34PairQuadratic.alternating_never m hm))

theorem residual_sound (j : Nat) (row : List Nat)
    (h : residualRows[j]? = some row) : Cover Good (table row) := by
  apply Cover.leaf
  intro m hm
  exact Or.inr ⟨j,row,h,hm⟩

theorem residual_count : residualRows.length = ${rows.length} := by decide
#print axioms easy_sound
#print axioms residual_sound
#print axioms residual_count
end ${dataNs}
`;
 writeFileSync(join(output,dataModule+".lean"),dataSource);

 function rebaseNode(text,start){
   if(!text.startsWith(".split "))return text;
   const lb=text.lastIndexOf("["),rb=text.lastIndexOf("]");
   assert(lb>=0&&rb>lb);
   const kids=text.slice(lb+1,rb).split(",").map(x=>Number(x)-start);
   assert(kids.every(x=>Number.isInteger(x)&&x>=0));
   return text.slice(0,lb+1)+kids.join(",")+text.slice(rb);
 }
 function leanTransition(i){
   if(i===0)return "none";
   const k=i-1,q=Math.floor(k/4),c=k%4;
   const w=c>=2,r=(c%2)===1;
   return `some ⟨${w}, ${r}, ⟨${q}, by decide⟩⟩`;
 }

 const shardMeta=[];
 let start=0;
 for(let i=0;i<25;i++){
   const end=topChildren[i],local=nodes.slice(start,end+1).map(x=>rebaseNode(x,start));
   const localRoot=local.length-1,suffix=String(i).padStart(2,"0");
   const module=`Raw34PairD1LF_F0LDDepth6Child${suffix}`;
   const ns=`BB6.Agent40Raw34PairD1LF_F0LDDepth6Child${suffix}`;
   const transition=leanTransition(i);
   const childSource=`import ${dataModule}
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace ${ns}
open BB6Coverage BB6.Agent50Raw34Plan ${dataNs}
def childParent : PartialMachine := refine parent rootSlot (${transition})
def nodes : Array EasyNode := #[
${local.map(n=>`  ${n}`).join(",\n")}
]
theorem node_count : nodes.size = ${local.length} := by decide
theorem checked : checkWith nodes residualRows easyCheck 4 ${localRoot} childParent = true := by
  decide +kernel
theorem cover : Cover Good childParent :=
  checkWith_sound nodes residualRows easyCheck easy_sound residual_sound
    4 ${localRoot} childParent checked
#print axioms node_count
#print axioms checked
#print axioms cover
end ${ns}
`;
   writeFileSync(join(output,module+".lean"),childSource);
   shardMeta.push({i,module,namespace:ns,start,end,nodes:local.length,transition});
   start=end+1;
 }
 assert.equal(start,nodes.length-1);

 function finCases(combo){
   const [w,r]=combo;
   const ids=[];
   for(let q=0;q<6;q++)ids.push(1+4*q+(w?2:0)+(r?1:0));
   const target=`Cover Good (refine parent rootSlot (some ⟨${w}, ${r}, q⟩))`;
   let body=`by\n  refine Fin.cases (by exact BB6.Agent40Raw34PairD1LF_F0LDDepth6Child${String(ids[0]).padStart(2,"0")}.cover) ?_ q\n`;
   let indent="  ";
   for(let k=1;k<6;k++){
     const varName=`q${k}`;
     body+=indent+`intro ${varName}\n`;
     if(k<5){
       body+=indent+`refine Fin.cases (by exact BB6.Agent40Raw34PairD1LF_F0LDDepth6Child${String(ids[k]).padStart(2,"0")}.cover) ?_ ${varName}\n`;
       indent+="  ";
     }else{
       body+=indent+`exact Fin.cases (by exact BB6.Agent40Raw34PairD1LF_F0LDDepth6Child${String(ids[k]).padStart(2,"0")}.cover) (fun z => Fin.elim0 z) ${varName}\n`;
     }
   }
   return {target,body};
 }
 const combos=[[false,false],[false,true],[true,false],[true,true]];
 const helperNames=["cover00","cover01","cover10","cover11"];
 const helpers=combos.map((c,i)=>{
   const x=finCases(c);
   return `theorem ${helperNames[i]} (q : Fin 6) : ${x.target} := ${x.body}`;
 }).join("\n");
 const importLines=shardMeta.map(x=>`import ${x.module}`).join("\n");
 const finalModule="Raw34PairD1LF_F0LDDepth6Sharded";
 const finalNs="BB6.Agent40Raw34PairD1LF_F0LDDepth6Sharded";
 const finalSource=`${importLines}
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace ${finalNs}
open BB6Coverage
open ${dataNs}
${helpers}
theorem cover : Cover Good parent := by
  apply Cover.branch parent rootSlot (by decide)
  intro t ht
  cases t with
  | none =>
      exact BB6.Agent40Raw34PairD1LF_F0LDDepth6Child00.cover
  | some mv =>
      rcases mv with ⟨w,r,q⟩
      cases w <;> cases r
      · exact cover00 q
      · exact cover01 q
      · exact cover10 q
      · exact cover11 q
#print axioms cover00
#print axioms cover01
#print axioms cover10
#print axioms cover11
#print axioms cover
end ${finalNs}
`;
 writeFileSync(join(output,finalModule+".lean"),finalSource);
 writeFileSync(join(output,"residualRows.json"),JSON.stringify(rows)+"\n");
 const report={
   parentCodes,d1:d1Action,f0:f0Action,physicalParentCompletions:String(25n**6n),
   nodeCount:nodes.length,residualCount:rows.length,rootIndex,rootSlot:topSlot,
   rootChildCount:topChildren.length,shards:shardMeta,bound:128,
   maxAssignedFreeTransitions:6,stats,
   theorem:finalNs+".cover",
   interpretation:"Exact pair-parent Cover, kernel-checked through 25 root subplans to avoid a monolithic decide proof."
 };
 writeFileSync(join(output,"manifest.json"),JSON.stringify(report,null,2)+"\n");
 console.log(JSON.stringify(report,null,2));
 process.exit(0);
}

const imports=easyMode
  ?"import Raw34Plan\nimport Raw34QuadraticPairGrowth"
  :"import Raw34Plan";
const easyPrelude=easyMode?`
inductive EasyCert where
  | base (cert : Cert)
  | contiguous
  | alternating

def easyCheck (p : PartialMachine) : EasyCert → Bool
  | .base cert => certCheck 128 p cert
  | .contiguous => sameTable p BB6.Agent40Raw34PairQuadratic.contiguous
  | .alternating => sameTable p BB6.Agent40Raw34PairQuadratic.alternating

abbrev EasyNode := PlanNode EasyCert
`:"";
const nodeType=easyMode?"EasyNode":"Node";
const proofBlock=easyMode?`
abbrev Good (m : Machine) : Prop :=
  DecidedBelow 128 m ∨ ExplicitResidual residualRows m

theorem easy_sound (p : PartialMachine) (cert : EasyCert)
    (h : easyCheck p cert = true) : Cover Good p := by
  cases cert with
  | base c =>
      apply Cover.leaf
      intro m hm
      exact Or.inl ((cert_sound 128 p c h).sound m hm)
  | contiguous =>
      have hp : p = BB6.Agent40Raw34PairQuadratic.contiguous :=
        sameTable_sound p _ h
      subst p
      apply Cover.leaf
      intro m hm
      exact Or.inl (Or.inl (BB6.Agent40Raw34PairQuadratic.contiguous_never m hm))
  | alternating =>
      have hp : p = BB6.Agent40Raw34PairQuadratic.alternating :=
        sameTable_sound p _ h
      subst p
      apply Cover.leaf
      intro m hm
      exact Or.inl (Or.inl (BB6.Agent40Raw34PairQuadratic.alternating_never m hm))

theorem residual_sound (j : Nat) (row : List Nat)
    (h : residualRows[j]? = some row) : Cover Good (table row) := by
  apply Cover.leaf
  intro m hm
  exact Or.inr ⟨j,row,h,hm⟩

theorem checked : checkWith nodes residualRows easyCheck 5 ${rootIndex} parent = true := by
  decide +kernel
theorem cover : Cover Good parent :=
  checkWith_sound nodes residualRows easyCheck easy_sound residual_sound
    5 ${rootIndex} parent checked
#print axioms node_count
#print axioms residual_count
#print axioms easy_sound
#print axioms residual_sound
#print axioms checked
#print axioms cover
`:`
theorem checked : check nodes residualRows 128 5 ${rootIndex} parent = true := by
  decide +kernel
theorem cover :
    Cover (fun m => DecidedBelow 128 m ∨ ExplicitResidual residualRows m) parent :=
  check_explicit_residual nodes residualRows 128 5 ${rootIndex} parent checked
#print axioms node_count
#print axioms residual_count
#print axioms checked
#print axioms cover
`;
const source=`${imports}
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace ${namespaceName}
open BB6Coverage BB6.Agent50Raw34Plan
${easyPrelude}
def parent : PartialMachine := table [${parentCodes.join(",")}]
def residualRows : List (List Nat) := [
${rows.map(r=>`  [${r.join(",")}]`).join(",\n")}
]
def nodes : Array ${nodeType} := #[
${nodes.map(n=>`  ${n}`).join(",\n")}
]
theorem node_count : nodes.size = ${nodes.length} := by decide
theorem residual_count : residualRows.length = ${rows.length} := by decide
${proofBlock}
end ${namespaceName}
`;
const outputModule=easyMode?"Raw34PairD1LF_F0LDDepth6Plan.lean":"Raw34PairDepth6Plan.lean";
writeFileSync(join(output,outputModule),source);
writeFileSync(join(output,"residualRows.json"),JSON.stringify(rows)+"\n");
const report={
 parentCodes,d1:d1Action,f0:f0Action,physicalParentCompletions:String(25n**6n),
 nodeCount:nodes.length,residualCount:rows.length,rootIndex,
 bound:128,maxAssignedFreeTransitions:6,stats,
 theorem:namespaceName+".cover",
 interpretation:"Every completion of this literal Raw34 subparent is DecidedBelow 128 or extends one of the explicit residualRows; Lean checker is authoritative."
};
writeFileSync(join(output,"manifest.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify(report,null,2));
