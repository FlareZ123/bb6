#!/usr/bin/env node
/**
 * Repackage the exact Raw34 D1=0LF,F0=0LD monolithic split plan into
 * recursively sharded Lean source modules. This does not change the plan:
 * it parses the generator's emitted postorder nodes and residual rows, then
 * proves the same Cover with <= threshold nodes per Boolean kernel check.
 */
import assert from "node:assert/strict";
import {mkdirSync,readFileSync,writeFileSync} from "node:fs";
import {join} from "node:path";

const args=process.argv.slice(2);
function opt(name,def){const i=args.indexOf(name);return i<0?def:args[i+1];}
const input=opt("--input","/tmp/a40-raw34-recursive/base");
const output=opt("--output","/tmp/a40-raw34-recursive/generated");
const threshold=Number(opt("--threshold","400"));
assert(Number.isInteger(threshold)&&threshold>=50);
mkdirSync(output,{recursive:true});

const manifest=JSON.parse(readFileSync(join(input,"manifest.json"),"utf8"));
const rows=JSON.parse(readFileSync(join(input,"residualRows.json"),"utf8"));
const plan=readFileSync(join(input,"Raw34PairD1LF_F0LDDepth6Plan.lean"),"utf8");

assert.equal(manifest.d1,"0LF");
assert.equal(manifest.f0,"0LD");
assert.equal(manifest.nodeCount,16976);
assert.equal(manifest.residualCount,4274);
assert.equal(rows.length,4274);
assert.equal(manifest.rootIndex,16975);

const begin="def nodes : Array EasyNode := #[\n";
const end="\n]\ntheorem node_count";
const a=plan.indexOf(begin), b=plan.indexOf(end,a);
assert(a>=0&&b>a);
const nodes=plan.slice(a+begin.length,b).split("\n").map(line=>{
  let x=line.trim();
  if(x.endsWith(","))x=x.slice(0,-1);
  return x;
}).filter(Boolean);
assert.equal(nodes.length,manifest.nodeCount);

const choiceCount=25;
function parseSplit(idx){
  const text=nodes[idx];
  if(!text.startsWith(".split "))return null;
  const lb=text.lastIndexOf("["),rb=text.lastIndexOf("]");
  assert(lb>=0&&rb>lb,text);
  const slot=text.slice(".split ".length,lb).trim();
  const body=text.slice(lb+1,rb).trim();
  const children=body===""?[]:body.split(",").map(Number);
  assert.equal(children.length,choiceCount);
  assert(children.every(x=>Number.isInteger(x)&&x>=0&&x<idx));
  return {slot,children};
}
const startMemo=new Map();
function subtreeStart(idx){
  if(startMemo.has(idx))return startMemo.get(idx);
  const sp=parseSplit(idx);
  const start=sp?subtreeStart(sp.children[0]):idx;
  startMemo.set(idx,start);
  return start;
}
function verifyPartition(idx){
  const sp=parseSplit(idx);
  if(!sp)return;
  let cursor=subtreeStart(idx);
  for(const child of sp.children){
    assert.equal(subtreeStart(child),cursor,`bad child partition at node ${idx}`);
    cursor=child+1;
  }
  assert.equal(cursor,idx,`bad subtree end at node ${idx}`);
}
for(let i=0;i<nodes.length;i++)if(parseSplit(i))verifyPartition(i);

function rebaseNode(text,start){
  if(!text.startsWith(".split "))return text;
  const lb=text.lastIndexOf("["),rb=text.lastIndexOf("]");
  const kids=text.slice(lb+1,rb).split(",").map(x=>Number(x)-start);
  assert(kids.every(x=>Number.isInteger(x)&&x>=0));
  return text.slice(0,lb+1)+kids.join(",")+text.slice(rb);
}
function leanTransition(i){
  assert(i>=0&&i<25);
  if(i===0)return "none";
  const k=i-1,q=Math.floor(k/4),c=k%4;
  const w=c>=2,r=(c%2)===1;
  return `some ⟨${w}, ${r}, ⟨${q}, by decide⟩⟩`;
}
function safePath(path){return path.map(x=>String(x).padStart(2,"0")).join("_");}

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
def parent : PartialMachine := table [${manifest.parentCodes.join(",")}]
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
writeFileSync(join(output,"residualRows.json"),JSON.stringify(rows)+"\n");

function helperBlock(parentName,slot,childNs){
  const combos=[[false,false],[false,true],[true,false],[true,true]];
  const names=["cover00","cover01","cover10","cover11"];
  const out=[];
  for(let ci=0;ci<4;ci++){
    const [w,r]=combos[ci];
    const ids=[];
    for(let q=0;q<6;q++)ids.push(1+4*q+(w?2:0)+(r?1:0));
    let body=`theorem ${names[ci]} (q : Fin 6) :
    Cover Good (refine ${parentName} ${slot} (some ⟨${w}, ${r}, q⟩)) := by
  refine Fin.cases (by exact ${childNs[ids[0]]}.cover) ?_ q
`;
    let indent="  ";
    for(let k=1;k<6;k++){
      const v=`q${k}`;
      body+=indent+`intro ${v}\n`;
      if(k<5){
        body+=indent+`refine Fin.cases (by exact ${childNs[ids[k]]}.cover) ?_ ${v}\n`;
        indent+="  ";
      }else{
        body+=indent+`exact Fin.cases (by exact ${childNs[ids[k]]}.cover) (fun z => Fin.elim0 z) ${v}\n`;
      }
    }
    out.push(body);
  }
  return out.join("\n");
}

const allModules=[],directModules=[],aggregateModules=[];
function emitSubtree(rootIdx,parentExpr,path,forcedModule=null,forcedNs=null){
  const start=subtreeStart(rootIdx),count=rootIdx-start+1;
  const sp=parseSplit(rootIdx);
  const suffix=safePath(path);
  const module=forcedModule??`Raw34PairD1LF_F0LDDepth6Part${suffix}`;
  const ns=forcedNs??`BB6.Agent40Raw34PairD1LF_F0LDDepth6Part${suffix}`;

  if(count<=threshold || !sp){
    const local=nodes.slice(start,rootIdx+1).map(x=>rebaseNode(x,start));
    const localRoot=local.length-1;
    const source=`import ${dataModule}
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace ${ns}
open BB6Coverage BB6.Agent50Raw34Plan ${dataNs}
def subtreeParent : PartialMachine := ${parentExpr}
def nodes : Array EasyNode := #[
${local.map(n=>`  ${n}`).join(",\n")}
]
theorem node_count : nodes.size = ${local.length} := by decide
theorem checked : checkWith nodes residualRows easyCheck 8 ${localRoot} subtreeParent = true := by
  decide +kernel
theorem cover : Cover Good subtreeParent :=
  checkWith_sound nodes residualRows easyCheck easy_sound residual_sound
    8 ${localRoot} subtreeParent checked
#print axioms node_count
#print axioms checked
#print axioms cover
end ${ns}
`;
    writeFileSync(join(output,module+".lean"),source);
    const meta={module,namespace:ns,kind:"direct",start,end:rootIdx,nodes:count,path};
    allModules.push(meta);directModules.push(meta);return meta;
  }

  const childMeta=[];
  for(let i=0;i<25;i++){
    const childExpr=`refine (${parentExpr}) ${sp.slot} (${leanTransition(i)})`;
    childMeta.push(emitSubtree(sp.children[i],childExpr,[...path,i]));
  }
  const childNs=childMeta.map(x=>x.namespace);
  const imports=[...new Set(childMeta.map(x=>`import ${x.module}`))].join("\n");
  const source=`${imports}
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace ${ns}
open BB6Coverage
open ${dataNs}
def subtreeParent : PartialMachine := ${parentExpr}
${helperBlock("subtreeParent",sp.slot,childNs)}
theorem cover : Cover Good subtreeParent := by
  apply Cover.branch subtreeParent ${sp.slot} (by decide)
  intro t ht
  cases t with
  | none =>
      exact ${childNs[0]}.cover
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
end ${ns}
`;
  writeFileSync(join(output,module+".lean"),source);
  const meta={module,namespace:ns,kind:"aggregate",start,end:rootIdx,nodes:count,path,
    children:childMeta.map(x=>x.module)};
  allModules.push(meta);aggregateModules.push(meta);return meta;
}

const finalModule="Raw34PairD1LF_F0LDDepth6Sharded";
const finalNs="BB6.Agent40Raw34PairD1LF_F0LDDepth6Sharded";
const rootSplit=parseSplit(manifest.rootIndex);
assert(rootSplit);
assert.equal(rootSplit.children.length,25);
const rootMeta=emitSubtree(manifest.rootIndex,"parent",["root"],finalModule,finalNs);
assert.equal(rootMeta.kind,"aggregate");

const topShards=rootSplit.children.map((idx,i)=>{
  const start=subtreeStart(idx);
  const childModule=allModules.find(x=>x.path.length===2&&x.path[0]==="root"&&x.path[1]===i);
  assert(childModule);
  return {i,module:childModule.module,namespace:childModule.namespace,start,end:idx,
    nodes:idx-start+1,transition:leanTransition(i),kind:childModule.kind};
});
assert.equal(topShards.reduce((n,x)=>n+x.nodes,0),nodes.length-1);
assert(directModules.every(x=>x.nodes<=threshold));

const report={
  parentCodes:manifest.parentCodes,d1:manifest.d1,f0:manifest.f0,
  physicalParentCompletions:manifest.physicalParentCompletions,
  nodeCount:nodes.length,residualCount:rows.length,rootIndex:manifest.rootIndex,
  rootSlot:11,rootSlotLean:rootSplit.slot,rootChildCount:rootSplit.children.length,
  shards:topShards,bound:128,threshold,
  directModuleCount:directModules.length,
  aggregateModuleCount:aggregateModules.length,
  generatedModuleCount:allModules.length,
  maxDirectNodes:Math.max(...directModules.map(x=>x.nodes)),
  maxAssignedFreeTransitions:manifest.maxAssignedFreeTransitions,
  stats:manifest.stats,
  theorem:finalNs+".cover",
  interpretation:"Exact pair-parent Cover, recursively sharded so every kernel Boolean plan check stays below the configured node threshold."
};
assert.equal(report.physicalParentCompletions,"244140625");
assert.equal(report.nodeCount,16976);
assert.equal(report.residualCount,4274);
assert.equal(rootSplit.slot,"(⟨5, by decide⟩, true)");
assert.equal(report.rootChildCount,25);
assert(report.maxDirectNodes<=threshold);
writeFileSync(join(output,"manifest.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify(report,null,2));
