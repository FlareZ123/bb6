#!/usr/bin/env node
/**
 * Source-producing depth-seven closure bank for the exact Raw34 pair frontier
 * D1=0LF, F0=0LD.
 *
 * Input is residualRows.json from generate_pair_depth6_plan.mjs --f0 0LD.
 * We select exactly those depth-six residual cylinders whose genuine next
 * undefined source query has all 25 physical choices certified immediately
 * by the short finite-halt or translated-half-line side-cycle checkers.
 * Candidate generation is untrusted; generated Lean rechecks every child
 * against the original source checkers and proves a Cover for the whole row.
 */
import assert from "node:assert/strict";
import {mkdirSync,readFileSync,writeFileSync} from "node:fs";
import {join} from "node:path";

const args=process.argv.slice(2);
function opt(name,def){const i=args.indexOf(name);return i<0?def:args[i+1];}
const source=opt("--source","/tmp/a40-raw34-pair-easy-plan/generated/residualRows.json");
const output=opt("--output","/tmp/a40-raw34-pair-full7");
const shardSize=Number(opt("--shard-size","20"));
assert(Number.isInteger(shardSize)&&shardSize>0);
mkdirSync(output,{recursive:true});

const rows=JSON.parse(readFileSync(source,"utf8"));
assert.equal(rows.length,4274);
const choiceCodes=[1];
for(let q=0;q<6;q++)choiceCodes.push(2+q,8+q,14+q,20+q);
assert.equal(choiceCodes.length,25);

function trace(p,cap=100){
  let q=0,h=0,ones=new Set(),hist=[];
  for(let t=0;t<=cap;t++){
    hist.push({q,h,ones:new Set(ones)});
    const slot=2*q+(ones.has(h)?1:0),action=p[slot];
    if(action===0||action===1)
      return {kind:action===0?"unknown":"halt",slot,hist,t};
    const v=action-2;
    v>=12?ones.add(h):ones.delete(h);
    q=v%6;h+=v%12>=6?1:-1;
  }
  return {kind:"long",hist};
}
function sideWitness(hist){
  const max=Math.min(hist.length,60);
  for(let entry=0;entry<max;entry++)
  for(let j=entry+1;j<Math.min(hist.length,entry+31);j++){
    const a=hist[entry],b=hist[j],delta=b.h-a.h;
    if(a.q!==b.q)continue;
    for(const right of [true,false]){
      if(right?delta<0:delta>0)continue;
      let boundary=right?Infinity:-Infinity;
      for(let t=entry;t<j;t++)
        boundary=right?Math.min(boundary,hist[t].h):
                       Math.max(boundary,hist[t].h);
      if([...a.ones].some(x=>(right?x>=boundary:x<=boundary)&&
          !b.ones.has(x+delta)))continue;
      if([...b.ones].some(y=>(right?y-delta>=boundary:y-delta<=boundary)&&
          !a.ones.has(y-delta)))continue;
      return {entry,period:j-entry,right,boundary};
    }
  }
  return null;
}
function conflict(a,b){
  return a.some((x,i)=>x!==0&&b[i]!==0&&x!==b[i]);
}
function leanSlot(slot){
  const q=Math.floor(slot/2),bit=(slot&1)===1;
  return `(⟨${q}, by decide⟩, ${bit})`;
}
function leanInt(x){return x<0?`(${x})`:String(x);}
function leanCert(c){
  if(c.kind==="halt")return `.halt ${c.n}`;
  return `.side ${c.entry} ${c.period} ${c.right} ${leanInt(c.boundary)}`;
}

const selected=[];
let open6=0,long6=0,totalHaltChildren=0,totalSideChildren=0;
const unresolvedHistogram={};
for(let rowIndex=0;rowIndex<rows.length;rowIndex++){
  const base=rows[rowIndex];
  assert(Array.isArray(base)&&base.length===12);
  const first=trace(base);
  if(first.kind==="long"){long6++;continue;}
  assert.equal(first.kind,"unknown");
  open6++;
  const certs=[];
  let unresolved=0;
  for(const code of choiceCodes){
    const p=base.slice();p[first.slot]=code;
    const r=trace(p),w=sideWitness(r.hist);
    if(w){certs.push({kind:"side",...w});continue;}
    if(r.kind==="halt"){certs.push({kind:"halt",n:r.t});continue;}
    certs.push(null);unresolved++;
  }
  unresolvedHistogram[unresolved]=(unresolvedHistogram[unresolved]??0)+1;
  if(unresolved===0){
    const haltCount=certs.filter(c=>c.kind==="halt").length;
    const sideCount=certs.filter(c=>c.kind==="side").length;
    assert.equal(haltCount,1);
    assert.equal(sideCount,24);
    totalHaltChildren+=haltCount;totalSideChildren+=sideCount;
    selected.push({rowIndex,codes:base,slot:first.slot,certs});
  }
}
assert.equal(open6,4234);
assert.equal(long6,40);
assert.equal(selected.length,114);
assert.equal(totalHaltChildren,114);
assert.equal(totalSideChildren,2736);
assert.equal(new Set(selected.map(x=>x.codes.join(","))).size,selected.length);
for(let i=0;i<selected.length;i++)
  for(let j=i+1;j<selected.length;j++)
    assert(conflict(selected[i].codes,selected[j].codes),
      `selected cylinders overlap ${selected[i].rowIndex} and ${selected[j].rowIndex}`);
for(const x of selected)
  assert.equal(x.codes.filter(v=>v===0).length,2);

const modules=[];
for(let i=0;i<Math.ceil(selected.length/shardSize);i++){
  const xs=selected.slice(i*shardSize,(i+1)*shardSize);
  const suffix=String(i).padStart(3,"0");
  const module=`Raw34PairFull7Shard${suffix}`;
  const namespace=`BB6.Agent40Raw34PairFull7.${module}`;
  modules.push({module,namespace,size:xs.length,rowIndices:xs.map(x=>x.rowIndex)});
  const lean=`import Raw34Plan
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ${namespace}
open BB6Coverage BB6.Agent50Raw34Plan

structure RowWitness where
  rowIndex : Nat
  codes : List Nat
  slot : Slot
  certs : List Cert

def witnesses : List RowWitness := [
${xs.map(x=>`  ⟨${x.rowIndex}, [${x.codes.join(",")}], ${leanSlot(x.slot)}, [${x.certs.map(leanCert).join(", ")}]⟩`).join(",\n")}
]

def rowCheck (r : RowWitness) : Bool :=
  let p := table r.codes
  decide (p r.slot = none) &&
    decide (r.certs.length = choices.length) &&
    choices.all fun t =>
      match r.certs[choices.idxOf t]? with
      | none => false
      | some c => certCheck 128 (refine p r.slot t) c

theorem row_sound (r : RowWitness) (h : rowCheck r = true) :
    Cover (DecidedBelow 128) (table r.codes) := by
  have hh : (decide ((table r.codes) r.slot = none) = true ∧
      decide (r.certs.length = choices.length) = true) ∧
      (choices.all fun t =>
        match r.certs[choices.idxOf t]? with
        | none => false
        | some c => certCheck 128 (refine (table r.codes) r.slot t) c) = true := by
    simpa only [rowCheck, Bool.and_eq_true] using h
  apply Cover.branch (table r.codes) r.slot (of_decide_eq_true hh.1.1)
  intro t ht
  have hc := List.all_eq_true.mp hh.2 t ht
  cases he : r.certs[choices.idxOf t]? with
  | none => simp [he] at hc
  | some c =>
      exact cert_sound 128 (refine (table r.codes) r.slot t) c
        (by simpa only [he] using hc)

theorem count : witnesses.length = ${xs.length} := by decide
theorem checked : witnesses.all rowCheck = true := by decide +kernel
theorem all_cover (r : RowWitness) (hr : r ∈ witnesses) :
    Cover (DecidedBelow 128) (table r.codes) :=
  row_sound r (List.all_eq_true.mp checked r hr)

#print axioms row_sound
#print axioms count
#print axioms checked
#print axioms all_cover
end ${namespace}
`;
  writeFileSync(join(output,module+".lean"),lean);
}
const report={
  status:"source-generated complete depth-seven row Covers; Lean acceptance required",
  parent:"1RB---_1RC---_0RD0LF_1LC---_------_0LD---",
  inputResidualRows:rows.length,openDepth6:open6,longDepth6:long6,
  fullyClosedAtDepth7:selected.length,
  haltingChildren:totalHaltChildren,sideCycleChildren:totalSideChildren,
  physicalMass:String(BigInt(selected.length)*25n**2n),
  pairwiseDisjoint:true,twoFreeSlotsEach:true,
  unresolvedHistogram,shardSize,modules
};
assert.equal(report.physicalMass,"71250");
writeFileSync(join(output,"manifest.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify({...report,modules:modules.map(x=>x.namespace+".all_cover")},null,2));
