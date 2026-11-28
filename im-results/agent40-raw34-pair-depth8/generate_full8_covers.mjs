#!/usr/bin/env node
/**
 * Source-producing depth-eight closure bank for the exact Raw34 pair frontier
 * D1=0LF, F0=0LD.
 *
 * Input is residualRows.json from generate_pair_depth6_plan.mjs --f0 0LD.
 * A selected depth-six row is kept exactly when every physical next-query
 * branch is either certified immediately, or reaches one final undefined
 * query whose 25 physical completions are all certified. Generated Lean
 * rechecks every finite-halt / side-cycle witness with the original source
 * checkers and proves a Cover for each entire depth-six row.
 */
import assert from "node:assert/strict";
import {mkdirSync,readFileSync,writeFileSync} from "node:fs";
import {join} from "node:path";

const args=process.argv.slice(2);
function opt(name,def){const i=args.indexOf(name);return i<0?def:args[i+1];}
const source=opt("--source","/tmp/a40-raw34-pair-easy-plan/generated/residualRows.json");
const output=opt("--output","/tmp/a40-raw34-pair-full8");
const shardSize=Number(opt("--shard-size","10"));
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
function closedReachable(p){
  const seen=new Set([0]),queue=[0];
  while(queue.length){
    const q=queue.pop();
    for(const bit of [0,1]){
      const action=p[2*q+bit];
      if(action<=1)return null;
      const next=(action-2)%6;
      if(!seen.has(next)){seen.add(next);queue.push(next);}
    }
  }
  return [...seen].sort((a,b)=>a-b);
}
function certFor(p){
  const r=trace(p),w=sideWitness(r.hist);
  if(w)return {kind:"side",...w,extended:false};
  if(r.kind==="halt")return {kind:"halt",n:r.t};
  const closed=closedReachable(p);
  if(closed)return {kind:"closed",ss:closed};
  if(r.kind==="long"){
    const rr=trace(p,1000),ww=sideWitness(rr.hist,500,200);
    if(ww)return {kind:"side",...ww,extended:true};
  }
  return {kind:r.kind,slot:r.slot};
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
  if(c.kind==="closed")return `.closed 0 [${c.ss.join(",")}]`;
  assert.equal(c.kind,"side");
  return `.side ${c.entry} ${c.period} ${c.right} ${leanInt(c.boundary)}`;
}
function leanChild(c){
  if(c.kind==="cert")return `.cert (${leanCert(c.cert)})`;
  assert.equal(c.kind,"split");
  return `.split ${leanSlot(c.slot)} [${c.certs.map(leanCert).join(", ")}]`;
}

const selected=[];
let open6=0,long6=0,full7Rows=0;
let directHalt=0,directSide=0,directExtendedSide=0,directClosed=0;
let grandHalt=0,grandSide=0,grandExtendedSide=0,grandClosed=0;
for(let rowIndex=0;rowIndex<rows.length;rowIndex++){
  const base=rows[rowIndex];
  assert(Array.isArray(base)&&base.length===12);
  const first=trace(base);
  if(first.kind==="long"){long6++;continue;}
  assert.equal(first.kind,"unknown");
  open6++;
  let complete=true,usedSplit=false;
  const children=[];
  for(const code of choiceCodes){
    const child=base.slice();child[first.slot]=code;
    const c=certFor(child);
    if(["halt","side","closed"].includes(c.kind)){
      children.push({kind:"cert",cert:c});
      continue;
    }
    if(c.kind==="long"){complete=false;break;}
    assert.equal(c.kind,"unknown");
    usedSplit=true;
    const certs=[];
    for(const code2 of choiceCodes){
      const grand=child.slice();grand[c.slot]=code2;
      const g=certFor(grand);
      if(!["halt","side","closed"].includes(g.kind)){complete=false;break;}
      certs.push(g);
    }
    if(!complete)break;
    assert.equal(certs.length,25);
    children.push({kind:"split",slot:c.slot,certs});
  }
  if(!complete)continue;
  assert.equal(children.length,25);
  if(!usedSplit)full7Rows++;
  for(const c of children){
    if(c.kind==="cert"){
      if(c.cert.kind==="halt")directHalt++;
      else if(c.cert.kind==="closed")directClosed++;
      else {directSide++;if(c.cert.extended)directExtendedSide++;}
    }else for(const g of c.certs){
      if(g.kind==="halt")grandHalt++;
      else if(g.kind==="closed")grandClosed++;
      else {grandSide++;if(g.extended)grandExtendedSide++;}
    }
  }
  selected.push({rowIndex,codes:base,slot:first.slot,children});
}
assert.equal(open6,4234);
assert.equal(long6,40);
assert.equal(selected.length,840);
assert.equal(full7Rows,114);
assert.equal(new Set(selected.map(x=>x.codes.join(","))).size,selected.length);
for(let i=0;i<selected.length;i++)
  for(let j=i+1;j<selected.length;j++)
    assert(conflict(selected[i].codes,selected[j].codes),
      `selected cylinders overlap ${selected[i].rowIndex} and ${selected[j].rowIndex}`);
for(const x of selected)assert.equal(x.codes.filter(v=>v===0).length,2);

const modules=[];
for(let i=0;i<Math.ceil(selected.length/shardSize);i++){
  const xs=selected.slice(i*shardSize,(i+1)*shardSize);
  const suffix=String(i).padStart(3,"0");
  const module=`Raw34PairFull8Shard${suffix}`;
  const namespace=`BB6.Agent40Raw34PairFull8.${module}`;
  modules.push({module,namespace,size:xs.length,rowIndices:xs.map(x=>x.rowIndex)});
  const lean=`import Raw34Plan
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ${namespace}
open BB6Coverage BB6.Agent50Raw34Plan

inductive ChildWitness where
  | cert (cert : Cert)
  | split (slot : Slot) (certs : List Cert)

structure RowWitness where
  rowIndex : Nat
  codes : List Nat
  slot : Slot
  children : List ChildWitness

def childCheck (p : PartialMachine) : ChildWitness → Bool
  | .cert c => certCheck 128 p c
  | .split s certs =>
      decide (p s = none) &&
        decide (certs.length = choices.length) &&
        choices.all fun t =>
          match certs[choices.idxOf t]? with
          | none => false
          | some c => certCheck 128 (refine p s t) c

def rowCheck (r : RowWitness) : Bool :=
  let p := table r.codes
  decide (p r.slot = none) &&
    decide (r.children.length = choices.length) &&
    choices.all fun t =>
      match r.children[choices.idxOf t]? with
      | none => false
      | some c => childCheck (refine p r.slot t) c

theorem child_sound (p : PartialMachine) (w : ChildWitness)
    (h : childCheck p w = true) : Cover (DecidedBelow 128) p := by
  cases w with
  | cert c =>
      exact cert_sound 128 p c h
  | split s certs =>
      have hh : (decide (p s = none) = true ∧
          decide (certs.length = choices.length) = true) ∧
          (choices.all fun t =>
            match certs[choices.idxOf t]? with
            | none => false
            | some c => certCheck 128 (refine p s t) c) = true := by
        simpa only [childCheck, Bool.and_eq_true] using h
      apply Cover.branch p s (of_decide_eq_true hh.1.1)
      intro t ht
      have hc := List.all_eq_true.mp hh.2 t ht
      cases he : certs[choices.idxOf t]? with
      | none => simp [he] at hc
      | some c =>
          exact cert_sound 128 (refine p s t) c
            (by simpa only [he] using hc)

theorem row_sound (r : RowWitness) (h : rowCheck r = true) :
    Cover (DecidedBelow 128) (table r.codes) := by
  have hh : (decide ((table r.codes) r.slot = none) = true ∧
      decide (r.children.length = choices.length) = true) ∧
      (choices.all fun t =>
        match r.children[choices.idxOf t]? with
        | none => false
        | some c => childCheck (refine (table r.codes) r.slot t) c) = true := by
    simpa only [rowCheck, Bool.and_eq_true] using h
  apply Cover.branch (table r.codes) r.slot (of_decide_eq_true hh.1.1)
  intro t ht
  have hc := List.all_eq_true.mp hh.2 t ht
  cases he : r.children[choices.idxOf t]? with
  | none => simp [he] at hc
  | some c =>
      exact child_sound (refine (table r.codes) r.slot t) c
        (by simpa only [he] using hc)

def witnesses : List RowWitness := [
${xs.map(x=>`  ⟨${x.rowIndex}, [${x.codes.join(",")}], ${leanSlot(x.slot)}, [${x.children.map(leanChild).join(", ")}]⟩`).join(",\n")}
]

theorem count : witnesses.length = ${xs.length} := by decide
theorem checked : witnesses.all rowCheck = true := by decide +kernel
theorem all_cover (r : RowWitness) (hr : r ∈ witnesses) :
    Cover (DecidedBelow 128) (table r.codes) :=
  row_sound r (List.all_eq_true.mp checked r hr)

#print axioms child_sound
#print axioms row_sound
#print axioms count
#print axioms checked
#print axioms all_cover
end ${namespace}
`;
  writeFileSync(join(output,module+".lean"),lean);
}
const report={
  status:"source-generated complete depth-eight row Covers; Lean acceptance required",
  parent:"1RB---_1RC---_0RD0LF_1LC---_------_0LD---",
  inputResidualRows:rows.length,openDepth6:open6,longDepth6:long6,
  fullyClosedAtDepth8:selected.length,ofWhichClosedAtDepth7:full7Rows,
  newlyClosedBeyondDepth7:selected.length-full7Rows,
  directHalt,directSide,directExtendedSide,directClosed,
  grandHalt,grandSide,grandExtendedSide,grandClosed,
  physicalMass:String(BigInt(selected.length)*25n**2n),
  remainingWholeDepth6CylinderMass:String(BigInt(rows.length-selected.length)*25n**2n),
  pairwiseDisjoint:true,twoFreeSlotsEach:true,
  shardSize,modules
};
assert.equal(selected.length,3464);
assert.equal(full7Rows,123);
assert.equal(directHalt,4234);
assert.equal(directSide,79735);
assert.equal(directExtendedSide,767);
assert.equal(directClosed,0);
assert.equal(grandHalt,20605);
assert.equal(grandSide,455952);
assert.equal(grandExtendedSide,0);
assert.equal(grandClosed,38568);
assert.equal(report.physicalMass,"2165000");
assert.equal(report.remainingWholeDepth6CylinderMass,"506250");
writeFileSync(join(output,"manifest.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify({...report,modules:modules.map(x=>x.namespace+".all_cover")},null,2));
