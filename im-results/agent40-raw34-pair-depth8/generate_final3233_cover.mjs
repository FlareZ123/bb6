#!/usr/bin/env node
/**
 * Exact source refinement from the 4,274 D1=0LF,F0=0LD Raw34 depth-six
 * residual cylinders to the final complete-machine frontier.
 *
 * Every source branch is explicit.  Leaves are either:
 *   - finite halt / side-cycle / closed-reachable source certificates, or
 *   - one literal complete machine in finalRows.
 *
 * The generated Lean shards prove Cover
 *   (DecidedBelow 128 ∨ ExplicitResidual finalRows)
 * for every original residual row.  A final composer combines those row
 * Covers with the exact root-sharded pair-parent Cover.
 */
import assert from "node:assert/strict";
import {createHash} from "node:crypto";
import {mkdirSync,readFileSync,writeFileSync} from "node:fs";
import {join} from "node:path";

const args=process.argv.slice(2);
function opt(name,def){const i=args.indexOf(name);return i<0?def:args[i+1];}
const source=opt("--source","/tmp/a40-raw34-final3233/base/residualRows.json");
const output=opt("--output","/tmp/a40-raw34-final3233/generated");
const shardSize=Number(opt("--shard-size","25"));
assert(Number.isInteger(shardSize)&&shardSize>0);
mkdirSync(output,{recursive:true});

const originalRows=JSON.parse(readFileSync(source,"utf8"));
assert.equal(originalRows.length,4274);
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
    q=v%6; h+=v%12>=6?1:-1;
  }
  return {kind:"long",hist,t:cap+1};
}
function sideWitness(hist,maxEntry=60,maxPeriod=30){
  const max=Math.min(hist.length,maxEntry);
  for(let entry=0;entry<max;entry++)
  for(let j=entry+1;j<Math.min(hist.length,entry+maxPeriod+1);j++){
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
  if(w)return {kind:"side",...w};
  if(r.kind==="halt" && r.t+1<=128)return {kind:"halt",n:r.t};
  const closed=closedReachable(p);
  if(closed)return {kind:"closed",ss:closed};
  if(r.kind==="unknown")return {kind:"unknown",slot:r.slot};
  if(r.kind==="long"){
    const rr=trace(p,1000),ww=sideWitness(rr.hist,500,200);
    if(ww)return {kind:"side",...ww};
    if(rr.kind==="halt" && rr.t+1<=128)return {kind:"halt",n:rr.t};
  }
  return {kind:"long"};
}
function leanSlot(slot){
  const q=Math.floor(slot/2),bit=(slot&1)===1;
  return "(⟨"+q+", by decide⟩, "+bit+")";
}
function leanInt(x){return x<0?"("+x+")":String(x);}
function leanCert(c){
  if(c.kind==="halt")return ".halt "+c.n;
  if(c.kind==="closed")return ".closed 0 ["+c.ss.join(",")+"]";
  assert.equal(c.kind,"side");
  return ".side "+c.entry+" "+c.period+" "+c.right+" "+leanInt(c.boundary);
}

const finalRows=[],finalIndex=new Map();
function residualLeaf(p){
  assert.equal(p.filter(x=>x===0).length,0);
  const key=p.join(",");
  let j=finalIndex.get(key);
  if(j===undefined){
    j=finalRows.length; finalIndex.set(key,j); finalRows.push(p.slice());
  }
  return {kind:"residual",row:j};
}
function leafFor(p,stats){
  const c=certFor(p);
  if(["halt","side","closed"].includes(c.kind)){
    stats["leaf_"+c.kind]=(stats["leaf_"+c.kind]??0)+1;
    return {kind:"cert",cert:c};
  }
  assert.equal(c.kind,"long");
  stats.leaf_residual=(stats.leaf_residual??0)+1;
  return residualLeaf(p);
}
function splitRemaining(p,slot,stats){
  assert.equal(p[slot],0);
  const leaves=[];
  for(const code of choiceCodes){
    const q=p.slice(); q[slot]=code; leaves.push(leafFor(q,stats));
  }
  return {kind:"split",slot,leaves};
}

const witnesses=[],stats={};
for(let rowIndex=0;rowIndex<originalRows.length;rowIndex++){
  const base=originalRows[rowIndex];
  assert.equal(base.length,12);
  assert.equal(base.filter(x=>x===0).length,2);
  const c0=certFor(base);
  let rootSlot,children=[];
  if(c0.kind==="unknown"){
    rootSlot=c0.slot;
    for(const code of choiceCodes){
      const child=base.slice(); child[rootSlot]=code;
      const c=certFor(child);
      if(["halt","side","closed"].includes(c.kind)){
        stats["direct_"+c.kind]=(stats["direct_"+c.kind]??0)+1;
        children.push({kind:"cert",cert:c});
      }else{
        assert(["unknown","long"].includes(c.kind));
        const holes=[];
        for(let s=0;s<12;s++)if(child[s]===0)holes.push(s);
        assert.equal(holes.length,1);
        const slot=c.kind==="unknown"?c.slot:holes[0];
        assert.equal(slot,holes[0]);
        stats["child_split_"+c.kind]=(stats["child_split_"+c.kind]??0)+1;
        children.push(splitRemaining(child,slot,stats));
      }
    }
  }else{
    assert.equal(c0.kind,"long");
    const holes=[];
    for(let s=0;s<12;s++)if(base[s]===0)holes.push(s);
    assert.equal(holes.length,2);
    rootSlot=holes[0];
    stats.long6_rows=(stats.long6_rows??0)+1;
    for(const code of choiceCodes){
      const child=base.slice(); child[rootSlot]=code;
      children.push(splitRemaining(child,holes[1],stats));
    }
  }
  assert.equal(children.length,25);
  witnesses.push({rowIndex,codes:base.slice(),slot:rootSlot,children});
}
assert.equal(witnesses.length,4274);
assert.equal(finalRows.length,3233);
assert.equal(finalIndex.size,3233);

const finalJson=JSON.stringify(finalRows)+"\n";
const finalSha256=createHash("sha256").update(finalJson).digest("hex");
assert.equal(finalSha256,"c63e67cc6bf6a30e6ec0d4d313a4b2407dd31593d6331311634fc6fe0537ef83");

function leanLeaf(x){
  if(x.kind==="cert")return ".cert ("+leanCert(x.cert)+")";
  return ".residual "+x.row;
}
function leanChild(x){
  if(x.kind==="cert")return ".cert ("+leanCert(x.cert)+")";
  return ".split "+leanSlot(x.slot)+" ["+x.leaves.map(leanLeaf).join(", ")+"]";
}
function leanWitness(x){
  return "  ⟨"+x.rowIndex+", ["+x.codes.join(",")+"], "+leanSlot(x.slot)+
    ", ["+x.children.map(leanChild).join(", ")+"]⟩";
}

const dataModule="Raw34PairFinal3233Data";
const dataNs="BB6.Agent40Raw34Final3233.Data";
const dataSource=[
"import Raw34Plan",
"set_option maxRecDepth 100000",
"set_option maxHeartbeats 0",
"namespace "+dataNs,
"open BB6Coverage BB6.Agent50Raw34Plan",
"",
"def finalRows : List (List Nat) := [",
finalRows.map(r=>"  ["+r.join(",")+"]").join(",\n"),
"]",
"",
"abbrev Good (m : Machine) : Prop :=",
"  DecidedBelow 128 m ∨ ExplicitResidual finalRows m",
"",
"inductive LeafWitness where",
"  | cert (cert : Cert)",
"  | residual (row : Nat)",
"",
"inductive ChildWitness where",
"  | cert (cert : Cert)",
"  | split (slot : Slot) (leaves : List LeafWitness)",
"",
"structure RowWitness where",
"  rowIndex : Nat",
"  codes : List Nat",
"  slot : Slot",
"  children : List ChildWitness",
"",
"def leafCheck (p : PartialMachine) : LeafWitness → Bool",
"  | .cert c => certCheck 128 p c",
"  | .residual j =>",
"      match finalRows[j]? with",
"      | none => false",
"      | some row => sameTable p (table row)",
"",
"def childCheck (p : PartialMachine) : ChildWitness → Bool",
"  | .cert c => certCheck 128 p c",
"  | .split s leaves =>",
"      decide (p s = none) &&",
"        decide (leaves.length = choices.length) &&",
"        choices.all fun t =>",
"          match leaves[choices.idxOf t]? with",
"          | none => false",
"          | some w => leafCheck (refine p s t) w",
"",
"def rowCheck (r : RowWitness) : Bool :=",
"  let p := table r.codes",
"  decide (p r.slot = none) &&",
"    decide (r.children.length = choices.length) &&",
"    choices.all fun t =>",
"      match r.children[choices.idxOf t]? with",
"      | none => false",
"      | some w => childCheck (refine p r.slot t) w",
"",
"theorem leaf_sound (p : PartialMachine) (w : LeafWitness)",
"    (h : leafCheck p w = true) : Cover Good p := by",
"  cases w with",
"  | cert c =>",
"      apply Cover.leaf",
"      intro m hm",
"      exact Or.inl ((cert_sound 128 p c h).sound m hm)",
"  | residual j =>",
"      cases hr : finalRows[j]? with",
"      | none => simp [leafCheck, hr] at h",
"      | some row =>",
"          have he : sameTable p (table row) = true := by",
"            simpa only [leafCheck, hr] using h",
"          rw [sameTable_sound p (table row) he]",
"          apply Cover.leaf",
"          intro m hm",
"          exact Or.inr ⟨j, row, hr, hm⟩",
"",
"theorem child_sound (p : PartialMachine) (w : ChildWitness)",
"    (h : childCheck p w = true) : Cover Good p := by",
"  cases w with",
"  | cert c =>",
"      apply Cover.leaf",
"      intro m hm",
"      exact Or.inl ((cert_sound 128 p c h).sound m hm)",
"  | split s leaves =>",
"      have hh : (decide (p s = none) = true ∧",
"          decide (leaves.length = choices.length) = true) ∧",
"          (choices.all fun t =>",
"            match leaves[choices.idxOf t]? with",
"            | none => false",
"            | some w => leafCheck (refine p s t) w) = true := by",
"        simpa only [childCheck, Bool.and_eq_true] using h",
"      apply Cover.branch p s (of_decide_eq_true hh.1.1)",
"      intro t ht",
"      have hc := List.all_eq_true.mp hh.2 t ht",
"      cases hw : leaves[choices.idxOf t]? with",
"      | none => simp [hw] at hc",
"      | some w =>",
"          exact leaf_sound (refine p s t) w (by simpa only [hw] using hc)",
"",
"theorem row_sound (r : RowWitness) (h : rowCheck r = true) :",
"    Cover Good (table r.codes) := by",
"  have hh : (decide ((table r.codes) r.slot = none) = true ∧",
"      decide (r.children.length = choices.length) = true) ∧",
"      (choices.all fun t =>",
"        match r.children[choices.idxOf t]? with",
"        | none => false",
"        | some w => childCheck (refine (table r.codes) r.slot t) w) = true := by",
"    simpa only [rowCheck, Bool.and_eq_true] using h",
"  apply Cover.branch (table r.codes) r.slot (of_decide_eq_true hh.1.1)",
"  intro t ht",
"  have hc := List.all_eq_true.mp hh.2 t ht",
"  cases hw : r.children[choices.idxOf t]? with",
"  | none => simp [hw] at hc",
"  | some w =>",
"      exact child_sound (refine (table r.codes) r.slot t) w",
"        (by simpa only [hw] using hc)",
"",
"def pairCheck (row : List Nat) (w : RowWitness) : Bool :=",
"  sameTable (table row) (table w.codes) && rowCheck w",
"",
"def pairListCheck : List (List Nat) → List RowWitness → Bool",
"  | [], [] => true",
"  | row::rows, w::ws => pairCheck row w && pairListCheck rows ws",
"  | _, _ => false",
"",
"theorem pairList_sound (rows : List (List Nat)) (ws : List RowWitness)",
"    (h : pairListCheck rows ws = true) :",
"    ∀ row, row ∈ rows → Cover Good (table row) := by",
"  induction rows generalizing ws with",
"  | nil => simp",
"  | cons r rs ih =>",
"      cases ws with",
"      | nil => simp [pairListCheck] at h",
"      | cons w ws =>",
"          have hh : pairCheck r w = true ∧ pairListCheck rs ws = true := by",
"            simpa only [pairListCheck, Bool.and_eq_true] using h",
"          intro row hr",
"          have hm : row = r ∨ row ∈ rs := by simpa using hr",
"          rcases hm with rfl | hr",
"          · have hp : sameTable (table r) (table w.codes) = true ∧",
"                rowCheck w = true := by",
"              simpa only [pairCheck, Bool.and_eq_true] using hh.1",
"            rw [sameTable_sound (table r) (table w.codes) hp.1]",
"            exact row_sound w hp.2",
"          · exact ih ws hh.2 row hr",
"",
"theorem final_count : finalRows.length = 3233 := by decide",
"#print axioms leaf_sound",
"#print axioms child_sound",
"#print axioms row_sound",
"#print axioms pairList_sound",
"#print axioms final_count",
"end "+dataNs,
""
].join("\n");
writeFileSync(join(output,dataModule+".lean"),dataSource);
writeFileSync(join(output,"finalRows.json"),finalJson);

const modules=[];
for(let start=0,shard=0;start<witnesses.length;start+=shardSize,shard++){
  const end=Math.min(witnesses.length,start+shardSize);
  const xs=witnesses.slice(start,end),rs=originalRows.slice(start,end);
  const suffix=String(shard).padStart(3,"0");
  const module="Raw34PairFinal3233Shard"+suffix;
  const ns="BB6.Agent40Raw34Final3233."+module;
  modules.push({module,namespace:ns,start,end,size:xs.length});
  const sourceText=[
    "import "+dataModule,
    "set_option maxRecDepth 100000",
    "set_option maxHeartbeats 0",
    "namespace "+ns,
    "open BB6Coverage BB6.Agent50Raw34Plan "+dataNs,
    "def rows : List (List Nat) := [",
    rs.map(r=>"  ["+r.join(",")+"]").join(",\n"),
    "]",
    "def witnesses : List RowWitness := [",
    xs.map(leanWitness).join(",\n"),
    "]",
    "theorem row_count : rows.length = "+xs.length+" := by decide",
    "theorem witness_count : witnesses.length = "+xs.length+" := by decide",
    "theorem checked : pairListCheck rows witnesses = true := by decide +kernel",
    "theorem cover_mem (row : List Nat) (h : row ∈ rows) :",
    "    Cover Good (table row) :=",
    "  pairList_sound rows witnesses checked row h",
    "#print axioms row_count",
    "#print axioms witness_count",
    "#print axioms checked",
    "#print axioms cover_mem",
    "end "+ns,
    ""
  ].join("\n");
  writeFileSync(join(output,module+".lean"),sourceText);
}

const indexModule="Raw34PairFinal3233Index";
const indexNs="BB6.Agent40Raw34Final3233.Index";
const imports=[
  "import Raw34PairD1LF_F0LDDepth6Data",
  ...modules.map(x=>"import "+x.module)
];
const allExpr=modules.map(x=>x.namespace+".rows").join(" ++\n  ");
let dispatch=[
"theorem cover_mem_all (row : List Nat) (h : row ∈ allRows) :",
"    Cover Good (table row) := by",
"  simp only [allRows, List.mem_append] at h"
];
for(let i=0;i<modules.length-1;i++){
  dispatch.push("  rcases h with h | h");
  dispatch.push("  · exact "+modules[i].namespace+".cover_mem row h");
  dispatch.push("  ·");
}
const last=modules[modules.length-1];
let indent="  ".repeat(modules.length);
dispatch.push(indent+"exact "+last.namespace+".cover_mem row h");
// Re-indent nested lines generated above into syntactically valid Lean.
let depth=0,dispatch2=[
"theorem cover_mem_all (row : List Nat) (h : row ∈ allRows) :",
"    Cover Good (table row) := by",
"  simp only [allRows, List.mem_append] at h"
];
for(let i=0;i<modules.length-1;i++){
  const pad="  ".repeat(depth+1);
  dispatch2.push(pad+"rcases h with h | h");
  dispatch2.push(pad+"· exact "+modules[i].namespace+".cover_mem row h");
  dispatch2.push(pad+"·");
  depth++;
}
dispatch2.push("  ".repeat(depth+1)+"exact "+last.namespace+".cover_mem row h");

const oldNs="BB6.Agent40Raw34PairD1LF_F0LDDepth6Data";
const indexSource=[
...imports,
"set_option maxRecDepth 100000",
"set_option maxHeartbeats 0",
"namespace "+indexNs,
"open BB6Coverage BB6.Agent50Raw34Plan "+dataNs,
"def allRows : List (List Nat) :=",
"  "+allExpr,
"theorem allRows_eq_old : allRows = "+oldNs+".residualRows := by decide +kernel",
...dispatch2,
"theorem old_row_cover (j : Nat) (row : List Nat)",
"    (hj : "+oldNs+".residualRows[j]? = some row) :",
"    Cover Good (table row) := by",
"  have hm : row ∈ "+oldNs+".residualRows := by",
"    rcases List.getElem?_eq_some_iff.mp hj with ⟨hidx, hget⟩",
"    exact List.mem_of_getElem hget",
"  have hm' : row ∈ allRows := by",
"    rw [allRows_eq_old]",
"    exact hm",
"  exact cover_mem_all row hm'",
"#print axioms allRows_eq_old",
"#print axioms cover_mem_all",
"#print axioms old_row_cover",
"end "+indexNs,
""
].join("\n");
writeFileSync(join(output,indexModule+".lean"),indexSource);

const composeModule="Raw34PairFinal3233Cover";
const composeNs="BB6.Agent40Raw34Final3233";
const composeSource=[
"import Raw34PairD1LF_F0LDDepth6Sharded",
"import "+indexModule,
"set_option maxRecDepth 100000",
"set_option maxHeartbeats 0",
"namespace "+composeNs,
"open BB6Coverage BB6.Agent50Raw34Plan",
"open "+dataNs,
"theorem cover : Cover Good "+oldNs+".parent := by",
"  apply Cover.leaf",
"  intro m hm",
"  rcases BB6.Agent40Raw34PairD1LF_F0LDDepth6Sharded.cover.sound m hm with hd | hr",
"  · exact Or.inl hd",
"  · rcases hr with ⟨j, row, hj, hrow⟩",
"    exact ("+indexNs+".old_row_cover j row hj).sound m hrow",
"#print axioms cover",
"end "+composeNs,
""
].join("\n");
writeFileSync(join(output,composeModule+".lean"),composeSource);

const manifest={
  status:"candidate generator; generated Lean must be kernel checked",
  parent:"1RB---_1RC---_0RD0LF_1LC---_------_0LD---",
  originalResidualRows:originalRows.length,
  originalResidualPhysical:"2671250",
  finalResidualRows:finalRows.length,
  finalResidualSha256:finalSha256,
  finalResidualsAreComplete:finalRows.every(r=>r.every(x=>x!==0)),
  finalResidualsUnique:new Set(finalRows.map(r=>r.join(","))).size===finalRows.length,
  boundedHaltTimes:[101,102,123],
  shardSize,shardCount:modules.length,stats,modules,
  theorem:composeNs+".cover",
  interpretation:"Every completion of the exact 244,140,625-table pair parent is DecidedBelow 128 or equals one of 3,233 explicit complete residual machines."
};
writeFileSync(join(output,"manifest.json"),JSON.stringify(manifest,null,2)+"\n");
console.log(JSON.stringify({...manifest,modules:undefined},null,2));
