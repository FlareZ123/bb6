#!/usr/bin/env node
"use strict";
/*
Given a candidate from search-one-sided-gliders.cjs, construct an original
source Lean theorem with an independently recomputed exact blank seed and
a kernel-checkable parametric certificate. Nothing in the search is trusted.
Usage:
  node search-one-sided-gliders.cjs TABLE 20000 8000 > /tmp/glider.json
  node generate-one-sided-glider-lean.cjs /tmp/glider.json OUT.lean Namespace
*/
const fs=require("node:fs");
const info=JSON.parse(fs.readFileSync(process.argv[2],"utf8")),v=info.found,out=process.argv[3],ns=process.argv[4]||"BB6Coverage.Agent31Pump.GeneratedOneSidedGlider";
if(!v||!out||!/^(?:[A-Za-z_][A-Za-z0-9_]*\.)*[A-Za-z_][A-Za-z0-9_]*$/.test(ns))throw Error("usage: node generate-one-sided-glider-lean.cjs SEARCH.json OUT.lean Namespace");
const code=v.table.replaceAll("_",""),tr=code.match(/.{3}/g);
if(code.length!==36||tr.length!==12||v.block.length<=0||v.prefix.length<=0||v.steps<=0||v.source_step<0)throw Error("bad candidate");
const side=v.side,q0=v.q;
let L=[],R=[],q=0;
for(let n=0;n<v.source_step;n++){
 const m=tr[2*q+(L[0]??0)];if(m==="---")throw Error("seed hits unknown entry");
 const w=+m[0];
 if(m[1]==="R"){L=[R[0]??0,w,...L.slice(1)];R=R.slice(1);}
 else{L=L.slice(1);R=[w,...R];}
 q=m.charCodeAt(2)-65;
}
if(q!==q0)throw Error("wrong seed state");
let body=side==="R"?L:R,other=side==="R"?R:L;
if(other.length!==0||body.slice(0,v.prefix.length).join("")!==v.prefix)throw Error("wrong or nonextremal source seed");
const tail=body.slice(v.prefix.length);
const bit=x=>x?"true":"false",ls=x=>"["+x.map(bit).join(",")+"]";
const as=x=>x.split("").map(Number);
const cases=tr.map((m,i)=>`  | ${i>>1},${bit(i%2)} => ${m==="---"?"none":`some (some ⟨${bit(+m[0])},${bit(m[1]==="R")},${m.charCodeAt(2)-65}⟩)`}`).join("\n");
const left=side==="R",atStart=left?`⟨${q0},.tail prefixWord false,.lit []⟩`:`⟨${q0},.lit [],.tail prefixWord false⟩`;
const atEnd=left?`⟨${q0},.tail (prefixWord ++ block) false,.lit []⟩`:`⟨${q0},.lit [],.tail (prefixWord ++ block) false⟩`;
const config=left?`⟨${q0},prefixWord ++ X,[]⟩`:`⟨${q0},[],prefixWord ++ X⟩`;
const src=`import Agent5TailPump
import Agent5MultiPump
import Root56Coverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-
Opaque-tail symbolic return discovered computationally but proven from scratch
by original-source Lean: seed ${v.source_step} steps, period ${v.steps} steps,
side ${side}, head displacement ${v.block.length} cells, partial table
${v.table}. A failed original-source checker invalidates this claim.
-/
namespace ${ns}
open BB6Coverage Agent31Pump BB6.Agent13BlankDelay Tails
def table : PartialMachine := fun s => match s.1.val,s.2 with
${cases}
  | _,_ => none
def prefixWord : List Bool := ${ls(as(v.prefix))}
def block : List Bool := ${ls(as(v.block))}
def initialTail : List Bool := ${ls(tail)}
def config (X : List Bool) : Z0 := ${config}
def cert : Tails.Cert :=
  ⟨${atStart},${atEnd},[.steps ${v.steps}],0,0,${v.steps}⟩
theorem check_cert : Tails.check table cert = true := by decide +kernel
theorem repeat_step (X : List Bool) :
    run0 table ${v.steps} (config X) = some (config (block ++ X)) := by
  simpa [config,cert,Tails.PZ.eval,Tails.Word.eval,List.append_assoc] using
    Tails.check_sound table cert check_cert 0 0 X []
theorem seed : run0 table ${v.source_step} ⟨0,[],[]⟩ = some (config initialTail) := by decide +kernel
def region (s : Z0) : Prop := ∃ X, s = config X
theorem closed (s : Z0) (h : region s) :
    ∃ k t, 0 < k ∧ region t ∧ run0 table k s = some t := by
  obtain ⟨X,rfl⟩ := h
  exact ⟨${v.steps},config (block ++ X),by decide,⟨_,rfl⟩,repeat_step X⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Multi.never_of_region table region ${v.source_step} (config initialTail) seed ⟨_,rfl⟩ closed m hm
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)
#print axioms cover
end ${ns}
`;
fs.writeFileSync(out,src);
console.log(JSON.stringify({output:out,table:v.table,source:v.source_step,period:v.steps,
 direction:side,namespace:ns,prefixLength:v.prefix.length,blockLength:v.block.length,tailLength:tail.length}));
