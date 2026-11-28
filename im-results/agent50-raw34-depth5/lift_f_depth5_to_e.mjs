#!/usr/bin/env node
/**
 * E↔F physical-state conjugates of the selected Raw34 F depth-five bank.
 *
 * This does not trust conjugacy as a theorem: each emitted transformed table
 * is rechecked by the original Lean fastSideCycleCheck and soundness theorem.
 */
import assert from "node:assert/strict";
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {join} from "node:path";

const args=process.argv.slice(2);
function opt(name,def){const i=args.indexOf(name);return i<0?def:args[i+1];}
const input=opt("--source","/tmp/a50-raw34-f-depth5");
const output=opt("--output","/tmp/a50-raw34-e-depth5");
mkdirSync(output,{recursive:true});
const manifest=JSON.parse(readFileSync(join(input,"manifest.json"),"utf8"));
assert(Number.isInteger(manifest.selectedCount)&&manifest.selectedCount>0);

function swapCode(c){
  if(c<=1)return c;
  const state=(c-2)%6;
  return state===4?c+1:state===5?c-1:c;
}
function swapTable(p){
  assert.equal(p.length,12);
  const out=p.map(swapCode);
  for(let bit=0;bit<=1;bit++){
    out[8+bit]=swapCode(p[10+bit]);
    out[10+bit]=swapCode(p[8+bit]);
  }
  assert.equal(out[0],21);
  assert.equal(out[2],22);
  assert.equal(out[4],11);
  assert.equal(out[6],16);
  return out;
}
function parse(text){
  return [...text.matchAll(/⟨\[([\d,\s]+)\],\s*(\d+),\s*(\d+),\s*(true|false),\s*(-?\d+)⟩/g)]
    .map(m=>({codes:m[1].split(",").map(x=>Number(x.trim())),
      entry:Number(m[2]),period:Number(m[3]),right:m[4]==="true",
      boundary:Number(m[5])}));
}
const modules=[];
let total=0;
for(let i=0;i<manifest.modules.length;i++){
  const src=manifest.modules[i];
  const witnesses=parse(readFileSync(join(input,src.module+".lean"),"utf8"));
  assert.equal(witnesses.length,src.size);
  const xs=witnesses.map(w=>({...w,codes:swapTable(w.codes)}));
  for(let j=0;j<xs.length;j++)
    assert.deepEqual(swapTable(xs[j].codes),witnesses[j].codes);
  const suffix=String(i).padStart(3,"0");
  const module=`Raw34EDepth5SideShard${suffix}`;
  const namespace=`BB6.Agent50EDepth5.${module}`;
  modules.push({module,namespace,size:xs.length});
  const source=`import Raw34D1RDOneStepCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-! E/F conjugates of fifth first-query sidecycles.  The transformed source
is rechecked directly; no unproved state-permutation principle is used. -/
namespace ${namespace}
open BB6Coverage BB6.Agent23Raw34Next BB6Coverage.Agent50SideCycle
structure CycleWitness where
  codes : List Nat
  entry : Nat
  period : Nat
  right : Bool
  boundary : Int
def witnesses : List CycleWitness := [
${xs.map(x=>`  ⟨[${x.codes.join(",")}], ${x.entry}, ${x.period}, ${x.right}, ${x.boundary}⟩`).join(",\n")}
]
def checkCycle (w : CycleWitness) : Bool :=
  decide (0 < w.period) &&
    fastSideCycleCheck (table w.codes) w.entry w.period w.right w.boundary
theorem count : witnesses.length = ${xs.length} := by decide
theorem checked : witnesses.all checkCycle = true := by decide +kernel
theorem all_never (w : CycleWitness) (hw : w ∈ witnesses)
    (m : Machine) (hm : compatible (table w.codes) m) : NeverHalts m := by
  have hh : checkCycle w = true := List.all_eq_true.mp checked w hw
  obtain ⟨hp,hc⟩ : decide (0 < w.period) = true ∧
      fastSideCycleCheck (table w.codes)
        w.entry w.period w.right w.boundary = true := by
    simpa only [checkCycle, Bool.and_eq_true] using hh
  exact fastSideCycleCheck_sound (table w.codes)
    w.entry w.period w.right w.boundary
    (of_decide_eq_true hp) hc m hm
#print axioms count
#print axioms checked
#print axioms all_never
end ${namespace}
`;
  writeFileSync(join(output,module+".lean"),source);
  total+=xs.length;
}
assert.equal(total,manifest.selectedCount);
const report={
  source:"E/F state conjugates, original Lean checker remains authoritative",
  depth:5,count:total,grossPhysicalVolume:String(BigInt(total)*25n**3n),
  sourceFManifest:{selectedCount:manifest.selectedCount,
    fullNewCandidateCount:manifest.fullNewCandidateCount},
  modules
};
assert.equal(report.grossPhysicalVolume,String(BigInt(manifest.selectedCount)*25n**3n));
writeFileSync(join(output,"manifest.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify({...report,
  modules:modules.map(x=>x.namespace+".all_never")},null,2));
