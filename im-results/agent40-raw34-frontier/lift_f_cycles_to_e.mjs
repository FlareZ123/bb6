#!/usr/bin/env node
/**
 * Transport exact original-source F-branch side-cycle witnesses to their
 * E↔F conjugates by a physical state permutation.  A0/B0/C0/D0 are fixed
 * without E/F targets, so the authentic Raw34 root is invariant.  The
 * original-source fastSideCycleCheck on transformed tables validates the
 * halflines and all-completion NeverHalts consequences without assuming
 * external permutation semantics. No generated theorem uses sorryAx.
 *
 * --depth 2 | 3 | 4; --source F-generated-dir; --output E-generated-dir.
 */
import assert from "node:assert/strict";
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname,join} from "node:path";
import {fileURLToPath} from "node:url";
const dir=dirname(fileURLToPath(import.meta.url));
const args=process.argv.slice(2);
function arg(name,otherwise){const i=args.indexOf(name);return i<0?otherwise:args[i+1];}
const depth=Number(arg("--depth","3"));
assert([2,3,4].includes(depth));
const input=arg("--source",join(dir,"generated-f-depth"+depth));
const out=arg("--output",join(dir,"generated-e-depth"+depth));
mkdirSync(out,{recursive:true});
const srcFiles=depth===2?[join(dir,"Raw34FDepth2Cycles.lean")]:
 Array.from({length:depth===3?12:93},(_,i)=>
 join(input,`Raw34FDepth${depth}SideShard${String(i).padStart(3,"0")}.lean`));
function swapCode(c){
 if(c<=1)return c;
 const a=c-2,s=a%6;
 return s===4?c+1:s===5?c-1:c;
}
function swapTable(p){
 assert.equal(p.length,12);
 const a=p.map(swapCode);
 for(let b=0;b<=1;b++){
  a[8+b]=swapCode(p[10+b]);a[10+b]=swapCode(p[8+b]);
 }
 assert.equal(a[0],21);
 assert.equal(a[2],22);
 assert.equal(a[4],11);
 assert.equal(a[6],16);
 return a;
}
function parse(s){
 return [...s.matchAll(/⟨\[([\d,\s]+)\],\s*(\d+),\s*(\d+),\s*(true|false),\s*(-?\d+)⟩/g)]
 .map(m=>({
  codes:m[1].split(",").map(x=>Number(x.trim())),
  entry:Number(m[2]),period:Number(m[3]),
  right:m[4]==="true",boundary:Number(m[5])
 }));
}
const byModule=[];
let total=0;
for(let i=0;i<srcFiles.length;i++){
 const witnesses=parse(readFileSync(srcFiles[i],"utf8"));
 assert(witnesses.length>0);
 const swapped=witnesses.map(w=>({
  ...w,codes:swapTable(w.codes)
 }));
 for(let k=0;k<witnesses.length;k++){
  assert.deepEqual(swapTable(swapped[k].codes),witnesses[k].codes);
 }
 const suffix=String(i).padStart(3,"0");
 const module=depth===2?"Raw34EDepth2Cycles":
   `Raw34EDepth${depth}SideShard${suffix}`;
 const namespace=depth===2?"BB6.Agent40Raw34EDepth2Cycles":
   `BB6.Agent40EDepth${depth}.${module}`;
 const source=`import Raw34D1RDOneStepCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! State E↔F permutation of an original-source F-branch sidecycle bank.
Root A0/B0/C0/D0 are fixed by the permutation; exact transformed
finiteWindow/finiteTailEq checks run in the original source kernel. -/
namespace ${namespace}
open BB6Coverage BB6.Agent23Raw34Next BB6Coverage.Agent50SideCycle
structure CycleWitness where
  codes : List Nat
  entry : Nat
  period : Nat
  right : Bool
  boundary : Int
def witnesses : List CycleWitness := [
${swapped.map(w=>`  ⟨[${w.codes.join(",")}], ${w.entry}, ${w.period}, ${w.right}, ${w.boundary}⟩`).join(",\n")}
]
def checkCycle (w : CycleWitness) : Bool :=
  decide (0 < w.period) &&
    fastSideCycleCheck (table w.codes) w.entry w.period w.right w.boundary
theorem count : witnesses.length = ${swapped.length} := by decide
theorem checked : witnesses.all checkCycle = true := by decide +kernel
theorem all_never (w : CycleWitness) (hw : w ∈ witnesses)
    (m : Machine) (hm : compatible (table w.codes) m) :
    NeverHalts m := by
  have hh : checkCycle w = true := List.all_eq_true.mp checked w hw
  obtain ⟨hpos,hc⟩ : decide (0 < w.period) = true ∧
      fastSideCycleCheck (table w.codes)
        w.entry w.period w.right w.boundary = true := by
    simpa only [checkCycle, Bool.and_eq_true] using hh
  exact fastSideCycleCheck_sound (table w.codes)
    w.entry w.period w.right w.boundary
    (of_decide_eq_true hpos) hc m hm
#print axioms count
#print axioms checked
#print axioms all_never
end ${namespace}
`;
 writeFileSync(join(out,module+".lean"),source);
 total+=swapped.length;
 byModule.push({module,namespace,size:swapped.length});
}
const target={2:34,3:592,4:9231}[depth];
assert.equal(total,target);
const gross=BigInt(total)*(25n**BigInt(8-depth));
const report={source:"Exact E/F state conjugacy, emitted E source checker is authoritative",
 depth,count:total,sourceShards:byModule.length,
 grossPhysicalVolume:String(gross),byModule};
writeFileSync(join(out,"manifest.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify({...report,byModule:byModule.map(x=>x.namespace+".all_never")},null,2));
