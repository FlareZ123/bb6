#!/usr/bin/env node
/**
 * An overlooked E/F symmetry gap in the ACCEPTED Agent50 depth-three
 * first-hole sidecycle bank: 168 old source sidecycles whose D1 target
 * is A..D have a missing physical E↔F conjugate. The original 1,206
 * D1-root source list omits these companions; 592 further missing
 * companions with D1 targeting E/F are already handled separately by
 * Agent40's F-branch source generator, so this bank avoids duplication.
 *
 * This generator exports original-source fastSideCycleCheck witnesses.
 * The Lean source checker is the authority for mathematical validity;
 * the JSON list and state permutation alone are not proofs.
 */
import assert from "node:assert/strict";
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname,join} from "node:path";
import {fileURLToPath} from "node:url";
const dir=dirname(fileURLToPath(import.meta.url));
const input=join(dir,"../agent50-raw34-firsthole/depth3-candidate-witnesses.json");
const xs=JSON.parse(readFileSync(input,"utf8")).witnesses;
assert.equal(xs.length,1206);
const old=new Set(xs.map(x=>x.table));
function swapAction(a){
 if(a==="---")return a;
 assert(/^([01])([LR])([ABCDEF])$/.test(a));
 return a.slice(0,2)+(a[2]==="E"?"F":a[2]==="F"?"E":a[2]);
}
function swapTable(t){
 const rows=t.split("_");
 assert.equal(rows.length,6);
 const r=rows.map(x=>swapAction(x.slice(0,3))+swapAction(x.slice(3,6)));
 [r[4],r[5]]=[r[5],r[4]];
 return r.join("_");
}
const actions=["HALT"];
for(const w of "01")for(const d of "LR")for(const q of "ABCDEF")
 actions.push(w+d+q);
const code=new Map(actions.map((x,i)=>[x,i+1]));
function physical(t){
 return t.replaceAll("_","").match(/.{3}/g).map(a=>a==="---"?0:code.get(a));
}
const sources=xs.map(x=>({...x,table:swapTable(x.table)}))
  .filter(x=>!old.has(x.table));
assert.equal(sources.length,760);
const missing=sources.filter(x=>!/[EF]$/.test(x.table.split("_")[3].slice(3,6)));
assert.equal(missing.length,168);
const names=new Set(missing.map(x=>x.table));
assert.equal(names.size,168);
const counts={};
for(const x of missing){const d=x.table.split("_")[3].slice(3,6);
 counts[d]=(counts[d]||0)+1;
 assert.deepEqual(swapTable(swapTable(x.table)),x.table);
}
const expected={ "0LD":42, "1LA":33,"1LB":37,"1LD":29,"1RD":27 };
assert.deepEqual(counts,expected);
const args=process.argv.slice(2);const i=args.indexOf("--output");
const output=i<0?"/tmp/a40-raw34-missing-ef-third":args[i+1];
mkdirSync(output,{recursive:true});
const modules=[];
for(let i=0;i<4;i++){
 const arr=missing.slice(i*42,(i+1)*42),
 suffix=String(i).padStart(3,"0"),
 module=`Raw34MissingEFThirdShard${suffix}`,
 namespace=`BB6.Agent40MissingEFThird.${module}`;
 const c=`import Raw34D1RDOneStepCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-! Original-source side-cycle checker for 168 old-bank omitted
E/F-conjugate D1-to-A..D three-slot physical cylinders. No quotient. -/
namespace ${namespace}
open BB6Coverage BB6.Agent23Raw34Next BB6Coverage.Agent50SideCycle
structure CycleWitness where
  codes : List Nat
  entry : Nat
  period : Nat
  right : Bool
  boundary : Int
def witnesses : List CycleWitness := [
${arr.map(x=>`  ⟨[${physical(x.table).join(",")}], ${x.entry}, ${x.period}, ${x.right}, ${x.boundary}⟩`).join(",\n")}
]
def checkCycle (w : CycleWitness) : Bool :=
  decide (0 < w.period) &&
    fastSideCycleCheck (table w.codes) w.entry w.period w.right w.boundary
theorem count : witnesses.length = 42 := by decide
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
 writeFileSync(join(output,module+".lean"),c);
 modules.push({module,namespace,size:42});
}
const report={status:"new missing depth3 EF-conjugate source certificates, Lean needed",
 sourceExistingBankSize:1206,symmetryMissingTotal:760,
 newlyGeneratedNonEF_D1:168,byD1:counts,
 distinctPhysicalCylinders:168,grossPhysicalVolume:String(168n*25n**5n),
 nonD1_1RDSourceCylinders:141,nonD1_1RDGross:String(141n*25n**5n),
 modules};
writeFileSync(join(output,"manifest.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify(report,null,2));
