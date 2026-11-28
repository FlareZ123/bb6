#!/usr/bin/env node
/**
 * Source-generate original-blank-tape unbounded E/F LEFT-ray witnesses.
 * D1,E0,E1,F0,F1 are arbitrarily chosen from the four leftward E/F
 * actions {0LE,0LF,1LE,1LF}; all other root slots remain completely
 * undefined, including potential HALT entries. The head steps from the
 * original B/C/D prefix left across the two inherited marked cells,
 * reaching a pristine left halfline in state E or F after 9 steps.
 * Every source witness uses finiteRayCheck_sound, no independent oracle.
 */
import assert from "node:assert/strict";
import {mkdirSync,writeFileSync} from "node:fs";
import {join} from "node:path";
const args=process.argv.slice(2),i=args.indexOf("--output");
const out=i<0?"/tmp/a40-raw34-ef-left":args[i+1];
mkdirSync(out,{recursive:true});
const left=[6,7,18,19];
const rows=[];
for(const d of left)for(const e0 of left)for(const e1 of left)
for(const f0 of left)for(const f1 of left)
 rows.push([21,0,22,0,11,0,16,d,e0,e1,f0,f1]);
assert.equal(rows.length,1024);
const modules=[];
for(let i=0;i<16;i++){
 const arr=rows.slice(64*i,64*(i+1)),suffix=String(i).padStart(3,"0"),
 module=`Raw34EFLeftShard${suffix}`,
 namespace=`BB6.Agent40EFLeft.${module}`;
 const source=`import Raw34EFRightRay
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-! Any 9-step partial blank trace escapes left, states E/F closed by
ordinary left actions on both bits. All other instructions may HALT. -/
namespace ${namespace}
open BB6Coverage BB6.Agent23Raw34Next BB6.Agent40Raw34EFRightRay
def tables : List (List Nat) := [
${arr.map(p=>`  [${p.join(",")}]`).join(",\n")}
]
theorem count : tables.length = 64 := by decide
theorem checked :
    tables.all (fun code => finiteRayCheck (table code) 9 false efMask) = true := by
  decide +kernel
theorem never (code : List Nat) (hc : code ∈ tables)
    (m : Machine) (hm : compatible (table code) m) : NeverHalts m := by
  have hh : finiteRayCheck (table code) 9 false efMask = true :=
    List.all_eq_true.mp checked code hc
  have h := (finiteRayCheck_sound (table code) 9 false efMask 0 hh).sound m hm
  rcases h with hn | ⟨n, hn, _⟩
  · exact hn
  · omega
#print axioms count
#print axioms checked
#print axioms never
end ${namespace}
`;
 writeFileSync(join(out,module+".lean"),source);
 modules.push({module,namespace,size:64});
}
const report={root:"1RB---_1RC---_0RD---_1LC---_------_------",
kind:"unbounded E/F left blank halfline source certificates",count:1024,
grossPhysicalVolume:String(1024n*25n**3n),sourceModules:modules};
assert.equal(report.grossPhysicalVolume,"16000000");
writeFileSync(join(out,"manifest.json"),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify(report,null,2));
