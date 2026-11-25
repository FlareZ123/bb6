const fs = require("node:fs");
function generate(records){
 const move=s=>s==="---"||s[2]==="Z"?"none":`some ⟨${s[0]==="1"},${s[1]==="R"},${s.charCodeAt(2)-65}⟩`;
 const slot=s=>`(${s.charCodeAt(0)-65},${s[1]==="1"})`;
 const header=`import HardRootParents

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent19HardRoot
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47WeightedHalt BB6.Agent8TNFPath

`;
 const body=records.map(r=>{const n=r.name,p=r.parent.raw,h=r.haltSlot,d=r.maxDelay,moves=r.table.replaceAll("_","").match(/.{3}/g).map(move).join(", "),sched=r.path.slice(1).map(a=>`(${a.t},${slot(a.slot)})`).join(", "),ds=Array.from({length:d+1},(_,i)=>i).join(", ");return `def ${n} : Machine := literal [${moves}]
def ${n}_schedule : List (Nat × Slot) := [${sched}]
theorem ${n}_path : FirstHolePath (forgetHaltRows ${n}) 6 :=
  checked_from_root _ ${n}_schedule (by decide)
theorem ${n}_parent : compatible p${p} ${n} :=
  (parentCheck_iff _ _).mp (by decide)
theorem ${n}_leaf_parent : ∀ m, compatible (forgetHaltRows ${n}) m → compatible p${p} m :=
  leaf_extends_parent _ _ (ordinaryParentCheck_sound _ (by decide)) ${n}_parent
theorem ${n}_cover_iff (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows ${n}) ↔
      ∀ k, HaltsAfter ${n} k → k+1+${d} ≤ B :=
  cover_iff_of_checks ${n} ${slot(h)} [${ds}] ${d} B (by decide) (by decide)
    (by decide) (by simp)
#print axioms ${n}_path
#print axioms ${n}_parent
#print axioms ${n}_leaf_parent
#print axioms ${n}_cover_iff
`});
 const footer=`/-- A6 branches from raw139 before the champion's long path. -/
def a6Sibling : PartialMachine := refine p139 (3,true) (some ⟨false,false,2⟩)
theorem A6_sibling : ∀ m, compatible (forgetHaltRows A6) m → compatible a6Sibling m :=
  leaf_extends_parent _ _ (ordinaryParentCheck_sound _ (by decide))
    ((parentCheck_iff _ _).mp (by decide))

def A6_certificate (B : Nat) (h : NeverHalts A6) :
    WeightedTNFCertificate B (forgetHaltRows A6) 6 :=
  forgetHaltRows_nonhaltCertificate B A6 (by decide) h

theorem A6_cover (B : Nat) (h : NeverHalts A6) :
    Cover (WeightedBound B) (forgetHaltRows A6) := (A6_certificate B h).toCover

#print axioms A6_sibling
#print axioms A6_certificate
#print axioms A6_cover
end BB6.Agent19HardRoot
`;
 return header+body.join("\n")+"\n"+footer;
}
process.stdout.write(generate(JSON.parse(fs.readFileSync(require("node:path").join(__dirname,"crosswalk.json"),"utf8")).records));
