import High2TailBase
import High2PhysicalBridge
import Lean.Elab.Tactic.Omega

namespace BB429High2Return

open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical
open BB429JFirstBranch BB429PhysicalBridge BB429DeltaPhysicalBridge
open BB429JuncHeadExcursion BB429High2PhysicalBridge
open BB429High2Tail BB429High2TailBase

/-- The high-2 endpoint is exactly the u=1 positive-MidA family. -/
theorem midA2_eq_midApos (v w : Nat) :
    midA2 v w = midApos 1 v w := by
  rfl

/-- The complete zipper suffix from the high-2 endpoint to Junc. -/
theorem midA2_to_junc0_of_base (u : Nat)
    (hbase : ∀ k : Nat,
      runWithDelta (4*k+36) (midAaux 0 k) =
        some (junc 0 0 (2*k+6), -4)) :
    runWithDelta (12*u+72) (midA2 (2*u+4) 1) =
      some (junc 0 0 (4*u+18), -((4*u+16 : Nat) : Int)) := by
  have h := midApos_to_junc0_of_base (2*u+4) (by omega) hbase
  simpa [midA2, midApos] using h

/-- From the synthetic J-chart state J(u,2u+2), the high-2 C/B branch
    now has a complete exact raw-source return to J(0,4u+18). The proof
    composes the source-connected C/B prefix with the universal MidA suffix.
    It does not assert that this synthetic J state is blank-root reachable. -/
theorem j_high2_to_junc_raw (u : Nat) :
    ∃ c', BB6Coverage.run BB429PhysicalFrontier.target429
      (4*u*u+44*u+204)
      {state:=BB429PhysicalFrontier.A,head:=0,tape:=BB429JPhysical.jTape u (2*u+2)}
        = some c' ∧
      BB429PhysicalBridge.Represents (junc 0 0 (4*u+18)) c' ∧
      c'.head = -((2*u+10 : Nat) : Int) := by
  let c0 : BB6Coverage.Config :=
    {state:=BB429PhysicalFrontier.A,head:=0,
      tape:=BB429JPhysical.jTape u (2*u+2)}
  obtain ⟨cMid, hprefix, hrepMid, hheadMid⟩ :=
    BB429High2PhysicalBridge.j_high2_to_midA_raw u
  have hrepPos :
      BB429PhysicalBridge.Represents (midApos 1 (2*u+4) 1) cMid := by
    simpa [midA2_eq_midApos] using hrepMid
  have htail :
      runWithDelta (12*u+72) (midApos 1 (2*u+4) 1) =
        some (junc 0 0 (4*u+18), -((4*u+16 : Nat) : Int)) := by
    simpa [midA2_eq_midApos] using
      (midA2_to_junc0_of_base u midAaux_zero_base)
  obtain ⟨cFinal, htailRaw, hrepFinal, hheadFinal⟩ :=
    BB429DeltaPhysicalBridge.source_runWithDelta_rep
      (12*u+72) (midApos 1 (2*u+4) 1) cMid hrepPos
      (junc 0 0 (4*u+18)) (-((4*u+16 : Nat) : Int)) htail
  have htotal :
      BB6Coverage.run BB429PhysicalFrontier.target429
        ((4*u*u+32*u+132)+(12*u+72)) c0 = some cFinal := by
    rw [BB6Bubble.run_add' BB429PhysicalFrontier.target429
      (4*u*u+32*u+132) (12*u+72) c0, hprefix]
    simp only [Option.bind_some]
    exact htailRaw
  have htime :
      (4*u*u+32*u+132)+(12*u+72) = 4*u*u+44*u+204 := by omega
  have hhead : cFinal.head = -((2*u+10 : Nat) : Int) := by
    rw [hheadFinal, hheadMid]
    omega
  exact ⟨cFinal, by simpa [c0, htime] using htotal, hrepFinal, hhead⟩

#print axioms midA2_to_junc0_of_base
#print axioms j_high2_to_junc_raw

end BB429High2Return
