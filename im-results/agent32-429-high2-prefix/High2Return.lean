import High2TailBase
import High2PhysicalBridge
import Lean.Elab.Tactic.Omega

namespace BB429High2Return

open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical
open BB429JFirstBranch BB429PhysicalBridge BB429DeltaPhysicalBridge
open BB429JuncHeadExcursion BB429High2PhysicalBridge
open BB429High2Tail BB429High2TailBase
open BB429SourceE1Delta BB429SourceE1Return BB429OddExcursion
open BB429FinishScanEDelta

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
  have hEq := midA2_eq_midApos (2*u+4) 1
  rw [hEq]
  have h := midApos_to_junc0_of_base (2*u+4) (by omega) hbase
  have htime : 6*(2*u+4)+48 = 12*u+72 := by omega
  have hparam : 2*(2*u+4)+10 = 4*u+18 := by omega
  have hdisp : 2*(2*u+4)+8 = 4*u+16 := by omega
  simpa [htime, hparam, hdisp] using h

/-- From the synthetic J-chart state J(u,2u+2), the high-2 C/B branch
    now has a complete exact raw-source return to J(0,4u+18). The proof
    composes the source-connected C/B prefix with the universal MidA suffix.
    It does not assert that this synthetic J state is blank-root reachable. -/
theorem j_high2_to_junc_raw (u : Nat) :
    ∃ c', BB6Coverage.run BB429PhysicalFrontier.target429
      (4*u*u+44*u+204)
      {state:=BB6Bubble.A,head:=0,tape:=BB429JPhysical.jTape u (2*u+2)}
        = some c' ∧
      BB429PhysicalBridge.Represents (junc 0 0 (4*u+18)) c' ∧
      c'.head = -((2*u+10 : Nat) : Int) := by
  let c0 : BB6Coverage.Config :=
    {state:=BB6Bubble.A,head:=0,
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

/-- After the high-2 return to Junc(0,0,4u+18), the exact Junc-cycle
    crossing theorem forces a later raw configuration strictly to the
    right of the original J-chart head. -/
theorem j_high2_crosses_origin_raw (u : Nat) :
    ∃ (steps : Nat) (cfg : Zipper) (c' : Config),
      BB6Coverage.run BB429PhysicalFrontier.target429
        (4*u*u+44*u+204+steps)
        {state:=BB6Bubble.A,head:=0,tape:=BB429JPhysical.jTape u (2*u+2)} =
          some c' ∧
      BB429PhysicalBridge.Represents cfg c' ∧
      c'.head > ((2*u+3 : Nat) : Int) := by
  let c0 : Config :=
    {state:=BB6Bubble.A,head:=0,
      tape:=BB429JPhysical.jTape u (2*u+2)}
  obtain ⟨cJ, hprefix, hrepJ, hheadJ⟩ := j_high2_to_junc_raw u
  obtain ⟨steps, cfg, d, hcrossRun, hcross⟩ :=
    BB429JuncHeadExcursion.juncCycle_crossing 0 (4*u+18)
      (3*u+12) (2*u+11) (by omega)
  obtain ⟨cFinal, hcrossRaw, hrepFinal, hheadFinal⟩ :=
    BB429DeltaPhysicalBridge.source_runWithDelta_rep steps
      (junc 0 0 (4*u+18)) cJ hrepJ cfg (d : Int) hcrossRun
  have htotal :
      BB6Coverage.run BB429PhysicalFrontier.target429
        ((4*u*u+44*u+204)+steps) c0 = some cFinal := by
    rw [BB6Bubble.run_add' BB429PhysicalFrontier.target429
      (4*u*u+44*u+204) steps c0, hprefix]
    simp only [Option.bind_some]
    exact hcrossRaw
  have hcrossInt : (2*(3*u+12) : Int) < (2*u+11 : Int) + (d : Int) := by
    omega
  have hhead : cFinal.head > ((2*u+3 : Nat) : Int) := by
    rw [hheadFinal, hheadJ]
    omega
  exact ⟨steps, cfg, cFinal, by simpa [c0] using htotal, hrepFinal, hhead⟩

#print axioms j_high2_crosses_origin_raw

/-- Exact endpoint alternatives for the finite Junc crossing. The terminal
    full-cycle remainder either leaves a Junc state with at most four right
    ones, or a midApos state after the maximal partial sweep. -/
theorem juncCycle_crossing_shape (u w k h : Nat) (hrel : h+w=2*k+5) :
    ∃ (steps : Nat) (cfg : Zipper) (d : Nat),
      runWithDelta steps (junc u 0 w) = some (cfg, (d : Int)) ∧
      2*k < h+d ∧
      ((w-juncCycleSpent (juncTerminalN u w) u ≤ 4 ∧
        steps = juncCycleTimeTotal (juncTerminalN u w) u ∧
        d = juncCycleSpent (juncTerminalN u w) u ∧
        cfg = junc (juncCycleU (juncTerminalN u w) u) 0
          (w-juncCycleSpent (juncTerminalN u w) u)) ∨
       (5 ≤ w-juncCycleSpent (juncTerminalN u w) u ∧
        ∃ N : Nat,
          N = (w-juncCycleSpent (juncTerminalN u w) u)/2-1 ∧
          steps = juncCycleTimeTotal (juncTerminalN u w) u + juncPosMidTime N 0 ∧
          d = juncCycleSpent (juncTerminalN u w) u + 2*N ∧
          cfg = midApos (juncCycleU (juncTerminalN u w) u-N)
            (2*(N-1)) (w-juncCycleSpent (juncTerminalN u w) u-2*(N-1)))) := by
  let n := juncTerminalN u w
  let spent := juncCycleSpent n u
  let rem := w-spent
  have hspent : spent ≤ w := by
    simpa [spent,n] using juncTerminal_spent_le u w
  have hcycles :
      runWithDelta (juncCycleTimeTotal n u) (junc u 0 w) =
        some (junc (juncCycleU n u) 0 rem, (spent : Int)) := by
    simpa [spent,rem] using juncCycle_iter_delta n u w hspent
  have hrel' : h+spent+rem=2*k+5 := by
    dsimp [rem]
    omega
  by_cases hsmall : rem ≤ 4
  · refine ⟨juncCycleTimeTotal n u, junc (juncCycleU n u) 0 rem,
      spent, ?_, ?_, ?_⟩
    · simpa using hcycles
    · omega
    · left
      simpa [n,spent,rem] using
        (show rem ≤ 4 ∧
          juncCycleTimeTotal n u = juncCycleTimeTotal n u ∧
          spent = spent ∧
          junc (juncCycleU n u) 0 rem = junc (juncCycleU n u) 0 rem
          from ⟨hsmall,rfl,rfl,rfl⟩)
  · have hrem : 5 ≤ rem := by omega
    have hb := juncTerminal_final_bounds u w
      (by simpa [rem,spent,n] using hrem)
    let N := rem/2-1
    have hN : 1 ≤ N := by dsimp [N]; exact hb.1
    have hU : N ≤ juncCycleU n u := by dsimp [N]; exact hb.2.1
    have hwN : 2*N-1 ≤ rem := by dsimp [N]; exact hb.2.2.1
    have hmid := juncPos_iter_mid_delta N (juncCycleU n u) 0 rem hN hU hwN
    refine ⟨juncCycleTimeTotal n u + juncPosMidTime N 0,
      midApos (juncCycleU n u-N) (2*(N-1)) (rem-2*(N-1)),
      spent+2*N, ?_, ?_, ?_⟩
    · rw [runWithDelta_add,hcycles]
      simp only [Option.bind_some]
      rw [hmid]
      simp only [Option.map_some]
      simp [Int.natCast_add,Int.natCast_mul]
    · omega
    · right
      refine ⟨hrem,N,?_,?_,?_,?_⟩
      · dsimp [N]
      · simp [n,spent,rem]
      · simp [n,spent,rem]
      · simp [n,spent,rem]

#print axioms juncCycle_crossing_shape

end BB429High2Return
