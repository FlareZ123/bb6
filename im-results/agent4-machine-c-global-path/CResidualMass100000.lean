import CResidualMass10000
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent4CResidualMass100000

open BB6.Agent4CResidualMass10000
open BB6.Agent4CResidualMass2000

/-- The original-source root orbit, stopped at the first state whose weighted
    mass exceeds 100,000. -/
def rootTrace100000 : Nat → Option (Nat × Nat) → List (Option (Nat × Nat))
  | 0, s => [s]
  | n+1, none => [none]
  | n+1, some (a,k) =>
      if 100000 < a+2*k then [some (a,k)]
      else some (a,k) :: rootTrace100000 n (BB6.Agent11Fuel.secNextFuel (a,k))

/-- Low/high stopping targets in the 100,000 raw-mass box.  The odd high-row
    first coordinate determines j=(x-3)/2, so the predicate stays finite. -/
def isStopTarget100000 : Option (Nat × Nat) → Bool
  | none => false
  | some (x,y) =>
      decide (x+2*y ≤ 100000) &&
        ((List.range 7).any
          (fun m => decide (x=1 ∧ y=BB6.Agent4CResidualMass2000.lowStopTargetY m)) ||
          (if 3 ≤ x ∧ x % 2 = 1 then
            (List.range 7).any
              (fun m => decide
                (BB6.Agent4CResidualMass2000.highStopTarget ((x-3)/2) m = (x,y)))
           else false))

theorem pow_linear_from_seven (m : Nat) (hm : 7 ≤ m) :
    16384 + 6*(m-7) ≤ 2^(m+8) := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases h : m=6
      · subst m
        decide
      · have hm' : 7 ≤ m := by omega
        have hprev := ih hm'
        have hp : 2^(m+1+8) = 2*2^(m+8) := by
          rw [show m+1+8 = (m+8)+1 by omega, Nat.pow_succ]
          simp [Nat.mul_comm]
        rw [hp]
        omega

theorem high_pow_linear_from_seven (m : Nat) (hm : 7 ≤ m) :
    8192 + 6*(m-7) ≤ 2^(m+7) := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases h : m=6
      · subst m
        decide
      · have hm' : 7 ≤ m := by omega
        have hprev := ih hm'
        have hp : 2^(m+1+7) = 2*2^(m+7) := by
          rw [show m+1+7 = (m+7)+1 by omega, Nat.pow_succ]
          simp [Nat.mul_comm]
        rw [hp]
        omega

/-- For m≥7, low stopping targets have raw mass at least 131,023. -/
theorem low_mass_ge_131023 (m : Nat) (hm : 7 ≤ m) :
    131023 ≤ BB6.Agent4MassBounds.lowRawMass m := by
  rw [BB6.Agent4MassBounds.lowRawMass_eq]
  have hlin := pow_linear_from_seven m hm
  have hfac : 8 ≤ 2^(m-4) := by
    have he : 3 ≤ m-4 := by omega
    calc
      8 = 2^3 := by decide
      _ ≤ 2^(m-4) := Nat.pow_le_pow_right (by decide) he
  have hexp : 2^(2*m+4) = 2^(m+8)*2^(m-4) := by
    rw [show 2*m+4 = (m+8)+(m-4) by omega, Nat.pow_add]
  have hprod : 8*(16384+6*(m-7)) ≤ 2^(m+8)*2^(m-4) := by
    calc
      8*(16384+6*(m-7)) ≤ 2^(m-4)*2^(m+8) := Nat.mul_le_mul hfac hlin
      _ = 2^(m+8)*2^(m-4) := Nat.mul_comm _ _
  rw [hexp]
  omega

/-- For m≥7, every high-row target has raw mass at least 196,559. -/
theorem high_mass_ge_196559 (j m : Nat) (hm : 7 ≤ m) :
    196559 ≤ BB6.Agent4MassBounds.highRawMass j m := by
  rw [BB6.Agent4MassBounds.highRawMass_eq]
  have hlin := high_pow_linear_from_seven m hm
  have hfac : 8 ≤ 2^(m-4) := by
    have he : 3 ≤ m-4 := by omega
    calc
      8 = 2^3 := by decide
      _ ≤ 2^(m-4) := Nat.pow_le_pow_right (by decide) he
  have hj3 : 3 ≤ j+3 := by omega
  have hprod :
      24*(8192+6*(m-7)) ≤ 2^(m+7)*2^(m-4)*(j+3) := by
    calc
      24*(8192+6*(m-7)) = (8192+6*(m-7))*24 := by omega
      _ ≤ 2^(m+7)*24 := Nat.mul_le_mul_right 24 hlin
      _ = 2^(m+7)*(8*3) := by congr 1 <;> omega
      _ ≤ 2^(m+7)*(2^(m-4)*3) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right 3 hfac)
      _ = 2^(m+7)*2^(m-4)*3 := by rw [← Nat.mul_assoc]
      _ ≤ 2^(m+7)*2^(m-4)*(j+3) := Nat.mul_le_mul_left _ hj3
  have hexp : 2^(2*m+3) = 2^(m+7)*2^(m-4) := by
    rw [show 2*m+3 = (m+7)+(m-4) by omega, Nat.pow_add]
  rw [hexp]
  omega

theorem low_raw_mass_box_100000 (m : Nat)
    (h : BB6.Agent4MassBounds.lowRawMass m ≤ 100000) : m ≤ 6 := by
  by_cases hm : 7 ≤ m
  · have hbig := low_mass_ge_131023 m hm
    omega
  · omega

theorem high_raw_mass_box_100000 (j m : Nat)
    (h : BB6.Agent4MassBounds.highRawMass j m ≤ 100000) : m ≤ 6 := by
  by_cases hm : 7 ≤ m
  · have hbig := high_mass_ge_196559 j m hm
    omega
  · omega

/-- Any source run reaching a target of mass at most 100,000 appears in the
    early-stopped shared prefix. -/
theorem rootTrace100000_contains_of_run (fuel n : Nat)
    (s : Option (Nat × Nat)) (x y : Nat)
    (hn : n ≤ fuel)
    (hrun : BB6.Agent11Fuel.runFuel n s = some (x,y))
    (hmass : x+2*y ≤ 100000) :
    some (x,y) ∈ rootTrace100000 fuel s := by
  induction fuel generalizing n s with
  | zero =>
      have hn0 : n=0 := by omega
      subst n
      cases s with
      | none => simp [BB6.Agent11Fuel.runFuel] at hrun
      | some p =>
          rcases p with ⟨a,k⟩
          simp only [BB6.Agent11Fuel.runFuel] at hrun
          have hp : (a,k)=(x,y) := Option.some.inj hrun
          cases hp
          simp [rootTrace100000]
  | succ fuel ih =>
      cases s with
      | none => simp [BB6.Agent4CResidualMass10000.runFuel_none] at hrun
      | some p =>
          rcases p with ⟨a,k⟩
          by_cases hstop : 100000 < a+2*k
          · have hgrowth :=
              BB6.Agent4CResidualMass10000.runFuel_weight_growth n a k x y hrun
            omega
          · have htrace : rootTrace100000 (fuel+1) (some (a,k)) =
                some (a,k) :: rootTrace100000 fuel
                  (BB6.Agent11Fuel.secNextFuel (a,k)) := by
              simp [rootTrace100000, hstop]
            rw [htrace]
            simp only [List.mem_cons]
            cases n with
            | zero =>
                left
                simp only [BB6.Agent11Fuel.runFuel] at hrun
                have hp : (a,k)=(x,y) := Option.some.inj hrun
                cases hp
                rfl
            | succ n =>
                right
                have hrun' :
                    BB6.Agent11Fuel.runFuel n
                      (BB6.Agent11Fuel.secNextFuel (a,k)) = some (x,y) := by
                  simpa only [BB6.Agent11Fuel.runFuel_succ_head, Option.bind_some] using hrun
                exact ih n (BB6.Agent11Fuel.secNextFuel (a,k)) (by omega) hrun'

theorem rootTrace100000_contains_of_sectionReach (x y : Nat)
    (hmass : x+2*y ≤ 100000)
    (hr : BB6.Agent11Mass.SectionReach x y) :
    some (x,y) ∈ rootTrace100000 50000 (some (5,1)) := by
  obtain ⟨n,hn,hrun⟩ :=
    (BB6.Agent11Mass.section_reach_iff_half_bound x y).mp hr
  have hn' : n ≤ 50000 := by omega
  have hrun' : BB6.Agent11Fuel.runFuel n (some (5,1)) = some (x,y) := by
    simpa only [BB6.Agent11Fuel.runFuel_eq] using hrun
  exact rootTrace100000_contains_of_run 50000 n (some (5,1)) x y hn' hrun' hmass

theorem rootTrace100000_no_stop_target :
    (rootTrace100000 50000 (some (5,1))).all
      (fun s => !isStopTarget100000 s) = true := by
  decide

theorem no_root_target100000 (x y : Nat)
    (hmass : x+2*y ≤ 100000)
    (hpred : isStopTarget100000 (some (x,y)) = true) :
    ¬ BB6.Agent11Mass.SectionReach x y := by
  intro hr
  have hmem := rootTrace100000_contains_of_sectionReach x y hmass hr
  have hnot := (List.all_eq_true.mp rootTrace100000_no_stop_target) (some (x,y)) hmem
  simp [hpred] at hnot

theorem low_is_stop_target100000 (m : Nat) (hm : m ≤ 6)
    (hmass : 1+2*BB6.Agent4CResidualMass2000.lowStopTargetY m ≤ 100000) :
    isStopTarget100000
      (some (1,BB6.Agent4CResidualMass2000.lowStopTargetY m)) = true := by
  unfold isStopTarget100000
  have hmass' :
      1+2*(2^(2*m+3)-(3*m+4)) ≤ 100000 := by
    simpa [BB6.Agent4CResidualMass2000.lowStopTargetY] using hmass
  simp [hmass', BB6.Agent4CResidualMass2000.lowStopTargetY]
  exact ⟨m, by omega, rfl⟩

theorem high_is_stop_target100000 (j m : Nat) (hm : m ≤ 6)
    (hmass :
      (BB6.Agent4CResidualMass2000.highStopTarget j m).1 +
        2*(BB6.Agent4CResidualMass2000.highStopTarget j m).2 ≤ 100000) :
    isStopTarget100000
      (some (BB6.Agent4CResidualMass2000.highStopTarget j m)) = true := by
  unfold isStopTarget100000
  have hmass' :
      2*j+3 +
        2*(2^(2*m+2)*(j+3)-(j+3*m+5)) ≤ 100000 := by
    simpa [BB6.Agent4CResidualMass2000.highStopTarget] using hmass
  have hx : 3 ≤ 2*j+3 := by omega
  have hodd : (2*j+3) % 2 = 1 := by omega
  simp [hmass', hx, hodd, BB6.Agent4CResidualMass2000.highStopTarget]
  exact ⟨m, by omega, rfl⟩

theorem low_no_section_reach_under_mass100000 (m : Nat)
    (hm : BB6.Agent4MassBounds.lowRawMass m ≤ 100000) :
    ¬ BB6.Agent11Mass.SectionReach 1
      (BB6.Agent4CResidualMass2000.lowStopTargetY m) := by
  have hmBound := low_raw_mass_box_100000 m hm
  have hmass :
      1+2*BB6.Agent4CResidualMass2000.lowStopTargetY m ≤ 100000 := by
    rw [← BB6.Agent4CResidualMass2000.low_target_weighted_mass]
    exact hm
  exact no_root_target100000 1 _ hmass
    (low_is_stop_target100000 m hmBound hmass)

theorem high_no_section_reach_under_mass100000 (j m : Nat)
    (hm : BB6.Agent4MassBounds.highRawMass j m ≤ 100000) :
    ¬ BB6.Agent11Mass.SectionReach
      (BB6.Agent4CResidualMass2000.highStopTarget j m).1
      (BB6.Agent4CResidualMass2000.highStopTarget j m).2 := by
  have hmBound := high_raw_mass_box_100000 j m hm
  have hmass :
      (BB6.Agent4CResidualMass2000.highStopTarget j m).1 +
        2*(BB6.Agent4CResidualMass2000.highStopTarget j m).2 ≤ 100000 := by
    rw [← BB6.Agent4CResidualMass2000.high_target_weighted_mass]
    exact hm
  exact no_root_target100000
    (BB6.Agent4CResidualMass2000.highStopTarget j m).1
    (BB6.Agent4CResidualMass2000.highStopTarget j m).2 hmass
    (high_is_stop_target100000 j m hmBound hmass)

theorem low_reach_implies_mass_gt_100000 (m : Nat)
    (hr : BB6.Agent11Mass.SectionReach 1
      (BB6.Agent4CResidualMass2000.lowStopTargetY m)) :
    100000 < BB6.Agent4MassBounds.lowRawMass m := by
  by_cases h : 100000 < BB6.Agent4MassBounds.lowRawMass m
  · exact h
  · have hm : BB6.Agent4MassBounds.lowRawMass m ≤ 100000 := by omega
    exact False.elim ((low_no_section_reach_under_mass100000 m hm) hr)

theorem high_reach_implies_mass_gt_100000 (j m : Nat)
    (hr : BB6.Agent11Mass.SectionReach
      (BB6.Agent4CResidualMass2000.highStopTarget j m).1
      (BB6.Agent4CResidualMass2000.highStopTarget j m).2) :
    100000 < BB6.Agent4MassBounds.highRawMass j m := by
  by_cases h : 100000 < BB6.Agent4MassBounds.highRawMass j m
  · exact h
  · have hm : BB6.Agent4MassBounds.highRawMass j m ≤ 100000 := by omega
    exact False.elim ((high_no_section_reach_under_mass100000 j m hm) hr)

#print axioms rootTrace100000_no_stop_target
#print axioms rootTrace100000_contains_of_sectionReach
#print axioms low_no_section_reach_under_mass100000
#print axioms high_no_section_reach_under_mass100000
#print axioms low_reach_implies_mass_gt_100000
#print axioms high_reach_implies_mass_gt_100000

end BB6.Agent4CResidualMass100000
