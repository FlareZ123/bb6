import CResidualMass2000
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent4CResidualMass10000

open BB6.Agent4CResidualMass2000

/-- One-pass prefix of the original source section orbit.  It stops as soon
    as the certified weighted mass has passed 10,000, since no target of
    weighted mass at most 10,000 can occur afterwards. -/
def rootTrace : Nat → Option (Nat × Nat) → List (Option (Nat × Nat))
  | 0, s => [s]
  | n+1, none => [none]
  | n+1, some (a,k) =>
      if 10000 < a+2*k then [some (a,k)]
      else some (a,k) :: rootTrace n (BB6.Agent11Fuel.secNextFuel (a,k))

/-- A state is one of the low/high Machine C stopping targets of raw mass at
    most 10,000.  For an odd first coordinate x≥3, its high-row index is
    uniquely recovered as (x-3)/2, so this predicate has no unbounded search. -/
def isStopTarget : Option (Nat × Nat) → Bool
  | none => false
  | some (x,y) =>
      decide (x+2*y ≤ 10000) &&
        ((List.range 5).any
          (fun m => decide (x=1 ∧ y=lowStopTargetY m)) ||
          (if 3 ≤ x ∧ x % 2 = 1 then
            (List.range 5).any
              (fun m => decide (highStopTarget ((x-3)/2) m = (x,y)))
           else false))

/-- Kernel-checked one-pass evaluation of the faithful original-source
    orbit.  This is a single shared orbit computation, rather than a
    repeated per-target call to massStopRoot. -/
theorem rootTrace_no_stop_target :
    (rootTrace 5000 (some (5,1))).all (fun s => !isStopTarget s) = true := by
  decide

/-- The original source fuel evaluator has the same weighted-mass growth
    theorem as the source section semantics. -/
theorem runFuel_weight_growth (n a k x y : Nat)
    (h : BB6.Agent11Fuel.runFuel n (some (a,k)) = some (x,y)) :
    a+2*k+2*n ≤ x+2*y := by
  have hsrc : BB6.Agent8Section.run BB6.Agent8Section.secNext n (some (a,k)) =
      some (x,y) := by
    simpa only [BB6.Agent11Fuel.runFuel_eq] using h
  exact BB6.Agent11Mass.run_generic_weight_growth n a k x y hsrc

theorem runFuel_none (n : Nat) :
    BB6.Agent11Fuel.runFuel n (none : Option (Nat × Nat)) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [BB6.Agent11Fuel.runFuel, ih]

/-- Any source run that reaches a target of mass at most 10,000 must appear
    in the early-stopped shared orbit prefix. -/
theorem rootTrace_contains_of_run (fuel n : Nat) (s : Option (Nat × Nat))
    (x y : Nat) (hn : n ≤ fuel)
    (hrun : BB6.Agent11Fuel.runFuel n s = some (x,y))
    (hmass : x+2*y ≤ 10000) :
    some (x,y) ∈ rootTrace fuel s := by
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
          simp [rootTrace]
  | succ fuel ih =>
      cases s with
      | none => simp [runFuel_none] at hrun
      | some p =>
          rcases p with ⟨a,k⟩
          by_cases hstop : 10000 < a+2*k
          · have hgrowth := runFuel_weight_growth n a k x y hrun
            omega
          · have htrace : rootTrace (fuel+1) (some (a,k)) =
                some (a,k) :: rootTrace fuel (BB6.Agent11Fuel.secNextFuel (a,k)) := by
              simp [rootTrace, hstop]
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

/-- The half-mass bound on the source section orbit places every reachable
    target of mass at most 10,000 within the shared prefix above. -/
theorem rootTrace_contains_of_sectionReach (x y : Nat)
    (hmass : x+2*y ≤ 10000)
    (hr : BB6.Agent11Mass.SectionReach x y) :
    some (x,y) ∈ rootTrace 5000 (some (5,1)) := by
  obtain ⟨n,hn,hrun⟩ :=
    (BB6.Agent11Mass.section_reach_iff_half_bound x y).mp hr
  have hn' : n ≤ 5000 := by omega
  have hrun' : BB6.Agent11Fuel.runFuel n (some (5,1)) = some (x,y) := by
    simpa only [BB6.Agent11Fuel.runFuel_eq] using hrun
  exact rootTrace_contains_of_run 5000 n (some (5,1)) x y hn' hrun' hmass

/-- No low/high target of raw mass at most 10,000 is on the blank-root
    section orbit. -/
theorem no_root_target (x y : Nat)
    (hmass : x+2*y ≤ 10000)
    (hpred : isStopTarget (some (x,y)) = true) :
    ¬ BB6.Agent11Mass.SectionReach x y := by
  intro hr
  have hmem := rootTrace_contains_of_sectionReach x y hmass hr
  have hnot := (List.all_eq_true.mp rootTrace_no_stop_target) (some (x,y)) hmem
  simp [hpred] at hnot

theorem low_is_stop_target (m : Nat) (hm : m ≤ 4)
    (hmass : 1+2*lowStopTargetY m ≤ 10000) :
    isStopTarget (some (1,lowStopTargetY m)) = true := by
  unfold isStopTarget
  have hmass' : 1+2*(2^(2*m+3)-(3*m+4)) ≤ 10000 := by
    simpa [lowStopTargetY] using hmass
  simp [hmass', lowStopTargetY]
  exact ⟨m, by omega, rfl⟩

theorem high_is_stop_target (j m : Nat) (hm : m ≤ 4)
    (hmass : (highStopTarget j m).1 + 2*(highStopTarget j m).2 ≤ 10000) :
    isStopTarget (some (highStopTarget j m)) = true := by
  unfold isStopTarget
  have hmass' : 2*j+3 + 2*(2^(2*m+2)*(j+3)-(j+3*m+5)) ≤ 10000 := by
    simpa [highStopTarget] using hmass
  have hx : 3 ≤ 2*j+3 := by omega
  have hodd : (2*j+3) % 2 = 1 := by omega
  simp [hmass', hx, hodd, highStopTarget]
  exact ⟨m, by omega, rfl⟩

/-- For m≥5, the low raw mass already exceeds the 10,000 cutoff. -/
theorem low_mass_ge_16347 (m : Nat) (hm : 5 ≤ m) :
    16347 ≤ BB6.Agent4MassBounds.lowRawMass m := by
  by_cases h5 : m=5
  · subst m
    rw [BB6.Agent4MassBounds.lowRawMass_eq]
    decide
  · have hm6 : 6 ≤ m := by omega
    rw [BB6.Agent4MassBounds.lowRawMass_eq]
    have hlin := BB6.Agent4MassBounds.pow_linear_from_four m (by omega)
    have hfac : 4 ≤ 2^(m-4) := by
      have he : 2 ≤ m-4 := by omega
      calc
        4 = 2^2 := by decide
        _ ≤ 2^(m-4) := Nat.pow_le_pow_right (by decide) he
    have hexp : 2^(2*m+4) = 2^(m+8)*2^(m-4) := by
      rw [show 2*m+4 = (m+8)+(m-4) by omega, Nat.pow_add]
    have hprod : 4*(4096+6*(m-4)) ≤ 2^(m+8)*2^(m-4) := by
      calc
        4*(4096+6*(m-4)) ≤ 2^(m-4)*2^(m+8) := Nat.mul_le_mul hfac hlin
        _ = 2^(m+8)*2^(m-4) := Nat.mul_comm _ _
    rw [hexp]
    omega

/-- For m≥5, every high-row target has raw mass above the 10,000 cutoff. -/
theorem high_mass_ge_12287 (j m : Nat) (hm : 5 ≤ m) :
    12287 ≤ BB6.Agent4MassBounds.highRawMass j m := by
  rw [BB6.Agent4MassBounds.highRawMass_eq]
  have hlin := BB6.Agent4MassBounds.high_pow_linear_from_four m (by omega)
  have hfac : 2 ≤ 2^(m-4) := by
    have he : 1 ≤ m-4 := by omega
    calc
      2 = 2^1 := by decide
      _ ≤ 2^(m-4) := Nat.pow_le_pow_right (by decide) he
  have hj3 : 3 ≤ j+3 := by omega
  have hprod : 6*(2048+6*(m-4)) ≤ 2^(m+7)*2^(m-4)*(j+3) := by
    calc
      6*(2048+6*(m-4)) = (2048+6*(m-4))*6 := by omega
      _ ≤ 2^(m+7)*6 := Nat.mul_le_mul_right 6 hlin
      _ = 2^(m+7)*(2*3) := by congr 1 <;> omega
      _ ≤ 2^(m+7)*(2^(m-4)*3) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right 3 hfac)
      _ = 2^(m+7)*2^(m-4)*3 := by rw [← Nat.mul_assoc]
      _ ≤ 2^(m+7)*2^(m-4)*(j+3) := Nat.mul_le_mul_left _ hj3
  have hexp : 2^(2*m+3) = 2^(m+7)*2^(m-4) := by
    rw [show 2*m+3 = (m+7)+(m-4) by omega, Nat.pow_add]
  rw [hexp]
  omega

theorem low_raw_mass_box_10000 (m : Nat)
    (h : BB6.Agent4MassBounds.lowRawMass m ≤ 10000) : m ≤ 4 := by
  by_cases hm : 5 ≤ m
  · have hbig := low_mass_ge_16347 m hm
    omega
  · omega

theorem high_raw_mass_box_10000 (j m : Nat)
    (h : BB6.Agent4MassBounds.highRawMass j m ≤ 10000) : m ≤ 4 := by
  by_cases hm : 5 ≤ m
  · have hbig := high_mass_ge_12287 j m hm
    omega
  · omega

/-- Every low stopping target of raw mass at most 10,000 is unreachable. -/
theorem low_no_section_reach_under_mass10000 (m : Nat)
    (hm : BB6.Agent4MassBounds.lowRawMass m ≤ 10000) :
    ¬ BB6.Agent11Mass.SectionReach 1 (lowStopTargetY m) := by
  have hmBound := low_raw_mass_box_10000 m hm
  have hmass : 1+2*lowStopTargetY m ≤ 10000 := by
    rw [← low_target_weighted_mass]
    exact hm
  exact no_root_target 1 (lowStopTargetY m) hmass
    (low_is_stop_target m hmBound hmass)

/-- Every high stopping target of raw mass at most 10,000 is unreachable. -/
theorem high_no_section_reach_under_mass10000 (j m : Nat)
    (hm : BB6.Agent4MassBounds.highRawMass j m ≤ 10000) :
    ¬ BB6.Agent11Mass.SectionReach (highStopTarget j m).1 (highStopTarget j m).2 := by
  have hmBound := high_raw_mass_box_10000 j m hm
  have hmass :
      (highStopTarget j m).1 + 2*(highStopTarget j m).2 ≤ 10000 := by
    rw [← high_target_weighted_mass]
    exact hm
  exact no_root_target (highStopTarget j m).1 (highStopTarget j m).2 hmass
    (high_is_stop_target j m hmBound hmass)

theorem low_reach_implies_mass_gt_10000 (m : Nat)
    (hr : BB6.Agent11Mass.SectionReach 1 (lowStopTargetY m)) :
    10000 < BB6.Agent4MassBounds.lowRawMass m := by
  by_cases h : 10000 < BB6.Agent4MassBounds.lowRawMass m
  · exact h
  · have hm : BB6.Agent4MassBounds.lowRawMass m ≤ 10000 := by omega
    exact False.elim ((low_no_section_reach_under_mass10000 m hm) hr)

theorem high_reach_implies_mass_gt_10000 (j m : Nat)
    (hr : BB6.Agent11Mass.SectionReach (highStopTarget j m).1 (highStopTarget j m).2) :
    10000 < BB6.Agent4MassBounds.highRawMass j m := by
  by_cases h : 10000 < BB6.Agent4MassBounds.highRawMass j m
  · exact h
  · have hm : BB6.Agent4MassBounds.highRawMass j m ≤ 10000 := by omega
    exact False.elim ((high_no_section_reach_under_mass10000 j m hm) hr)

#print axioms rootTrace_no_stop_target
#print axioms rootTrace_contains_of_sectionReach
#print axioms low_no_section_reach_under_mass10000
#print axioms high_no_section_reach_under_mass10000
#print axioms low_reach_implies_mass_gt_10000
#print axioms high_reach_implies_mass_gt_10000

end BB6.Agent4CResidualMass10000
