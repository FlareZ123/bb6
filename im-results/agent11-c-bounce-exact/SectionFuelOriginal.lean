import SectionMassOriginal
import FastSectionDef
import GenericSection
import Std
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Fuel
open BB6.Agent46

/-- Structurally recursive bounce evaluator that normalizes under kernel reduction. -/
def bounceFuel : Nat → Nat → Nat → Nat × Option (Nat × Nat)
 | 0,_,_ => (0,none)
 | fuel+1,k,c =>
    if c<4 then (0,none)
    else if k%2=1 then
      if c≤2*k+6 then (c,some (2*k+6-c,c))
      else
        let out := bounceFuel fuel (2*k+3) (c-(2*k+3))
        (2*k+4+out.1,out.2)
    else if c=4 then (2,some (2*k+2,3))
    else if c=5 then (2,none)
    else if c≤2*k+8 then (c-3,some (2*k+8-c,c-1))
    else
      let out := bounceFuel fuel (2*k+4) (c-(2*k+5))
      (2*k+3+out.1,out.2)

/-- Exact equivalence to the original well-founded recursive bounce whenever
    the explicit evaluator fuel covers the initial height. -/
theorem bounceFuel_correct (c : Nat) :
  ∀ fuel k, c≤fuel → bounceFuel fuel k c = bounce k c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro fuel k hf
    cases fuel with
    | zero =>
      have hc:c=0 := by omega
      subst c
      simp [bounceFuel,bounce.eq_1]
    | succ fuel =>
      rw [bounceFuel, bounce.eq_1]
      by_cases hc : c<4
      · simp [hc]
      simp only [hc,ite_false]
      by_cases hk : k%2=1
      · simp only [hk,ite_true]
        by_cases hs : c≤2*k+6
        · simp [hs]
        · simp only [hs,ite_false]
          have ht : c-(2*k+3)<c := Nat.sub_lt (by omega) (by omega)
          have hb : c-(2*k+3)≤fuel := by omega
          rw [ih (c-(2*k+3)) ht fuel (2*k+3) hb]
      · simp only [hk,ite_false]
        by_cases hc4:c=4
        · simp [hc4]
        simp only [hc4,ite_false]
        by_cases hc5:c=5
        · simp [hc5]
        simp only [hc5,ite_false]
        by_cases hs:c≤2*k+8
        · simp [hs]
        simp only [hs,ite_false]
        have ht : c-(2*k+5)<c := Nat.sub_lt (by omega) (by omega)
        have hb : c-(2*k+5)≤fuel := by omega
        rw [ih (c-(2*k+5)) ht fuel (2*k+4) hb]

@[simp] theorem bounceFuel_self (k c : Nat) : bounceFuel c k c = bounce k c :=
  bounceFuel_correct c c k (Nat.le_refl c)

/-- Exact evaluator for original BB6.Agent46.secNext. -/
def secNextFuel (p : Nat×Nat) : Option (Nat×Nat) :=
 let (a,k):=p
 if a=0 then
  if k=0 then none else if k=1 then some (0,4)
  else (bounceFuel (2*k+1) 1 (2*k+1)).2
 else if a=1 then
  if k=0 then some (5,1) else if k=1 then some (2,3) else if k=2 then some (2,5)
  else if k=3 then some (0,7) else (bounceFuel (2*k-3) 4 (2*k-3)).2
 else if k=0 then some (a-2,2) else if 2*k≤a then some (a-2*k,2*k+2)
 else (bounceFuel (2*k-a+3) (a-1) (2*k-a+3)).2

theorem secNextFuel_eq (a k : Nat) : secNextFuel (a,k) = secNext (a,k) := by
  unfold secNextFuel secNext exactSection
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [ha0,hk0]
    · by_cases hk1 : k=1
      · simp [ha0,hk0,hk1]
      · simp [ha0,hk0,hk1,bounceFuel_self]
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [ha0,ha1,hk0]
      · by_cases hk1 : k=1
        · simp [ha0,ha1,hk0,hk1]
        · by_cases hk2 : k=2
          · simp [ha0,ha1,hk0,hk1,hk2]
          · by_cases hk3 : k=3
            · simp [ha0,ha1,hk0,hk1,hk2,hk3]
            · simp [ha0,ha1,hk0,hk1,hk2,hk3,bounceFuel_self]
    · by_cases hk0 : k=0
      · simp [ha0,ha1,hk0]
      · by_cases hr : 2*k≤a
        · simp [ha0,ha1,hk0,hr]
        · simp [ha0,ha1,hk0,hr,bounceFuel_self]

/-- Structurally recursive faithful section iteration with executable kernel reduction. -/
def runFuel : Nat → Option (Nat×Nat) → Option (Nat×Nat)
  | 0,s => s
  | n+1,s => (runFuel n s).bind secNextFuel

theorem runFuel_eq (n : Nat) (s : Option (Nat×Nat)) :
 runFuel n s = BB6.Agent8Section.run secNext n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [runFuel,BB6.Agent8Section.run,ih]
    cases hp : BB6.Agent8Section.run secNext n s with
    | none => simp [hp]
    | some p =>
      rcases p with ⟨a,k⟩
      simpa [hp] using secNextFuel_eq a k

/-- Executable finite blank-root reachability query from the original-source mass bound. -/
def reachableFastBool (x y : Nat) : Bool :=
  (List.range (x+2*y+1)).any
    (fun n => decide (runFuel n (some (5,1)) = some (x,y)))

theorem reachableFastBool_correct (x y : Nat) :
  reachableFastBool x y = true ↔ BB6.Agent11Mass.SectionReach x y := by
  rw [BB6.Agent11Mass.section_reach_iff_bounded]
  simp only [reachableFastBool,List.any_eq_true,List.mem_range,decide_eq_true_eq]
  constructor
  · rintro ⟨n,hn,h⟩
    refine ⟨n,by omega,?_⟩
    simpa only [runFuel_eq] using h
  · rintro ⟨n,hn,h⟩
    refine ⟨n,by omega,?_⟩
    simpa only [runFuel_eq] using h

/-- Concrete universal nonreachability certificates are now possible with
    kernel reduction (here, two small members of the second halting family). -/
theorem no_second_gate_m0 : ¬ BB6.Agent11Mass.SectionReach 5 10 := by
  intro hr
  have h := (reachableFastBool_correct 5 10).mpr hr
  have hc : reachableFastBool 5 10 = false := by decide
  simp [hc] at h

theorem no_second_gate_m1 : ¬ BB6.Agent11Mass.SectionReach 11 100 := by
  intro hr
  have h := (reachableFastBool_correct 11 100).mpr hr
  have hc : reachableFastBool 11 100 = false := by decide
  simp [hc] at h


/-- Single-pass prefix scan, avoiding the quadratic repeated-run work of
    reachableFastBool. Faithful by a direct induction on prefix length. -/
theorem runFuel_commute (n : Nat) : ∀ s : Option (Nat×Nat),
  runFuel n (s.bind secNextFuel) = (runFuel n s).bind secNextFuel := by
  induction n with
  | zero =>
    intro s
    rfl
  | succ n ih =>
    intro s
    change (runFuel n (s.bind secNextFuel)).bind secNextFuel =
      ((runFuel n s).bind secNextFuel).bind secNextFuel
    rw [ih]

theorem runFuel_succ_head (n : Nat) (s : Option (Nat×Nat)) :
  runFuel (n+1) s = runFuel n (s.bind secNextFuel) := by
  exact (runFuel_commute n s).symm

def hasHit (x y : Nat) : Nat → Option (Nat×Nat) → Bool
  | 0,s => decide (s=some (x,y))
  | n+1,s => if s=some (x,y) then true else hasHit x y n (s.bind secNextFuel)

theorem hasHit_iff (fuel x y : Nat) :
  ∀ s : Option (Nat×Nat),
    hasHit x y fuel s = true ↔
      ∃ n ≤ fuel, runFuel n s = some (x,y) := by
  induction fuel with
  | zero =>
    intro s
    simp only [hasHit, decide_eq_true_eq]
    constructor
    · intro h
      exact ⟨0,by omega,by simpa only [runFuel] using h⟩
    · rintro ⟨n,hn,h⟩
      have hn0 : n=0 := by omega
      subst n
      simpa only [runFuel] using h
  | succ fuel ih =>
    intro s
    by_cases hstart : s=some (x,y)
    · simp only [hasHit, hstart, ite_true]
      constructor
      · intro _
        exact ⟨0,by omega,by simpa only [runFuel] using hstart⟩
      · intro _
        trivial
    · simp only [hasHit,hstart,ite_false]
      rw [ih (s.bind secNextFuel)]
      constructor
      · rintro ⟨n,hn,h⟩
        refine ⟨n+1,by omega,?_⟩
        simpa only [runFuel_succ_head] using h
      · rintro ⟨n,hn,h⟩
        cases n with
        | zero =>
          have hs : s=some (x,y) := by simpa only [runFuel] using h
          exact False.elim (hstart hs)
        | succ n =>
          refine ⟨n,by omega,?_⟩
          simpa only [runFuel_succ_head] using h

/-- Sound and complete source-checked blank target decision using a linear
    orbit scan and the independent all-time rank upper bound. -/
theorem hasHitFull_iff (x y : Nat) :
  hasHit x y (x+2*y) (some (5,1)) = true ↔
  BB6.Agent11Mass.SectionReach x y := by
  rw [hasHit_iff,BB6.Agent11Mass.section_reach_iff_bounded]
  simp only [runFuel_eq]

/-- Entire all-time exclusion for the genuine second-gate m=2 target
    (j=7,m=2), from finite kernel reduction plus the universal rank lemma. -/
theorem no_second_gate_m2 : ¬ BB6.Agent11Mass.SectionReach 17 622 := by
  intro hr
  have h := (hasHitFull_iff 17 622).mpr hr
  have hc : hasHit 17 622 (17+2*622) (some (5,1)) = false := by
    set_option maxRecDepth 4096 in
      decide
  simp [hc] at h

#print axioms runFuel_commute
#print axioms runFuel_succ_head
#print axioms hasHit_iff
#print axioms hasHitFull_iff
#print axioms no_second_gate_m2

#print axioms bounceFuel_correct
#print axioms secNextFuel_eq
#print axioms runFuel_eq
#print axioms reachableFastBool_correct
#print axioms no_second_gate_m0
#print axioms no_second_gate_m1
end BB6.Agent11Fuel
