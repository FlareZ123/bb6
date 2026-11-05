import FastForward
import ResetParentStrict
set_option maxHeartbeats 0
namespace CascadeFastReturn
open CascadeRank CascadeResetInverse CascadeSweep CascadeManyShield

/-- Exact first-reset transitions strictly increase the reset height. -/
theorem fastOutcome_strict (h u : Nat) (hf : fastOutcome h=some u) : h<u := by
  have hs : nextReset h=some u := (fastOutcome_eq_nextReset h).symm.trans hf
  exact reset_parent_strict h u ((nextReset_iff_parent h u).mp hs)

/-- All future successful resets are at least as high as their starting
    reset height, including a zero-step run. -/
theorem runFast_mono (h steps u : Nat) (hr : runFast h steps=some u) : h≤u := by
  induction steps generalizing u with
  | zero =>
    simp only [runFast] at hr
    have hh := Option.some.inj hr
    omega
  | succ steps ih =>
    cases hs : runFast h steps with
    | none => simp [runFast,hs] at hr
    | some v =>
      have hs' : fastOutcome v=some u := by simpa [runFast,hs] using hr
      have hlo := ih v hs
      have hstep := fastOutcome_strict v u hs'
      omega

/-- A one-edge first-reset step may be moved to the beginning of a
    deterministically iterated forward trace. -/
theorem runFast_shift (h v : Nat) (he : fastOutcome h=some v) :
    ∀ t, runFast h (t+1) = runFast v t := by
  intro t
  induction t with
  | zero => simpa [runFast] using he
  | succ t ih =>
    change (runFast h (t+1)).bind fastOutcome = (runFast v t).bind fastOutcome
    rw [ih]

/-- A first-reset halt means no successful later reset may be reached. -/
theorem runFast_halted (h : Nat) (he : fastOutcome h=none) :
    ∀ t, runFast h (t+1) = none := by
  intro t
  induction t with
  | zero => simpa [runFast] using he
  | succ t ih =>
    change (runFast h (t+1)).bind fastOutcome = none
    rw [ih]
    rfl

/-- An efficient single-trajectory executable decision for a fixed reset
    target. Stops once its increasing height passes the target. -/
def boundedHitFrom (target : Nat) : Nat → Nat → Bool
  | 0, h => decide (h=target)
  | fuel+1, h =>
    if h=target then true
    else if target<h then false
    else match fastOutcome h with
      | none => false
      | some v => boundedHitFrom target fuel v

/-- The optimized single-trajectory checker is exactly equivalent to the
    existence of a successful visit within the prescribed reset-step budget. -/
theorem boundedHitFrom_iff (target fuel h : Nat) :
    boundedHitFrom target fuel h = true ↔
    ∃ t, t≤fuel ∧ runFast h t=some target := by
  induction fuel generalizing h with
  | zero =>
    constructor
    · intro hr
      have hh : h=target := by simpa [boundedHitFrom] using hr
      exact ⟨0,by omega,by simpa [hh,runFast]⟩
    · rintro ⟨t,ht,hr⟩
      have ht0 : t=0 := by omega
      subst t
      have hh : h=target := by simpa [runFast] using hr
      simpa [boundedHitFrom,hh]
  | succ fuel ih =>
    by_cases heq : h=target
    · constructor
      · intro _
        exact ⟨0,by omega,by simpa [heq,runFast]⟩
      · intro _
        simp [boundedHitFrom,heq]
    · by_cases hgt : target<h
      · constructor
        · intro hf
          simp [boundedHitFrom,heq,hgt] at hf
        · rintro ⟨t,ht,hr⟩
          have hl := runFast_mono h t target hr
          omega
      · cases he : fastOutcome h with
        | none =>
          constructor
          · intro hf
            simp [boundedHitFrom,heq,hgt,he] at hf
          · rintro ⟨t,ht,hr⟩
            cases t with
            | zero =>
              simp only [runFast] at hr
              have hh := Option.some.inj hr
              exact False.elim (heq hh)
            | succ t =>
              have hn := runFast_halted h he t
              rw [hn] at hr
              cases hr
        | some v =>
          have hdef : boundedHitFrom target (fuel+1) h = boundedHitFrom target fuel v := by
            simp [boundedHitFrom,heq,hgt,he]
          rw [hdef]
          constructor
          · intro hf
            obtain ⟨t,ht,hr⟩ := (ih v).mp hf
            exact ⟨t+1,by omega,(runFast_shift h v he t).trans hr⟩
          · rintro ⟨t,ht,hr⟩
            cases t with
            | zero =>
              have hh := Option.some.inj (by simpa [runFast] using hr)
              exact False.elim (heq hh)
            | succ t =>
              apply (ih v).mpr
              refine ⟨t,by omega,?_⟩
              rw [←runFast_shift h v he t]
              exact hr

/-- A decidable Boolean predicate, with a quadratic worst-case fuel bound,
    exactly characterizes genuine source-root fatal-index reachability. -/
def fatalHitBool (n : Nat) : Bool :=
  boundedHitFrom (fatal n) ((n+2)^2) 2

theorem root_fatal_iff_fatalHitBool (n : Nat) (hn : 2≤n) :
    ReachC (2,0) (fatal n,0) ↔ fatalHitBool n=true := by
  rw [root_fatal_iff_bounded_executable_run n hn]
  exact (boundedHitFrom_iff (fatal n) ((n+2)^2) 2).symm

#print axioms boundedHitFrom_iff
#print axioms root_fatal_iff_fatalHitBool
end CascadeFastReturn
