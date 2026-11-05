import S4TogglePair
import Lean.Elab.Tactic.Omega

namespace S4ToggleSafe
open S4Power S4Octet S4Toggle S4TogglePair
set_option maxHeartbeats 0

theorem safe_280397 (T : List Nat) :
    P (280::397::T) = some (281::513::bumpN 907 T) := by
  cases T <;> simp [P,G,H,bumpN]

theorem safe_281513 (T : List Nat) :
    P (281::513::T) = some (283::909::bumpN 626 T) := by
  cases T <;> simp [P,G,H,bumpN]

theorem safe_283909 (T : List Nat) :
    P (283::909::T) = some (282::968::bumpN 966 T) := by
  cases T <;> simp [P,G,H,bumpN]

theorem safe_281511 (T : List Nat) :
    P (281::511::T) = some (283::908::bumpN 625 T) := by
  cases T <;> simp [P,G,H,bumpN]

theorem safe_281509 (T : List Nat) :
    P (281::509::T) = some (283::907::bumpN 624 T) := by
  cases T <;> simp [P,G,H,bumpN]

theorem safe_283907 (T : List Nat) :
    P (283::907::T) = some (282::967::bumpN 965 T) := by
  cases T <;> simp [P,G,H,bumpN]

theorem witness_3 : P [282,968,851] = none := by simp [P,G,H]
theorem witness_4 : P [280,399,114] = none := by simp [P,G,H]
theorem witness_6 : P [283,908,57] = none := by simp [P,G,H]
theorem witness_7 : P [282,965,341] = none := by simp [P,G,H]
theorem witness_8 : P [280,398,114] = none := by simp [P,G,H]
theorem witness_9 : P [281,512,397] = none := by simp [P,G,H]
theorem witness_10 : P [283,906,58] = none := by simp [P,G,H]
theorem witness_11 : P [282,964,854] = none := by simp [P,G,H]
theorem witness_12 : P [280,396,115] = none := by simp [P,G,H]
theorem witness_15 : P [282,967,341] = none := by simp [P,G,H]

def SafePhase (i : Nat) : Prop :=
    i=0 ∨ i=1 ∨ i=2 ∨ i=5 ∨ i=13 ∨ i=14

theorem exact_pair_safety_below16 (i : Nat) (hi : i<16) :
    (∀ T : List Nat, P ((pairRun i).1::(pairRun i).2::T) ≠ none) ↔ SafePhase i := by
  rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 by omega) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (280::397::T) ≠ none
      rw [safe_280397]
      simp
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (281::513::T) ≠ none
      rw [safe_281513]
      simp
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (283::909::T) ≠ none
      rw [safe_283909]
      simp
  · subst i
    constructor
    · intro hall
      have hne : P [282,968,851] ≠ none := by
        simpa [pairRun,step,S4ToggleHead.h] using hall [851]
      exact False.elim (hne witness_3)
    · intro hs
      simp [SafePhase] at hs
  · subst i
    constructor
    · intro hall
      have hne : P [280,399,114] ≠ none := by
        simpa [pairRun,step,S4ToggleHead.h] using hall [114]
      exact False.elim (hne witness_4)
    · intro hs
      simp [SafePhase] at hs
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (281::511::T) ≠ none
      rw [safe_281511]
      simp
  · subst i
    constructor
    · intro hall
      have hne : P [283,908,57] ≠ none := by
        simpa [pairRun,step,S4ToggleHead.h] using hall [57]
      exact False.elim (hne witness_6)
    · intro hs
      simp [SafePhase] at hs
  · subst i
    constructor
    · intro hall
      have hne : P [282,965,341] ≠ none := by
        simpa [pairRun,step,S4ToggleHead.h] using hall [341]
      exact False.elim (hne witness_7)
    · intro hs
      simp [SafePhase] at hs
  · subst i
    constructor
    · intro hall
      have hne : P [280,398,114] ≠ none := by
        simpa [pairRun,step,S4ToggleHead.h] using hall [114]
      exact False.elim (hne witness_8)
    · intro hs
      simp [SafePhase] at hs
  · subst i
    constructor
    · intro hall
      have hne : P [281,512,397] ≠ none := by
        simpa [pairRun,step,S4ToggleHead.h] using hall [397]
      exact False.elim (hne witness_9)
    · intro hs
      simp [SafePhase] at hs
  · subst i
    constructor
    · intro hall
      have hne : P [283,906,58] ≠ none := by
        simpa [pairRun,step,S4ToggleHead.h] using hall [58]
      exact False.elim (hne witness_10)
    · intro hs
      simp [SafePhase] at hs
  · subst i
    constructor
    · intro hall
      have hne : P [282,964,854] ≠ none := by
        simpa [pairRun,step,S4ToggleHead.h] using hall [854]
      exact False.elim (hne witness_11)
    · intro hs
      simp [SafePhase] at hs
  · subst i
    constructor
    · intro hall
      have hne : P [280,396,115] ≠ none := by
        simpa [pairRun,step,S4ToggleHead.h] using hall [115]
      exact False.elim (hne witness_12)
    · intro hs
      simp [SafePhase] at hs
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (281::509::T) ≠ none
      rw [safe_281509]
      simp
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (283::907::T) ≠ none
      rw [safe_283907]
      simp
  · subst i
    constructor
    · intro hall
      have hne : P [282,967,341] ≠ none := by
        simpa [pairRun,step,S4ToggleHead.h] using hall [341]
      exact False.elim (hne witness_15)
    · intro hs
      simp [SafePhase] at hs

theorem exact_pair_safety (n : Nat) :
    (∀ T : List Nat, P ((pairRun n).1::(pairRun n).2::T) ≠ none) ↔
      SafePhase (n%16) := by
  rw [pairRun_mod16]
  exact exact_pair_safety_below16 _ (Nat.mod_lt n (by omega))

#print axioms exact_pair_safety_below16
#print axioms exact_pair_safety
#print axioms safe_280397
#print axioms safe_283907
#print axioms witness_3
#print axioms witness_15
end S4ToggleSafe
