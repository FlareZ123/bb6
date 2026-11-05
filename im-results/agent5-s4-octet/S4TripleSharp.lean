import S4TripleResidue
import Lean.Elab.Tactic.Omega

namespace S4TripleSharp
open S4Power S4Octet S4Toggle S4TripleHead S4TripleResidue
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem witness_3 : P [282,968,3657,1668]=none := by simp [P,G,H]
theorem witness_6 : P [283,908,2493,317]=none := by simp [P,G,H]
theorem witness_7 : P [282,965,1729,2030]=none := by simp [P,G,H]
theorem witness_10 : P [283,906,984,48]=none := by simp [P,G,H]
theorem witness_11 : P [282,964,974,963]=none := by simp [P,G,H]
theorem witness_12 : P [280,396,742,937]=none := by simp [P,G,H]
theorem witness_15 : P [282,967,2129,641]=none := by simp [P,G,H]
theorem witness_23 : P [282,965,1732,840]=none := by simp [P,G,H]
theorem witness_25 : P [281,512,1339,40]=none := by simp [P,G,H]
theorem witness_26 : P [283,906,982,49]=none := by simp [P,G,H]
theorem witness_28 : P [280,396,743,453]=none := by simp [P,G,H]
theorem witness_31 : P [282,967,2128,1531]=none := by simp [P,G,H]

def SafePhase (i : Nat) : Prop :=
  i=0 ∨ i=1 ∨ i=2 ∨ i=4 ∨ i=5 ∨ i=8 ∨ i=9 ∨ i=13 ∨ i=14 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=24 ∨ i=27 ∨ i=29 ∨ i=30

theorem exact_triple_safety_below32 (i : Nat) (hi : i<32) :
    (∀ T : List Nat, P ((tripleRun i).1::(tripleRun i).2.1::(tripleRun i).2.2::T) ≠ none) ↔
    SafePhase i := by
  rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=16 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=27 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 by omega) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (280::397::1158::T) ≠ none
      apply P_safe_if_residues 280 397 1158 T
      · decide
      · decide
      · decide
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (281::513::2065::T) ≠ none
      apply P_safe_if_residues 281 513 2065 T
      · decide
      · decide
      · decide
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (283::909::2691::T) ≠ none
      apply P_safe_if_residues 283 909 2691 T
      · decide
      · decide
      · decide
  · subst i
    constructor
    · intro hall
      have hne := hall [1668]
      change P [282,968,3657,1668] ≠ none at hne
      exact False.elim (hne witness_3)
    · intro hs
      simp [SafePhase] at hs
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (280::399::2823::T) ≠ none
      apply P_safe_if_residues 280 399 2823 T
      · decide
      · decide
      · decide
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (281::511::1868::T) ≠ none
      apply P_safe_if_residues 281 511 1868 T
      · decide
      · decide
      · decide
  · subst i
    constructor
    · intro hall
      have hne := hall [317]
      change P [283,908,2493,317] ≠ none at hne
      exact False.elim (hne witness_6)
    · intro hs
      simp [SafePhase] at hs
  · subst i
    constructor
    · intro hall
      have hne := hall [2030]
      change P [282,965,1729,2030] ≠ none at hne
      exact False.elim (hne witness_7)
    · intro hs
      simp [SafePhase] at hs
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (280::398::1255::T) ≠ none
      apply P_safe_if_residues 280 398 1255 T
      · decide
      · decide
      · decide
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (281::512::1338::T) ≠ none
      apply P_safe_if_residues 281 512 1338 T
      · decide
      · decide
      · decide
  · subst i
    constructor
    · intro hall
      have hne := hall [48]
      change P [283,906,984,48] ≠ none at hne
      exact False.elim (hne witness_10)
    · intro hs
      simp [SafePhase] at hs
  · subst i
    constructor
    · intro hall
      have hne := hall [963]
      change P [282,964,974,963] ≠ none at hne
      exact False.elim (hne witness_11)
    · intro hs
      simp [SafePhase] at hs
  · subst i
    constructor
    · intro hall
      have hne := hall [937]
      change P [280,396,742,937] ≠ none at hne
      exact False.elim (hne witness_12)
    · intro hs
      simp [SafePhase] at hs
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (281::509::540::T) ≠ none
      apply P_safe_if_residues 281 509 540 T
      · decide
      · decide
      · decide
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (283::907::1164::T) ≠ none
      apply P_safe_if_residues 283 907 1164 T
      · decide
      · decide
      · decide
  · subst i
    constructor
    · intro hall
      have hne := hall [641]
      change P [282,967,2129,641] ≠ none at hne
      exact False.elim (hne witness_15)
    · intro hs
      simp [SafePhase] at hs
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (280::397::1157::T) ≠ none
      apply P_safe_if_residues 280 397 1157 T
      · decide
      · decide
      · decide
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (281::513::2064::T) ≠ none
      apply P_safe_if_residues 281 513 2064 T
      · decide
      · decide
      · decide
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (283::909::2690::T) ≠ none
      apply P_safe_if_residues 283 909 2690 T
      · decide
      · decide
      · decide
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (282::968::3656::T) ≠ none
      apply P_safe_if_residues 282 968 3656 T
      · decide
      · decide
      · decide
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (280::399::2825::T) ≠ none
      apply P_safe_if_residues 280 399 2825 T
      · decide
      · decide
      · decide
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (281::511::1869::T) ≠ none
      apply P_safe_if_residues 281 511 1869 T
      · decide
      · decide
      · decide
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (283::908::2494::T) ≠ none
      apply P_safe_if_residues 283 908 2494 T
      · decide
      · decide
      · decide
  · subst i
    constructor
    · intro hall
      have hne := hall [840]
      change P [282,965,1732,840] ≠ none at hne
      exact False.elim (hne witness_23)
    · intro hs
      simp [SafePhase] at hs
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (280::398::1257::T) ≠ none
      apply P_safe_if_residues 280 398 1257 T
      · decide
      · decide
      · decide
  · subst i
    constructor
    · intro hall
      have hne := hall [40]
      change P [281,512,1339,40] ≠ none at hne
      exact False.elim (hne witness_25)
    · intro hs
      simp [SafePhase] at hs
  · subst i
    constructor
    · intro hall
      have hne := hall [49]
      change P [283,906,982,49] ≠ none at hne
      exact False.elim (hne witness_26)
    · intro hs
      simp [SafePhase] at hs
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (282::964::973::T) ≠ none
      apply P_safe_if_residues 282 964 973 T
      · decide
      · decide
      · decide
  · subst i
    constructor
    · intro hall
      have hne := hall [453]
      change P [280,396,743,453] ≠ none at hne
      exact False.elim (hne witness_28)
    · intro hs
      simp [SafePhase] at hs
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (281::509::539::T) ≠ none
      apply P_safe_if_residues 281 509 539 T
      · decide
      · decide
      · decide
  · subst i
    constructor
    · intro _
      simp [SafePhase]
    · intro _ T
      change P (283::907::1163::T) ≠ none
      apply P_safe_if_residues 283 907 1163 T
      · decide
      · decide
      · decide
  · subst i
    constructor
    · intro hall
      have hne := hall [1531]
      change P [282,967,2128,1531] ≠ none at hne
      exact False.elim (hne witness_31)
    · intro hs
      simp [SafePhase] at hs

theorem exact_triple_safety (n : Nat) :
    (∀ T : List Nat,
      P ((tripleRun n).1::(tripleRun n).2.1::(tripleRun n).2.2::T) ≠ none) ↔
      SafePhase (n%32) := by
  rw [tripleRun_mod32]
  exact exact_triple_safety_below32 _ (Nat.mod_lt n (by omega))

#print axioms exact_triple_safety_below32
#print axioms exact_triple_safety
#print axioms witness_3
#print axioms witness_31
end S4TripleSharp
