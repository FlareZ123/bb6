import FastAffineNormalize
import Lean.Elab.Tactic.Omega

namespace BB6.Agent27FastBool

/-- Original affine-normalizer last gate, evaluated through a proved
    source-equivalent structurally recursive implementation. -/
def fastNormalizerDecidable (j m : Nat) :
    Decidable ((BB6.Agent15.affineNormalize (2*j+3)
      (2^(2*m+2)*(j+3)-(j+3*m+5))).2 ≠ 4) :=
  let a := 2*j+3
  let k := 2^(2*m+2)*(j+3)-(j+3*m+5)
  if h : (BB6.Agent27FastNorm.fastNormalize a k).2 ≠ 4 then
    isTrue (by simpa only [BB6.Agent27FastNorm.fastNormalize_eq] using h)
  else
    isFalse (fun hp =>
      h (by simpa only [BB6.Agent27FastNorm.fastNormalize_eq] using hp))

/-- Hierarchical constructor of the full *source* predicate decision;
    no original sieve definition is changed or assumed. -/
def fastPriorHighDecidable (j m : Nat) :
    Decidable (BB6.Agent11C58AllDepth.highAllowed j m) :=
  letI : Decidable (∀ n : Nat, ¬(n+4≤2*m+2 ∧
      (j+3*m+3)%2^(n+4)=2^(n+2) ∧
      (2*j+3)%8=(if n%2=0 then 7 else 3))) :=
        BB6.Agent27FullBool.olderAllowedDecidable j m
  letI : Decidable (∀ r : Nat, ¬(2≤r ∧ 3≤m ∧ r+4≤2*m+2 ∧
      m%4=(2*r+3)%4 ∧
      (j+9*m+14)%2^(r+4)=3*2^(r+2))) :=
        BB6.Agent27FullBool.olderC58AllowedDecidable j m
  letI : Decidable ((BB6.Agent15.affineNormalize (2*j+3)
      (2^(2*m+2)*(j+3)-(j+3*m+5))).2 ≠ 4) :=
        fastNormalizerDecidable j m
  letI : Decidable (BB6.Agent3.jointHighAllowed j m) := by
    unfold BB6.Agent3.jointHighAllowed
    infer_instance
  letI : Decidable (BB6.Agent3.jointHighRectAllowed j m) := by
    unfold BB6.Agent3.jointHighRectAllowed
    infer_instance
  letI : Decidable (BB6.Agent19Joint.highAllowed j m) := by
    unfold BB6.Agent19Joint.highAllowed
    infer_instance
  letI : Decidable (BB6.Agent29Joint.highAllowedPlus j m) := by
    unfold BB6.Agent29Joint.highAllowedPlus
    infer_instance
  letI : Decidable (BB6.Agent3ValSix.highAllowedValSix j m) := by
    unfold BB6.Agent3ValSix.highAllowedValSix
    infer_instance
  letI : Decidable (BB6.Agent3ValSix.highAllowedValSixThree j m) := by
    unfold BB6.Agent3ValSix.highAllowedValSixThree
    infer_instance
  letI : Decidable (BB6.Agent11Joint.highAllowed j m) := by
    unfold BB6.Agent11Joint.highAllowed
    infer_instance
  letI : Decidable (BB6.Agent19Five.highAllowed j m) := by
    unfold BB6.Agent19Five.highAllowed
    infer_instance
  letI : Decidable (BB6.Agent3ValSix.highAllowedValSixFull j m) := by
    unfold BB6.Agent3ValSix.highAllowedValSixFull
    infer_instance
  letI : Decidable (BB6.Agent11C58ValSix.highAllowed j m) := by
    unfold BB6.Agent11C58ValSix.highAllowed
    infer_instance
  letI : Decidable (BB6.Agent11C58AllDepth.highAllowed j m) := by
    unfold BB6.Agent11C58AllDepth.highAllowed
    infer_instance
  inferInstance

/-- Every source-conjunct of the pre-phase high sieve, executable at
    practical large stopping targets without unfolding the source
    normalizer's well-founded recursor. -/
def fastPriorHighAllowedBool (j m : Nat) : Bool :=
  letI : Decidable (BB6.Agent11C58AllDepth.highAllowed j m) :=
    fastPriorHighDecidable j m
  decide (BB6.Agent11C58AllDepth.highAllowed j m)

theorem fastPriorHighAllowedBool_iff (j m : Nat) :
    fastPriorHighAllowedBool j m = true ↔
      BB6.Agent11C58AllDepth.highAllowed j m := by
  simp only [fastPriorHighAllowedBool, decide_eq_true_eq]

/-- Executable strongest C high parameter filter including the exact
    all-phase exclusion and all earlier original-source restrictions. -/
def fastHighAllowedFullBool (j m : Nat) : Bool :=
  letI : Decidable (BB6.Agent11C58AllDepth.highAllowed j m) :=
    fastPriorHighDecidable j m
  letI : Decidable (BB6.Agent46.allPhaseExcluded j m) :=
    BB6.Agent27FullBool.phaseExcludedDecidable j m
  letI : Decidable (BB6.Agent24Phase.highAllowed j m) := by
    unfold BB6.Agent24Phase.highAllowed
    infer_instance
  decide (BB6.Agent24Phase.highAllowed j m)

theorem fastHighAllowedFullBool_iff (j m : Nat) :
    fastHighAllowedFullBool j m = true ↔
      BB6.Agent24Phase.highAllowed j m := by
  simp only [fastHighAllowedFullBool, decide_eq_true_eq]

/-- Exact original-blank Machine C stopping equivalence with a
    computationally practical complete high-parameter Boolean guard. -/
theorem blank_halts_iff_fast_full_booleans :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent27FullBool.lowAllowedFullBool m = true ∧
         BB6.Agent3ValSix.valSixMixedRootDecision 1
           (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, fastHighAllowedFullBool j m = true ∧
         BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
           (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent24Phase.blank_halts_iff_c58_two_sided_all_phase]
  constructor
  · rintro (⟨m,hallow,hroot⟩ | ⟨j,m,hallowed,hroot⟩)
    · exact Or.inl ⟨m,(BB6.Agent27FullBool.lowAllowedFullBool_iff m).mpr hallow,hroot⟩
    · exact Or.inr ⟨j,m,(fastHighAllowedFullBool_iff j m).mpr hallowed,hroot⟩
  · rintro (⟨m,hallow,hroot⟩ | ⟨j,m,hallowed,hroot⟩)
    · exact Or.inl ⟨m,(BB6.Agent27FullBool.lowAllowedFullBool_iff m).mp hallow,hroot⟩
    · exact Or.inr ⟨j,m,(fastHighAllowedFullBool_iff j m).mp hallowed,hroot⟩

-- Fully kernel-reduced original predicate examples that previously stuck
-- inside the source affine normalizer's well-founded recursor.
#guard fastPriorHighAllowedBool 2256 15 == true
#guard fastPriorHighAllowedBool 3292 11 == true
#guard fastHighAllowedFullBool 2256 15 == false
#guard fastHighAllowedFullBool 3292 11 == false

#print axioms fastPriorHighAllowedBool_iff
#print axioms fastHighAllowedFullBool_iff
#print axioms blank_halts_iff_fast_full_booleans
end BB6.Agent27FastBool
