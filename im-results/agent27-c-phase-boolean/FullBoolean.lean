import StrongPhaseBool
import Lean.Elab.Tactic.Omega

namespace BB6.Agent27FullBool

/-- Exact original Agent19 odd-dyadic high stopping predicate. -/
def olderGate (n j m : Nat) : Prop :=
  n+4≤2*m+2 ∧
  (j+3*m+3)%2^(n+4)=2^(n+2) ∧
  (2*j+3)%8=(if n%2=0 then 7 else 3)

instance (n j m : Nat) : Decidable (olderGate n j m) := by
  unfold olderGate
  infer_instance

/-- The original all-depth condition has a bounded candidate range. -/
def olderAllowedBool (j m : Nat) : Bool :=
  (List.range (2*m+1)).all (fun n => decide (¬olderGate n j m))

theorem olderAllowedBool_iff (j m : Nat) :
    olderAllowedBool j m = true ↔ ∀ n, ¬ olderGate n j m := by
  simp only [olderAllowedBool, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h n hg
    have hn : n < 2*m+1 := by
      dsimp [olderGate] at hg
      omega
    exact h n hn hg
  · intro h n _
    exact h n

/-- Constructive decidability of Agent19's original unbounded depth. -/
def olderAllowedDecidable (j m : Nat) : Decidable (∀ n, ¬olderGate n j m) :=
  if h : olderAllowedBool j m = true then
    isTrue ((olderAllowedBool_iff j m).mp h)
  else
    isFalse (fun hp => h ((olderAllowedBool_iff j m).mpr hp))

/-- Decidability of the earlier Agent11 all-depth predicate. -/
def olderC58AllowedDecidable (j m : Nat) :
    Decidable (∀ r, ¬BB6.Agent11GateDecision.gate r j m) :=
  if h : BB6.Agent11GateDecision.allowedBool j m = true then
    isTrue ((BB6.Agent11GateDecision.allowedBool_iff j m).mp h)
  else
    isFalse (fun hp => h ((BB6.Agent11GateDecision.allowedBool_iff j m).mpr hp))

/-- Decidability of the new all-phase exceptions. -/
def phaseExcludedDecidable (j m : Nat) :
    Decidable (BB6.Agent46.allPhaseExcluded j m) :=
  if h : BB6.Agent27Phase.phaseExcludedFastBool j m = true then
    isTrue ((BB6.Agent27Phase.phaseExcludedFastBool_iff j m).mp h)
  else
    isFalse (fun hp => h ((BB6.Agent27Phase.phaseExcludedFastBool_iff j m).mpr hp))

/-- The original high sieve is decidable by composing all its named
    historical stages. Local instances keep typeclass inference bounded
    and leave each source definition unchanged. -/
def priorHighDecidable (j m : Nat) :
    Decidable (BB6.Agent11C58AllDepth.highAllowed j m) :=
  letI : Decidable (∀ n : Nat, ¬(n+4≤2*m+2 ∧
      (j+3*m+3)%2^(n+4)=2^(n+2) ∧
      (2*j+3)%8=(if n%2=0 then 7 else 3))) := olderAllowedDecidable j m
  letI : Decidable (∀ r : Nat, ¬(2≤r ∧ 3≤m ∧ r+4≤2*m+2 ∧
      m%4=(2*r+3)%4 ∧
      (j+9*m+14)%2^(r+4)=3*2^(r+2))) := olderC58AllowedDecidable j m
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

/-- Completely computable high parameter filter. -/
def highAllowedFullBool (j m : Nat) : Bool :=
  letI : Decidable (BB6.Agent11C58AllDepth.highAllowed j m) := priorHighDecidable j m
  letI : Decidable (BB6.Agent46.allPhaseExcluded j m) := phaseExcludedDecidable j m
  letI : Decidable (BB6.Agent24Phase.highAllowed j m) := by
    unfold BB6.Agent24Phase.highAllowed
    infer_instance
  decide (BB6.Agent24Phase.highAllowed j m)

theorem highAllowedFullBool_iff (j m : Nat) :
    highAllowedFullBool j m = true ↔ BB6.Agent24Phase.highAllowed j m := by
  simp only [highAllowedFullBool, decide_eq_true_eq]

/-- Source-authentic prior high sieve, before the latest phase gate. -/
def priorHighAllowedBool (j m : Nat) : Bool :=
  letI : Decidable (BB6.Agent11C58AllDepth.highAllowed j m) := priorHighDecidable j m
  decide (BB6.Agent11C58AllDepth.highAllowed j m)

theorem priorHighAllowedBool_iff (j m : Nat) :
    priorHighAllowedBool j m = true ↔
      BB6.Agent11C58AllDepth.highAllowed j m := by
  simp only [priorHighAllowedBool, decide_eq_true_eq]

/-- The new two-sided phase gate excludes an explicit high target that
    survived every previous integrated source-authentic parameter guard.
    This does not decide whether that target is blank-reachable. -/
theorem phase_strict_example :
    BB6.Agent11C58AllDepth.highAllowed 2256 15 ∧
    ¬ BB6.Agent24Phase.highAllowed 2256 15 := by
  constructor
  · exact (priorHighAllowedBool_iff 2256 15).mp (by decide)
  · intro h
    exact h.2 ((BB6.Agent27Phase.phaseExcludedFastBool_iff 2256 15).mp (by decide))

/-- The source low-family predicate has only finite arithmetic guards. -/
def lowAllowedFullBool (m : Nat) : Bool :=
  letI : Decidable (BB6.Agent11C58ValSix.lowAllowed m) := by
    unfold BB6.Agent11C58ValSix.lowAllowed
      BB6.Agent3ValSix.lowAllowedValSixFull
      BB6.Agent11Joint.lowAllowed
      BB6.Agent3.jointLowAllowed
    infer_instance
  decide (BB6.Agent11C58ValSix.lowAllowed m)

theorem lowAllowedFullBool_iff (m : Nat) :
    lowAllowedFullBool m = true ↔ BB6.Agent11C58ValSix.lowAllowed m := by
  simp only [lowAllowedFullBool, decide_eq_true_eq]

/-- Exact, completely executable per-parameter criterion for the
    genuine Machine C blank-start stopping problem. Both existential
    parameter domains remain unbounded, so the machine is undecided. -/
theorem blank_halts_iff_full_booleans :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, lowAllowedFullBool m = true ∧
         BB6.Agent3ValSix.valSixMixedRootDecision 1
           (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedFullBool j m = true ∧
         BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
           (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent24Phase.blank_halts_iff_c58_two_sided_all_phase]
  constructor
  · rintro (⟨m,hallow,hroot⟩ | ⟨j,m,hallowed,hroot⟩)
    · exact Or.inl ⟨m,(lowAllowedFullBool_iff m).mpr hallow,hroot⟩
    · exact Or.inr ⟨j,m,(highAllowedFullBool_iff j m).mpr hallowed,hroot⟩
  · rintro (⟨m,hallow,hroot⟩ | ⟨j,m,hallowed,hroot⟩)
    · exact Or.inl ⟨m,(lowAllowedFullBool_iff m).mp hallow,hroot⟩
    · exact Or.inr ⟨j,m,(highAllowedFullBool_iff j m).mp hallowed,hroot⟩

#print axioms priorHighAllowedBool_iff
#print axioms phase_strict_example
#print axioms olderAllowedBool_iff
#print axioms highAllowedFullBool_iff
#print axioms lowAllowedFullBool_iff
#print axioms blank_halts_iff_full_booleans
end BB6.Agent27FullBool
