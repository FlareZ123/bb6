import CostRecurrence
import Lean.Elab.Tactic.Omega

namespace BB6ChampionArithmetic

/-- Generic deterministic partial transition semantics, matching the shape of
    the repository's original run, without replacing its source definitions. -/
def fuelRun {α : Type} (step : α → Option α) : Nat → α → Option α
  | 0, c => some c
  | n+1, c => (fuelRun step n c).bind step

theorem fuelRun_append {α : Type} (step : α → Option α)
    (a b : Nat) (c : α) :
    fuelRun step (a+b) c = (fuelRun step a c).bind (fuelRun step b) := by
  induction b with
  | zero => simp [fuelRun]
  | succ b ih =>
    calc
      fuelRun step (a+(b+1)) c = (fuelRun step (a+b) c).bind step := by rw [Nat.add_succ]; rfl
      _ = ((fuelRun step a c).bind (fuelRun step b)).bind step := by rw [ih]
      _ = (fuelRun step a c).bind (fuelRun step (b+1)) := by
        cases h : fuelRun step a c with
        | none => simp
        | some d => simp [fuelRun]

theorem nextMarker_normalized (m : Nat) : (nextMarker m)%3=nextMarker m := by
  unfold nextMarker
  omega

/-- Conditional consumption theorem. Its premise is the MISSING exact
    original-machine counted Rst0/1/2 macro statement, and must be proved
    separately for the genuine TM63 machine before applying this theorem. -/
theorem section_fuel_sound {α : Type} (step : α → Option α)
    (encode : Nat → Nat → Nat → Nat → α)
    (hmacro : ∀ n m a b : Nat, 0<n →
      fuelRun step (proposedIncrementCost (m%3) n a b) (encode n (m%3) a b) =
      some (encode (n-1) (nextMarker m)
        (nextExponent m a b) (nextRight b)))
    (n m a b : Nat) :
    fuelRun step (sectionResult n m a b).cost (encode n (m%3) a b) =
      some (encode 0 (sectionResult n m a b).marker
        (sectionResult n m a b).exponent (sectionResult n m a b).right) := by
  induction n generalizing m a b with
  | zero => simp [sectionResult, fuelRun]
  | succ n ih =>
    simp only [sectionResult]
    rw [fuelRun_append]
    rw [hmacro (n+1) m a b (by omega)]
    simp
    have hm : (nextMarker m)%3 = nextMarker m := nextMarker_normalized m
    simpa only [hm] using ih (nextMarker m) (nextExponent m a b) (nextRight b)

#print axioms section_fuel_sound

end BB6ChampionArithmetic
