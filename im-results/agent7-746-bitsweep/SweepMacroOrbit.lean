import SweepStageAlgorithm

namespace CascadeFastReturn
open CascadeBitSweep

/-- Original source-reset runs concatenate exactly even across Option failure. -/
theorem runBit_add (h a b : Nat) :
    runBit h (a+b)=(runBit h a).bind (fun u => runBit u b) := by
  induction b with
  | zero =>
      simp [runBit]
  | succ b ih =>
      rw [Nat.add_succ]
      change (runBit h (a+b)).bind bitOutcome =
          (runBit h a).bind (fun u => (runBit u b).bind bitOutcome)
      rw [ih]
      cases hv : runBit h a with
      | none => simp
      | some v => simp

/-- Original source reset count and resulting height after n complete
    dyadic-level events. A halt remains terminal. -/
def macroOrbit (start : Nat) : Nat → Nat × Option Nat
  | 0 => (0,some start)
  | n+1 =>
      let prev := macroOrbit start n
      match prev.2 with
      | none => prev
      | some h =>
          let next := levelMacro h
          (prev.1+next.1,next.2)

/-- Every finite prefix of the compressed deterministic level orbit is
    source-exact, including the exact count of original source steps. -/
theorem macroOrbit_sound (start n : Nat) :
    runBit start (macroOrbit start n).1=(macroOrbit start n).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      let prev := macroOrbit start n
      change runBit start
          (match prev.2 with
            | none => prev
            | some h => (prev.1+(levelMacro h).1,(levelMacro h).2)).1 =
          (match prev.2 with
            | none => prev
            | some h => (prev.1+(levelMacro h).1,(levelMacro h).2)).2
      cases hp : prev.2 with
      | none =>
          simpa only using ih
      | some h =>
          change runBit start (prev.1+(levelMacro h).1)=(levelMacro h).2
          rw [runBit_add]
          have hi : runBit start prev.1=some h := by simpa [prev,hp] using ih
          rw [hi]
          exact levelMacro_sound h

/-- The source sweep index grows by at least one per successful macro event,
    regardless of how many original first resets each event compresses. -/
theorem macroOrbit_level_bound (start n u : Nat)
    (hu : (macroOrbit start n).2=some u) :
    firstFailIndex start+n≤firstFailIndex u := by
  induction n generalizing u with
  | zero =>
      simp [macroOrbit] at hu
      have he : start=u := hu
      subst u
      omega
  | succ n ih =>
      let prev := macroOrbit start n
      change (match prev.2 with
        | none => prev
        | some h => (prev.1+(levelMacro h).1,(levelMacro h).2)).2=some u at hu
      cases hp : prev.2 with
      | none =>
          simp only [hp] at hu
          cases hu
      | some h =>
          simp only [hp] at hu
          have hbound := ih h hp
          have hnext := levelMacro_advances h u hu
          omega

#print axioms runBit_add
#print axioms macroOrbit_sound
#print axioms macroOrbit_level_bound
end CascadeFastReturn
