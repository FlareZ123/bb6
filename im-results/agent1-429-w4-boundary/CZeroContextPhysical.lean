import CZeroContext
import BB429DeltaPhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000

namespace BB429CZeroContextPhysical
open BB6Coverage BB429OddExcursion BB429CZeroEvenReturn BB429CZeroContext
open BB429PhysicalBridge BB429PhysicalFrontier BB429DeltaPhysicalBridge BB429SourceE1Delta

private theorem physical_run_add (m n : Nat) (c : Config) :
    BB6Coverage.run BB429PhysicalFrontier.target429 (m+n) c =
      (BB6Coverage.run BB429PhysicalFrontier.target429 m c).bind
        (BB6Coverage.run BB429PhysicalFrontier.target429 n) := by
  induction n with
  | zero =>
      simp only [Nat.add_zero]
      change (BB6Coverage.run BB429PhysicalFrontier.target429 m c) =
        (BB6Coverage.run BB429PhysicalFrontier.target429 m c).bind (fun d => some d)
      cases BB6Coverage.run BB429PhysicalFrontier.target429 m c <;> rfl
  | succ n ih =>
      rw [Nat.add_succ]
      change ((BB6Coverage.run BB429PhysicalFrontier.target429 (m+n) c).bind
        (rawStep BB429PhysicalFrontier.target429)) =
        (BB6Coverage.run BB429PhysicalFrontier.target429 m c).bind
          (fun d => (BB6Coverage.run BB429PhysicalFrontier.target429 n d).bind
            (rawStep BB429PhysicalFrontier.target429))
      rw [ih]
      rw [Option.bind_assoc]

/-- Entire-tape physical lift of the even-block C/0 first-return rule. -/
theorem physical_even_C0_context (k : Nat) (tail : List Bool) (c : Config)
    (hrep : Represents (z 2 (ones (2*k+2) ++ (false::tail)) false []) c) :
    ∃ c', BB6Coverage.run BB429PhysicalFrontier.target429 (4*k+11) c = some c' ∧
       Represents (z 2 (true::false::(ones (2*k+4) ++ tail)) false []) c' :=
  source_run_rep (4*k+11) _ c hrep _ (even_C0_context k tail)

/-- A three-zero delimiter after an odd block forces actual raw halting
    from any physically represented original-machine configuration. -/
theorem physical_odd_C0_context_halts (k : Nat) (tail : List Bool) (c : Config)
    (hrep : Represents (z 2 (ones (2*k+3) ++ (false::false::false::tail)) false []) c) :
    BB6Coverage.run BB429PhysicalFrontier.target429 (4*k+22) c = none := by
  obtain ⟨l, hz⟩ := odd_C0_context_fatal k tail
  obtain ⟨c', hc', hrep'⟩ := source_run_rep (4*k+20) _ c hrep _ hz
  have h2 : runWithDelta 2 (z 2 l false [true]) = none := by rfl
  have hc2 := source_runWithDelta_none_rep 2 (z 2 l false [true]) c' hrep' h2
  rw [show 4*k+22 = (4*k+20)+2 by omega, physical_run_add, hc']
  simpa using hc2

/-- Direct authentic blank-root consequence; no claim of actual reachability. -/
theorem blank_reaches_odd_C0_context_halts (n k : Nat) (tail : List Bool) (c : Config)
    (hroot : BB6Coverage.run BB429PhysicalFrontier.target429 n BB6Coverage.blank = some c)
    (hrep : Represents (z 2 (ones (2*k+3) ++ (false::false::false::tail)) false []) c) :
    BB6Coverage.run BB429PhysicalFrontier.target429 (n+4*k+22) BB6Coverage.blank = none := by
  rw [show n+4*k+22 = n+(4*k+22) by omega,physical_run_add,hroot]
  simpa using physical_odd_C0_context_halts k tail c hrep

#print axioms physical_even_C0_context
#print axioms physical_odd_C0_context_halts
#print axioms blank_reaches_odd_C0_context_halts
end BB429CZeroContextPhysical
