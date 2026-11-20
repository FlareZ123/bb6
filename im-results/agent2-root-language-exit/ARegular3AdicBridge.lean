import DRegularSourceShift
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2ARegular3AdicBridge

open CryptidBoundary BB6.BoundaryPadding

/-- The external A(n,r) section in the repository's physical configuration
    representation: two leading unary bits are implicit in init. -/
def ASection (n : Nat) (r : List Bool) : CryptidBoundary.Cfg :=
  CryptidBoundary.init (List.replicate (n-2) true ++ r)

/-- The regular suffix represented by a DRegular state. -/
def regularSuffix (s : DRegular.L) : List Bool :=
  CryptidBoundary.oppairs s.q ++ List.replicate s.b true

/-- Exact representation identity: DRegular's source section is A(a,r)
    for r=(01)^q 1^b. -/
theorem sourceSection_eq_ASection (s : DRegular.L) :
    DRegularSource.sourceSection s = ASection s.a (regularSuffix s) := by
  rfl

/-- Canonical DRegular sections satisfy the suffix side condition in the
    external A(n,r) notation: r is empty or begins with 0. -/
theorem canonical_suffix_shape (s : DRegular.L)
    (hc : DRegular.Canon s) :
    regularSuffix s = [] ∨ ∃ tail, regularSuffix s = false :: tail := by
  rcases hc with ⟨ha,hcanon⟩
  cases hq : s.q with
  | zero =>
      have hb : s.b = 0 := by
        rcases hcanon with hq' | hb
        · exact False.elim (hq' hq)
        · exact hb
      left
      simp [regularSuffix,hq,hb,CryptidBoundary.oppairs]
  | succ q =>
      right
      refine ⟨true :: (CryptidBoundary.oppairs q ++ List.replicate s.b true), ?_⟩
      simp [regularSuffix,hq,CryptidBoundary.oppairs,List.append_assoc]

/-- Model-level form of the wiki's 3-adic prefix-synchronization observation:
    adding 3^k*p to the unary parameter preserves the first k DRegular
    transitions and adds 8^k*p to the output parameter. -/
theorem synchronized_model (s t : DRegular.L) (k p : Nat)
    (hc : DRegular.Canon s) (hr : DRegular.run k s = some t) :
    DRegular.run k (BB6.DRegularSourceShift.inputLift s k p) =
      some (BB6.DRegularSourceShift.outputLift t k p) :=
  BB6.DRegularSourceShift.lifted_model s t k p hc hr

/-- Original-source version of the same 3-adic synchronization law, expressed
    in A(n,r) notation. For every canonical regular suffix and every p, the
    physical machine follows the same k-step DRegular itinerary from
    A(a+3^k*p,r), ending at A(a'+8^k*p,r'). This proves the wiki's suggested
    shift law on the regular suffix language, not for arbitrary r. -/
theorem synchronized_source (s t : DRegular.L) (k p : Nat)
    (hc : DRegular.Canon s) (hr : DRegular.run k s = some t) :
    BB6.BoundaryPadding.ObsEq
      (CryptidBoundary.run
        (DRegular.accumulated k
          (BB6.DRegularSourceShift.inputLift s k p))
        (ASection (s.a+3^k*p) (regularSuffix s)))
      (ASection (t.a+8^k*p) (regularSuffix t)) := by
  have h := BB6.DRegularSourceShift.lifted_original_run s t k p hc hr
  simpa [ASection,regularSuffix,DRegularSource.sourceSection,
    BB6.DRegularSourceShift.inputLift,BB6.DRegularSourceShift.outputLift,
    BB6.DRegularShift.shiftNat] using h

/-- Base and lifted physical runs are both authenticated, with the same
    suffix updates and the exact 3^k/8^k affine parameter shifts. -/
theorem paired_synchronized_source (s t : DRegular.L) (k p : Nat)
    (hc : DRegular.Canon s) (hr : DRegular.run k s = some t) :
    BB6.BoundaryPadding.ObsEq
      (CryptidBoundary.run (DRegular.accumulated k s)
        (ASection s.a (regularSuffix s)))
      (ASection t.a (regularSuffix t)) ∧
    BB6.BoundaryPadding.ObsEq
      (CryptidBoundary.run
        (DRegular.accumulated k
          (BB6.DRegularSourceShift.inputLift s k p))
        (ASection (s.a+3^k*p) (regularSuffix s)))
      (ASection (t.a+8^k*p) (regularSuffix t)) := by
  have h := BB6.DRegularSourceShift.paired_original_run s t k p hc hr
  constructor
  · simpa [ASection,regularSuffix,DRegularSource.sourceSection] using h.1
  · exact synchronized_source s t k p hc hr

#print axioms synchronized_model
#print axioms synchronized_source
#print axioms paired_synchronized_source

end BB6.Agent2ARegular3AdicBridge
