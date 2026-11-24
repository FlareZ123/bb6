import HighWordCertificate
import ResetBlockCore
import ResetChain

namespace CascadePeriodic

theorem grammar_iff_edge (h u : Nat) :
    Grammar h u ↔ CascadeResetShield.Edge h u := Iff.rfl

theorem grammar_iff_parent (h u : Nat) :
    Grammar h u ↔ CascadeResetInverse.ResetParent h u := Iff.rfl

theorem ResetPath.toShield {n h u : Nat} (p : ResetPath n h u) :
    CascadeResetShield.Path CascadeResetShield.Edge h u := by
  induction p with
  | nil h => exact .refl h
  | cons he hp ih => exact .step ((grammar_iff_edge _ _).mp he) ih

theorem ResetPath.toSource {n h u : Nat} (p : ResetPath n h u) :
    CascadeResetInverse.ResetChain h u := by
  induction p with
  | nil h => exact .root h
  | @cons n h v u he hp ih =>
    -- ResetChain extends at the right; use its transitivity or the helper below.
    have hs : CascadeResetInverse.ResetChain h v :=
      .append (.root h) ((grammar_iff_parent _ _).mp he)
    induction ih with
    | root => exact hs
    | append hr he' ih' => exact .append ih' he'

theorem highBlock_fatal_exclusion (c : HighCert) (n z N : Nat)
    (hc : checkHighBlock 2 0 c=some (n,z))
    (hz : CascadeResetShield.fatal N<z)
    (j : Nat) (hj : j≤N) :
    ¬ CascadeResetShield.Path CascadeResetShield.Edge 2
        (CascadeResetShield.fatal j) :=
  CascadeResetShield.bounded_fatal_exclusion
    CascadeResetShield.edge_deterministic CascadeResetShield.edge_strict
    (fun _ _ e => e) N z (checkHighBlock_sound _ _ _ _ _ hc).toShield hz j hj

#print axioms highBlock_fatal_exclusion
#print axioms ResetPath.toSource
end CascadePeriodic
