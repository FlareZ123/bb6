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

theorem sourceChain_trans {h v u : Nat}
    (p : CascadeResetInverse.ResetChain h v)
    (q : CascadeResetInverse.ResetChain v u) :
    CascadeResetInverse.ResetChain h u := by
  induction q with
  | root => exact p
  | append hr he ih => exact .append ih he

theorem ResetPath.toSource {n h u : Nat} (p : ResetPath n h u) :
    CascadeResetInverse.ResetChain h u := by
  induction p with
  | nil => exact .root
  | cons he hp ih =>
    exact sourceChain_trans (.append .root ((grammar_iff_parent _ _).mp he)) ih

theorem sourceChain_toShield {h u : Nat}
    (p : CascadeResetInverse.ResetChain h u) :
    CascadeResetShield.Path CascadeResetShield.Edge h u := by
  induction p with
  | root => exact .refl _
  | append hr he ih =>
    exact CascadeResetShield.path_trans ih
      (.step ((grammar_iff_edge _ _).mp ((grammar_iff_parent _ _).mpr he)) (.refl _))

theorem highBlock_fatal_exclusion (c : HighCert) (n z N : Nat)
    (hc : checkHighBlock 2 0 c=some (n,z))
    (hz : CascadeResetShield.fatal N<z)
    (j : Nat) (hj : j≤N) :
    ¬ CascadeResetShield.Path CascadeResetShield.Edge 2
        (CascadeResetShield.fatal j) :=
  CascadeResetShield.bounded_fatal_exclusion
    CascadeResetShield.edge_deterministic CascadeResetShield.edge_strict
    (fun _ _ e => e) N z (checkHighBlock_sound _ _ _ _ _ hc).toShield hz j hj

theorem highBlock_source_fatal_exclusion (c : HighCert) (n z N : Nat)
    (hc : checkHighBlock 2 0 c=some (n,z))
    (hz : CascadeResetShield.fatal N<z)
    (j : Nat) (hj : j≤N) :
    ¬ CascadeSweep.ReachC (2,0) (4*2^j-j-4,0) := by
  intro hr
  exact highBlock_fatal_exclusion c n z N hc hz j hj
    (sourceChain_toShield ((CascadeResetInverse.root_reset_chain_iff _).mp hr))

#print axioms highBlock_fatal_exclusion
#print axioms highBlock_source_fatal_exclusion
#print axioms ResetPath.toSource
end CascadePeriodic
