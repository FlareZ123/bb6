import Bound10000
import OriginalRawGate
import ResetChain

namespace CascadeResetShield

/-- Definitional equality pins the locally checked arithmetic grammar to
    the exact source ResetParent theorem, without a new semantic assumption. -/
theorem edge_iff_source (h u : Nat) :
    Edge h u ↔ CascadeResetInverse.ResetParent h u := Iff.rfl

theorem source_chain_to_path {s u : Nat}
    (hr : CascadeResetInverse.ResetChain s u) : Path Edge s u := by
  induction hr with
  | root => exact Path.refl _
  | append hr he ih =>
    exact path_trans ih (Path.step ((edge_iff_source _ _).mpr he) (Path.refl _))

theorem source_no_fatal_through_10000 (n : Nat) (hn : n≤10000) :
    ¬ CascadeSweep.ReachC (2,0) (4*2^n-n-4,0) := by
  intro hr
  exact no_fatal_through_10000 n hn
    (source_chain_to_path ((CascadeResetInverse.root_reset_chain_iff _).mp hr))

end CascadeResetShield

namespace Agent10Raw746
open BusyBeaver
open BusyBeaver.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA
open CascadeSweep

theorem original_machine_halts_iff_surviving_10001 :
    IsHalt target ↔ ∃ n, 10001≤n ∧ (n%6=4 ∨ n%6=5) ∧
      ReachC (2,0) (4*2^n-n-4,0) := by
  rw [original_machine_halts_iff_surviving_257]
  constructor
  · rintro ⟨n,_,hres,hr⟩
    by_cases hn : 10001≤n
    · exact ⟨n,hn,hres,hr⟩
    · exact False.elim (CascadeResetShield.source_no_fatal_through_10000 n (by omega) hr)
  · rintro ⟨n,hn,hres,hr⟩
    exact ⟨n,by omega,hres,hr⟩

#print axioms CascadeResetShield.edge_iff_source
#print axioms CascadeResetShield.source_no_fatal_through_10000
#print axioms original_machine_halts_iff_surviving_10001
end Agent10Raw746
