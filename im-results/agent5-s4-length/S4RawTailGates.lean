import S4RawCompact
import Lean.Elab.Tactic.Omega

namespace S4SourceBridge

private theorem pow2_four (x : Nat) :
    S4Power.Pow2 (4*x) ↔ S4Power.Pow2 x := by
  have hh : 4*x=2*(2*x) := by omega
  rw [hh]
  exact (S4Power.pow2_double (2*x)).trans (S4Power.pow2_double x)

private theorem root_W_eq_power (T : List Nat) :
    _root_.W T = S4Power.W T :=
  ((S4Power.W_eq_source T).trans (S4Length.W_eq_original T)).symm

theorem tail_gate_80 (R : List Nat) :
    (∃ k : Nat, _root_.W (80::150::R)+45=2^k) ↔
    (∃ k : Nat, _root_.W R+107=2^k) := by
  change S4Power.Pow2 (_root_.W (80::150::R)+45) ↔
    S4Power.Pow2 (_root_.W R+107)
  rw [root_W_eq_power, root_W_eq_power]
  have hw : S4Power.W (80::150::R)+45 = 4*(S4Power.W R+107) := by
    simp [S4Power.W]
    omega
  rw [hw, pow2_four]

theorem tail_gate_82 (R : List Nat) :
    (∃ k : Nat, _root_.W (82::231::R)+45=2^k) ↔
    (∃ k : Nat, _root_.W R+148=2^k) := by
  change S4Power.Pow2 (_root_.W (82::231::R)+45) ↔
    S4Power.Pow2 (_root_.W R+148)
  rw [root_W_eq_power, root_W_eq_power]
  have hw : S4Power.W (82::231::R)+45 = 4*(S4Power.W R+148) := by
    simp [S4Power.W]
    omega
  rw [hw, pow2_four]

/-- The exact halting arithmetic for any genuine reduced stack at or after
    the nine-return synchronization is one of the two phase-specific tail
    powers. The statement is on all natural times, never a finite trace. -/
theorem rooted_halt_gate_iff_two_tails (n : Nat) (s : List Nat)
    (hroot : compactRun (9+n) [42,12,8,5] = some s) :
    (∃ k : Nat, _root_.W s+45=2^k) ↔
    (n%8=4 ∧ ∃ R, s=80::150::R ∧ (∃ k, _root_.W R+107=2^k)) ∨
    (n%8=7 ∧ ∃ R, s=82::231::R ∧ (∃ k, _root_.W R+148=2^k)) := by
  have hr : S4.reducedRun (9+n) [42,12,8,5] = some s := by
    rw [← compactRun_eq_reducedRun]
    exact hroot
  constructor
  · intro hpow
    have hnone : S4.reduced s = none := by
      rw [reduced_eq_native]
      exact (S4NativeCompact.nativeReduced_none_iff_pow2 s).mpr hpow
    obtain h4 | h7 := S4.actual_only_two_hazard_phases n s hr hnone
    · obtain ⟨R,hs⟩ := S4.actual_pair_cycle n s hr
      have heq : s=80::150::R := by simpa [S4.pairPhase,h4] using hs
      refine Or.inl ⟨h4,R,heq,?_⟩
      rw [heq] at hpow
      exact (tail_gate_80 R).mp hpow
    · obtain ⟨R,hs⟩ := S4.actual_pair_cycle n s hr
      have heq : s=82::231::R := by simpa [S4.pairPhase,h7] using hs
      refine Or.inr ⟨h7,R,heq,?_⟩
      rw [heq] at hpow
      exact (tail_gate_82 R).mp hpow
  · rintro (⟨h4,R,heq,hpow⟩ | ⟨h7,R,heq,hpow⟩)
    · rw [heq]
      exact (tail_gate_80 R).mpr hpow
    · rw [heq]
      exact (tail_gate_82 R).mpr hpow

/-- Original six-state raw S4 halting is equivalent to exactly two rooted,
    infinite-horizon tail-weight power-of-two conditions. -/
theorem original_machine_halts_iff_two_tail_powers :
    BusyBeaver.IsHalt
      BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.target ↔
    ∃ n R,
      (n%8=4 ∧
        compactRun (9+n) [42,12,8,5] = some (80::150::R) ∧
        (∃ k : Nat, _root_.W R+107=2^k)) ∨
      (n%8=7 ∧
        compactRun (9+n) [42,12,8,5] = some (82::231::R) ∧
        (∃ k : Nat, _root_.W R+148=2^k)) := by
  constructor
  · intro hh
    obtain ⟨n,s,_,hr,hpow⟩ :=
      original_machine_halts_iff_compact_power_gate.mp hh
    rcases (rooted_halt_gate_iff_two_tails n s hr).mp hpow with
    | inl ⟨h4,R,hs,hpow⟩ =>
        refine ⟨n,R,Or.inl ⟨h4,?_,hpow⟩⟩
        simpa [hs] using hr
    | inr ⟨h7,R,hs,hpow⟩ =>
        refine ⟨n,R,Or.inr ⟨h7,?_,hpow⟩⟩
        simpa [hs] using hr
  · rintro ⟨n,R,(⟨h4,hr,hpow⟩ | ⟨h7,hr,hpow⟩)⟩
    · apply original_machine_halts_iff_compact_power_gate.mpr
      exact ⟨n,80::150::R,Or.inl h4,hr,(tail_gate_80 R).mpr hpow⟩
    · apply original_machine_halts_iff_compact_power_gate.mpr
      exact ⟨n,82::231::R,Or.inr h7,hr,(tail_gate_82 R).mpr hpow⟩

#print axioms rooted_halt_gate_iff_two_tails
#print axioms original_machine_halts_iff_two_tail_powers
end S4SourceBridge
