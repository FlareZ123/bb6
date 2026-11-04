import S4RawPowerGate

namespace S4SourceBridge

/-- Standalone compact stack iteration, using the exact Agent 3 transducer
    rather than the 32-epoch intermediate S4 state model. -/
def compactRun : Nat → List Nat → Option (List Nat)
  | 0, T => some T
  | n+1, T => (compactRun n T).bind _root_.compactNext

theorem compactRun_eq_reducedRun (n : Nat) (T : List Nat) :
    compactRun n T = S4.reducedRun n T := by
  have hs : S4.reduced = _root_.compactNext := by
    funext s
    exact (reduced_eq_native s).trans
      (S4NativeCompact.nativeReduced_eq_compactNext s)
  induction n with
  | zero => rfl
  | succ n ih =>
      change (compactRun n T).bind _root_.compactNext =
        (S4.reducedRun n T).bind S4.reduced
      rw [ih, ← hs]

/-- The entire raw-machine open halting question is equivalently a
    power-of-two hit by this explicit one-list transducer at one of two
    authentic phase residues. This does not assert such a hit occurs. -/
theorem original_machine_halts_iff_compact_power_gate :
    BusyBeaver.IsHalt
      BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.target ↔
    ∃ n s, (n%8=4 ∨ n%8=7) ∧
      compactRun (9+n) [42,12,8,5] = some s ∧
      (∃ k : Nat, _root_.W s + 45 = 2^k) := by
  simpa only [← compactRun_eq_reducedRun] using
    original_machine_halts_iff_power_gate

#print axioms compactRun_eq_reducedRun
#print axioms original_machine_halts_iff_compact_power_gate
end S4SourceBridge
