import S4RawTwoGates
import S4PowerNative

namespace S4SourceBridge

open BusyBeaver.M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF

theorem reduced_bump_eq (k : Nat) (T : List Nat) :
    S4.bumpBy k T = S4SourceShape.bumpN k T := by
  rw [← S4SourceBridge.bumpBy_eq k T, S4NativeCompact.bumpN_eq k T]

theorem reduced_bump17_eq (T : List Nat) :
    S4.bumpBy 17 T = _root_.bump17 T := by
  rw [reduced_bump_eq 17 T]
  cases T with
  | nil => decide
  | cons b S => rfl

theorem reduced_eq_native (T : List Nat) :
    S4.reduced T = S4NativeCompact.nativeReduced T := by
  unfold S4.reduced S4.dangerous S4NativeCompact.nativeReduced
  rw [reduced_bump_eq 31 T]
  rw [← S4SourceBridge.epoch_eq (S4SourceShape.bumpN 31 T) 27 [0,6,5,3,1]]
  cases h : stepEpoch 27 (S4SourceShape.bumpN 31 T) [0,6,5,3,1] with
  | none => simp [h]
  | some s =>
      cases s with
      | C a L =>
          simp only [h, Option.map_some, S4SourceBridge.unwrap,
            S4NativeCompact.unwrap, Prod.snd]
          exact reduced_bump17_eq (L.drop 4)

/-- Raw halting iff a genuinely attained, exceptional-phase reduced stack
    meets the complete 2-adic power-of-two stopping equation. -/
theorem original_machine_halts_iff_power_gate :
    BusyBeaver.IsHalt target ↔
    ∃ n s, (n % 8 = 4 ∨ n % 8 = 7) ∧
      S4.reducedRun (9+n) [42,12,8,5] = some s ∧
      (∃ k : Nat, _root_.W s + 45 = 2^k) := by
  rw [S4SourceBridge.original_machine_halts_iff_two_exceptional_gates]
  constructor
  · rintro ⟨n, s, hp, hr, hnone⟩
    refine ⟨n, s, hp, hr, ?_⟩
    apply (S4NativeCompact.nativeReduced_none_iff_pow2 s).mp
    rw [← reduced_eq_native]
    exact hnone
  · rintro ⟨n, s, hp, hr, hpow⟩
    refine ⟨n, s, hp, hr, ?_⟩
    rw [reduced_eq_native]
    exact (S4NativeCompact.nativeReduced_none_iff_pow2 s).mpr hpow

#print axioms reduced_eq_native
#print axioms original_machine_halts_iff_power_gate

end S4SourceBridge
