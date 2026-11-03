import StackDyadicGate
import Lean.Elab.Tactic.Omega

namespace Agent15Stack

theorem encode_cons_mod_two (a : Nat) (L : List Nat) :
    encode (a::L)%2 = 1 := by
  have h := encode_cons_succ a L
  have hdvd : 2 ∣ encode (a::L)+1 := by
    rw [h,Nat.pow_succ]
    exact ⟨2^a*(2*encode L+1), by ac_rfl⟩
  omega

theorem encode_zero_or_odd (L : List Nat) :
    encode L = 0 ∨ encode L%2 = 1 := by
  cases L with
  | nil => left; rfl
  | cons a L => right; exact encode_cons_mod_two a L

/-- For this exact Fibonacci binary-word encoding, the 4-bit
    residue 3 is possible only for the singleton stack [1]. -/
theorem encode_mod16_three_iff_singleton_one (L : List Nat) :
    encode L%16 = 3 ↔ L = [1] := by
  constructor
  · intro h
    cases L with
    | nil => simp [encode] at h
    | cons a L =>
      rcases a with _ | _ | a
      · rw [encode_zero] at h
        omega
      · rw [encode_one] at h
        have hp := encode_zero_or_odd L
        rcases hp with hp | hp
        · exact (encode_zero_iff L).mp hp ▸ rfl
        · omega
      · have heq : 2^((a+2)+1) = 8*2^a := by
          rw [show a+2+1 = ((a+1)+1)+1 by omega]
          repeat rw [Nat.pow_succ]
          omega
        have hp := encode_cons_succ (a+2) L
        have hdvd : 8 ∣ encode ((a+2)::L)+1 := by
          rw [hp,heq]
          exact ⟨2^a*(2*encode L+1), by ac_rfl⟩
        have hh : a+1+1 = a+2 := by omega
        rw [hh] at h
        omega
  · intro h
    subst L
    decide

/-- The exact, all-time halting obligation for the transcribed
    two-mode stack rules is an encoded D-mode cylinder. -/
theorem blank_halts_iff_mod16_cylinder :
    (∃ n, run n = none) ↔
      (∃ n L R, run n = some (.D,L,R) ∧ encode L%16 = 3 ∧ 0 < encode R) := by
  constructor
  · intro hh
    obtain ⟨n,L,R,hn,hl,hr⟩ := blank_halts_iff_encoded_three.mp hh
    exact ⟨n,L,R,hn,(encode_mod16_three_iff_singleton_one L).mpr
      ((encode_three_iff L).mp hl),hr⟩
  · rintro ⟨n,L,R,hn,hl,hr⟩
    apply blank_halts_iff_encoded_three.mpr
    exact ⟨n,L,R,hn,(encode_three_iff L).mpr
      ((encode_mod16_three_iff_singleton_one L).mp hl),hr⟩

#print axioms encode_mod16_three_iff_singleton_one
#print axioms blank_halts_iff_mod16_cylinder

end Agent15Stack
