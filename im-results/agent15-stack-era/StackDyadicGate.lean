import StackDyadic
import Lean.Elab.Tactic.Omega

namespace Agent15Stack

theorem encode_cons_pos (a : Nat) (L : List Nat) : 0 < encode (a::L) := by
  have h := encode_cons_succ a L
  have hp : 2 ≤ 2^(a+1) := by
    rw [Nat.pow_succ]
    have := Nat.two_pow_pos a
    omega
  have hm : 2^(a+1) ≤ 2^(a+1)*(2*encode L+1) := by
    have hm' := Nat.mul_le_mul_left (2^(a+1))
      (show 1 ≤ 2*encode L+1 by omega)
    simpa using hm'
  omega

theorem encode_zero_iff (L : List Nat) : encode L = 0 ↔ L = [] := by
  cases L with
  | nil => simp [encode]
  | cons a L =>
    have hp := encode_cons_pos a L
    constructor
    · intro h; omega
    · intro h; cases h

theorem encode_three_iff (L : List Nat) : encode L = 3 ↔ L = [1] := by
  constructor
  · intro h
    cases L with
    | nil => simp [encode] at h
    | cons a L =>
      rcases a with _ | _ | a
      · have hp := encode_cons_succ 0 L
        have hp' : encode (0::L)+1 = 2*(2*encode L+1) := by simpa using hp
        omega
      · change encode (1::L) = 3 at h
        have hp := encode_one L
        have hzero : encode L = 0 := by omega
        have hnil : L = [] := (encode_zero_iff L).mp hzero
        simp [hnil]
      · have hh : a+1+1 = a+2 := by omega
        rw [hh] at h
        have hp := encode_cons_succ (a+2) L
        have hpow : 8 ≤ 2^((a+2)+1) := by
          have hpos := Nat.two_pow_pos a
          have heq : 2^((a+2)+1) = 8*2^a := by
            rw [show a+2+1 = ((a+1)+1)+1 by omega]
            repeat rw [Nat.pow_succ]
            omega
          omega
        have hmul : 2^((a+2)+1) ≤ 2^((a+2)+1)*(2*encode L+1) := by
          have ht := Nat.mul_le_mul_left (2^((a+2)+1))
            (show 1 ≤ 2*encode L+1 by omega)
          simpa using ht
        omega
  · intro h
    subst L
    decide

/-- The exact, all-time arithmetic-face halting criterion for the copied
    DeepMind two-mode stack map: D-mode left binary word 11 (=3), with a
    nonempty right binary word. This does not solve that reachability problem. -/
theorem blank_halts_iff_encoded_three :
    (∃ n, run n = none) ↔
      (∃ n L R, run n = some (.D,L,R) ∧ encode L = 3 ∧ 0 < encode R) := by
  constructor
  · intro hh
    obtain ⟨n,e,T,hn⟩ := blank_halts_iff_singleton_feeder.mp hh
    exact ⟨n,[1],e::T,hn,by decide,encode_cons_pos e T⟩
  · rintro ⟨n,L,R,h,hl,hr⟩
    have hL : L = [1] := (encode_three_iff L).mp hl
    cases R with
    | nil => simp [encode] at hr
    | cons e R =>
      apply blank_halts_iff_singleton_feeder.mpr
      exact ⟨n,e,R,by simpa [hL] using h⟩

#print axioms encode_three_iff
#print axioms blank_halts_iff_encoded_three

end Agent15Stack
