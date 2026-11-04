import Lean
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent48.NeedleTerminalOddInverse

private theorem pow_five_ge_pow_two (n : Nat) : (2:Nat)^n ≤ 5^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      calc
        2^(n+1) = 2^n*2 := by simp [Nat.pow_succ', Nat.mul_comm]
        _ ≤ 5^n*2 := Nat.mul_le_mul_right 2 ih
        _ ≤ 5^n*5 := Nat.mul_le_mul_left (5^n) (by decide)
        _ = 5^(n+1) := by simp [Nat.pow_succ', Nat.mul_comm]

private theorem pow_two_pos (K : Nat) : 0 < (2:Nat)^K :=
  Nat.pow_pos (by decide)

private theorem pow_five_pos (t : Nat) : 0 < (5:Nat)^t :=
  Nat.pow_pos (by decide)

/-- The length t of a nonempty positive odd block into a power-of-two
terminal counter is strictly less than the terminal exponent K. -/
theorem terminal_block_length_lt (K t m : Nat) (hK : 0<K) (hm : 0<m)
    (h : 5^t*m-1=2^K-2) : t < K := by
  have hp5 : 0 < 5^t := pow_five_pos t
  have hmul : 5^t ≤ 5^t*m := by
    simpa using Nat.mul_le_mul_left (5^t) (show 1 ≤ m by omega)
  have htwo : 2 ≤ 2^K := by
    have hpow := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (show 1≤K by omega)
    simpa using hpow
  have hpow : 5^t*m + 1 = 2^K := by omega
  by_cases ht : t < K
  · exact ht
  have hkt : K ≤ t := by omega
  have hmono : 5^K ≤ 5^t := Nat.pow_le_pow_right (by decide) hkt
  have hpow2 : 2^K ≤ 5^K := pow_five_ge_pow_two K
  omega

/-- A positive t-call odd segment can end at the K-th terminal power
if and only if 5^t divides 2^K-1. The positive odd quotient m is unique. -/
theorem terminal_odd_quotient_iff (K t : Nat) (hK : 0<K) :
    (∃ m, 0<m ∧ 5^t*m-1=2^K-2) ↔ (5^t ∣ 2^K-1) := by
  constructor
  · rintro ⟨m,hm,he⟩
    have hp5 : 0<5^t := pow_five_pos t
    have hmul : 0<5^t*m := Nat.mul_pos hp5 hm
    have htwo : 2 ≤ 2^K := by
      have hpow := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (show 1≤K by omega)
      simpa using hpow
    have hpower : 5^t*m+1=2^K := by omega
    exact ⟨m,by omega⟩
  · rintro ⟨m,hm⟩
    have h2 : 1<2^K := by
      have hh : 2 ≤ (2:Nat)^K := by
        have hpow := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (show 1≤K by omega)
        simpa using hpow
      omega
    have h5 : 0<5^t := pow_five_pos t
    have hmp : 0<m := by
      by_cases hz : m=0
      · simp [hz] at hm
        omega
      · omega
    refine ⟨m,hmp,?_⟩
    omega

/-- A finite exact enumeration of all admissible positive block lengths
for reaching a chosen terminal exponent K. -/
def oddTerminalLengths (K : Nat) : List Nat :=
  (List.range K).filter (fun t => 0 < t ∧ 5^t ∣ 2^K-1)

theorem oddTerminalLengths_spec (K t : Nat) (hK : 0<K) :
    t ∈ oddTerminalLengths K ↔
      0<t ∧ ∃ m, 0<m ∧ 5^t*m-1=2^K-2 := by
  simp only [oddTerminalLengths]
  simp only [List.mem_filter, List.mem_range]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨ht, htpos, hdiv⟩
    exact ⟨htpos, (terminal_odd_quotient_iff K t hK).mpr hdiv⟩
  · rintro ⟨htpos, m, hm, he⟩
    exact ⟨terminal_block_length_lt K t m hK hm he, htpos,
       (terminal_odd_quotient_iff K t hK).mp ⟨m,hm,he⟩⟩

#print axioms terminal_block_length_lt
#print axioms terminal_odd_quotient_iff
#print axioms oddTerminalLengths_spec
end BB6.Agent48.NeedleTerminalOddInverse
