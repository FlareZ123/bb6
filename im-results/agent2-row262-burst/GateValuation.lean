import Valuation
set_option maxHeartbeats 1000000
namespace BB6.Row262

theorem v2_zero_iff_odd (n : Nat) (hn : n > 0) :
    v2 n = 0 ↔ n % 2 = 1 := by
  constructor
  · intro hv
    by_cases he : n % 2 = 0
    · have mpos : n/2 > 0 := by omega
      have heq : n = 2*(n/2) := by omega
      rw [heq, v2_twice _ mpos] at hv
      omega
    · omega
  · intro hm
    rw [v2]
    simp [Nat.ne_of_gt hn, show n%2 ≠ 0 by omega]

theorem v2_one_iff_mod4_two (n : Nat) (hn : n > 0) :
    v2 n = 1 ↔ n % 4 = 2 := by
  have ht : n%2=0 → n=2*(n/2) := by omega
  constructor
  · intro hv
    have he : n % 2 = 0 := v2_pos_even n hn (by omega)
    have hm : n/2>0 := by omega
    have hz : v2 (n/2)=0 := by
      have hf := v2_twice (n/2) hm
      rw [ht he, hf] at hv
      omega
    have ho := (v2_zero_iff_odd (n/2) hm).1 hz
    omega
  · intro hmod
    have he : n%2=0 := by omega
    have hm : n/2>0 := by omega
    have ho : (n/2)%2=1 := by omega
    have hz := (v2_zero_iff_odd (n/2) hm).2 ho
    rw [ht he,v2_twice (n/2) hm,hz]

theorem halt_gate_v2 (R : Nat) : R % 4 = 3 ↔ v2 (7*R+9) = 1 := by
  have hp : 7*R+9 > 0 := by omega
  have heq := v2_one_iff_mod4_two (7*R+9) hp
  constructor
  · intro h
    apply heq.mpr
    omega
  · intro h
    have hmod := heq.mp h
    omega

-- Exactly two primitive source transitions from any A0 configuration.
private def frozenF1 (c : Cfg) : Prop := c.st=5 ∧ c.head=true

theorem gate_exact2 (ls rs : List Bool) :
    frozenF1 (run 2 ⟨0,ls,false,rs⟩) ↔ bitsVal rs % 4 = 3 := by
  cases rs with
  | nil => simp [frozenF1, run, step, moveL, moveR, bitsVal] <;> omega
  | cons b rs =>
      cases b with
      | false => simp [frozenF1, run, step, moveL, moveR, bitsVal] <;> omega
      | true =>
          cases rs with
          | nil => simp [frozenF1,run,step,moveR,bitsVal]
          | cons c zs =>
              cases c <;> simp [frozenF1,run,step,moveR,bitsVal] <;> omega

-- Equivalent 2-adic oracle for the source's A0/right11 frozen halting gate.
theorem gate_exact2_valuation (ls rs : List Bool) :
    frozenF1 (run 2 ⟨0,ls,false,rs⟩) ↔ v2 (7*bitsVal rs+9) = 1 := by
  rw [gate_exact2, halt_gate_v2]

#print axioms BB6.Row262.v2_zero_iff_odd
#print axioms BB6.Row262.v2_one_iff_mod4_two
#print axioms BB6.Row262.halt_gate_v2
#print axioms BB6.Row262.gate_exact2
#print axioms BB6.Row262.gate_exact2_valuation
end BB6.Row262
