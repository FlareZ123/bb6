import UniformResetChain
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace BB6.Agent50TwoReset
private theorem octic_step (x : Nat) (hx:64≤x) :
    13824*(x+1)^8 ≤2*(13824*x^8) := by
  have hlin : 64*(x+1)≤65*x := by omega
  have hpow := Nat.pow_le_pow_left hlin 8
  have hratio : 65^8≤2*64^8 := by decide
  have hscaled : 64^8*(13824*(x+1)^8)≤65^8*(13824*x^8) := by
    calc
      _ = 13824*(64*(x+1))^8 := by simp only [Nat.mul_pow]; ac_rfl
      _ ≤13824*(65*x)^8 := Nat.mul_le_mul_left 13824 hpow
      _=65^8*(13824*x^8) := by simp only [Nat.mul_pow]; ac_rfl
  have hscaled2 : 65^8*(13824*x^8)≤(2*64^8)*(13824*x^8) :=
    Nat.mul_le_mul_right _ hratio
  have hscaled3 : 64^8*(13824*(x+1)^8)≤64^8*(2*(13824*x^8)) := by
    calc
      _≤65^8*(13824*x^8) := hscaled
      _≤(2*64^8)*(13824*x^8) := hscaled2
      _=_ := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hscaled3 (by decide)

theorem octic_growth (n:Nat) (hn:62≤n) :
    13824*(n+2)^8 <2^n := by
  have h: ∀ k:Nat, 13824*(k+64)^8 <2^(k+62) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have hs := octic_step (k+64) (by omega)
      have ht : 2*(13824*(k+64)^8)<2*(2^(k+62)) :=
        Nat.mul_lt_mul_of_pos_left ih (by decide)
      calc
        13824*((k+1)+64)^8=13824*((k+64)+1)^8 := by
          rw [show (k+1)+64=(k+64)+1 by omega]
        _ ≤ 2*(13824*(k+64)^8) := hs
        _ < 2*(2^(k+62)) := ht
        _=2^((k+1)+62) := by
          calc
            _=2^(k+62)*2 := Nat.mul_comm 2 (2^(k+62))
            _=2^((k+62)+1) := (Nat.pow_succ 2 (k+62)).symm
            _=2^((k+1)+62) :=
              congrArg (fun z:Nat=>2^z) (by omega)
  simpa only [show (n-62)+64=n+2 by omega,
    show (n-62)+62=n by omega] using h (n-62)

theorem two_additional_resets_exclude_log_wall
    (n K m F D : Nat) (hn:62≤n)
    (hK: K+n+3=7*2^n)
    (h:ResetChain n K 2 m F D)
    (hlog:2^(n-m)<n) : False := by
  have hbudget : budget n 2*(n+2)<2^n := by
    have hh:=octic_growth n hn
    have heq : budget n 2*(n+2)=13824*(n+2)^8 := by
      calc
        _=(24*24*24)*(n+2)^8 := by
          simp only [budget, Nat.pow_succ,Nat.pow_zero]
          ac_rfl
        _=13824*(n+2)^8 := by
          have hc : (24:Nat)*24*24=13824 := by decide
          rw [hc]
    omega
  exact h.excludes_log_wall (by omega) hK hbudget hlog

#print axioms BB6.Agent50TwoReset.octic_growth
#print axioms BB6.Agent50TwoReset.two_additional_resets_exclude_log_wall
end BB6.Agent50TwoReset
