import Std
namespace BB6.Agent28
private def F (x : Nat) : Nat := 24*x^3*(24*x+3)
private theorem step_scale (x : Nat) (hx : 32 ≤ x) : F (x+1) ≤ 2*F x := by
  have ha : 32*(x+1) ≤ 33*x := by omega
  have hb : 32*(24*(x+1)+3) ≤ 33*(24*x+3) := by omega
  have hpow := Nat.pow_le_pow_left ha 3
  have hprod := Nat.mul_le_mul hpow hb
  have hscaled : 32^4*F (x+1) ≤ 33^4*F x := by
    calc
      _ = 24*((32*(x+1))^3*(32*(24*(x+1)+3))) := by
        simp only [F, Nat.pow_succ, Nat.pow_zero]
        ac_rfl
      _ ≤ 24*((33*x)^3*(33*(24*x+3))) := Nat.mul_le_mul_left 24 hprod
      _ = 33^4*F x := by
        simp only [F, Nat.pow_succ, Nat.pow_zero]
        ac_rfl
  have hratio : 33^4 ≤ 2*(32^4) := by decide
  have hscale2 : 33^4*F x ≤ (2*32^4)*F x := Nat.mul_le_mul_right (F x) hratio
  have h : 32^4*F (x+1) ≤ 32^4*(2*F x) := by
    calc
      _ ≤ 33^4*F x := hscaled
      _ ≤ (2*32^4)*F x := hscale2
      _ = 32^4*(2*F x) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left h (by decide)

private theorem growth_plus (k:Nat) : F (k+32) < 7*2^(k+30) := by
  induction k with
  | zero => decide
  | succ k ih =>
      have hs : F ((k+32)+1) ≤ 2*F (k+32) := step_scale (k+32) (by omega)
      have ht : 2*F (k+32) < 2*(7*2^(k+30)) := Nat.mul_lt_mul_of_pos_left ih (by decide)
      have heq : 2*(7*2^(k+30)) = 7*2^((k+1)+30) := by
        have hidx : (k+30)+1 = (k+1)+30 := by omega
        have hmul (q : Nat) : 2*(7*q) = 7*(q*2) := by omega
        calc
          _ = 7*((2:Nat)^(k+30)*2) := hmul (2^(k+30))
          _ = 7*(2:Nat)^((k+30)+1) := congrArg (fun t : Nat => 7*t) (Nat.pow_succ 2 (k+30)).symm
          _ = 7*2^((k+1)+30) := congrArg (fun e : Nat => 7*(2:Nat)^e) hidx
      have hsucc : F ((k+32)+1) < 7*2^((k+1)+30) := by omega
      have hidx : (k+32)+1 = (k+1)+32 := by omega
      simpa only [hidx] using hsucc

theorem quartic_growth (n:Nat) (hn:30 ≤ n) :
  24*(n+2)^3*(24*(n+2)+3) < 7*2^n := by
  have hrep : n = (n-30)+30 := by omega
  have hb := growth_plus (n-30)
  unfold F at hb
  have hidx : (n-30)+32 = n+2 := by omega
  have hpowidx : (n-30)+30 = n := by omega
  simpa only [hidx, hpowidx] using hb

#print axioms BB6.Agent28.quartic_growth
end BB6.Agent28
