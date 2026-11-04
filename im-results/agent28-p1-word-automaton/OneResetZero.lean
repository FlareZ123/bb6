import OneResetSourceBridge

namespace BB6.Agent28
open BB6.Agent1Quarter BB6.Agent1UpperTail

private theorem zero_dom_pow (n : Nat) (hn : 4 ≤ n) : n+4 ≤ 2^n := by
  have hb : ∀ t:Nat, (t+4)+4 ≤ 2^(t+4) := by
    intro t
    induction t with
    | zero => decide
    | succ t ih =>
        have hidx : (t+1)+4 = (t+4)+1 := by omega
        rw [hidx, Nat.pow_succ]
        omega
  have heq : (n-4)+4 = n := by omega
  simpa only [heq] using hb (n-4)

/-- Original-source n≥30 affine wall cannot occur on an all-depth upper-only odd cone. -/
theorem source_critical_zero_reset_no_wall
    (n b d m r : Nat) (hn : 30 ≤ n)
    (hpre : UpperTail (14*2^n-2*n-16) 3 0 b d m r)
    (hwall : b=4*(m+n)) : False := by
  let x : Nat := n+2
  let P : Nat := 2^n
  let R : Nat := 2^r
  let b0 : Nat := 14*P-2*n-16
  have hdom : n+4 ≤ P := zero_dom_pow n (by omega)
  have hpreDy := upper_tail_dyadic b0 3 0 b d m r
    (by simpa only [b0,P] using hpre)
  have hprepow : R*(b+12)=b0+12 := hpreDy.1
  have hmr : m=r := by omega
  let Fr : Nat := (b+12)/2
  have hFr : 2*Fr=b+12 := by dsimp [Fr]; omega
  have hroot : R*Fr+x=7*P := by
    have hh : 2*(R*Fr)=14*P-2*n-4 := by
      calc
        _ = R*(b+12) := by rw [←hFr]; ac_rfl
        _ = b0+12 := hprepow
        _ = 14*P-2*n-4 := by dsimp [b0]; omega
    dsimp [x]; omega
  have hxP : x<P := by dsimp [x]; omega
  have hbR := power_remainder_division n r 7 Fr x (by dsimp [x]; omega) hxP
    (by simpa only [R,P,x] using hroot)
  have hRle : R≤x := hbR.2
  have hrlt : r<R := Nat.lt_pow_self (by decide : 1<(2:Nat))
  have hFrbound : Fr≤5*x := by
    dsimp [x]
    omega
  have hRFr : R*Fr ≤ x*(5*x) := Nat.mul_le_mul hRle hFrbound
  have hbudget : R*Fr + x ≤ 6*x^2 := by
    have hh : x≤x^2 := by
      have h := Nat.pow_le_pow_right (show 0<x by dsimp [x]; omega) (by decide : 1≤2)
      simpa using h
    have hmul : x*(5*x)=5*x^2 := by simp only [Nat.pow_succ,Nat.pow_zero]; ac_rfl
    omega
  have hgrowth : 24*x^3*(24*x+3)<7*P := by
    simpa only [P,x] using quartic_growth n hn
  have h2 : x^2≤x^3 := Nat.pow_le_pow_right (show 0<x by dsimp [x]; omega) (by decide : 2≤3)
  have h6 : 6*x^2 ≤ 24*x^3 := by omega
  have hfactor : 1≤24*x+3 := by omega
  have h7 : 24*x^3≤24*x^3*(24*x+3) := by
    have hh := Nat.mul_le_mul_left (24*x^3) hfactor
    simpa using hh
  omega

#print axioms BB6.Agent28.source_critical_zero_reset_no_wall
end BB6.Agent28
