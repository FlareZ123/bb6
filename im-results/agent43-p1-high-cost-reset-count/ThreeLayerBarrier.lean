import ThreeLayerPeel

namespace BB6.Agent43ThreeLayer

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Three shallow transitions separated by dyadic runs cannot meet an exact
wall equation once the critical index is at least 58. -/
theorem three_layer_abstract_barrier
  (n s u v r alpha beta gamma q p a b c K R1 R2 R3 E : Nat)
  (hn : 58≤n)
  (hqp : q*p=2^n)
  (hqd : ∃ d, q*d=14*n+92)
  (hq : q=8^s) (hExp : p=2^(n-3*s))
  (ha : a=2^alpha) (hb : b=2^beta) (hc : c=2^gamma)
  (hK : 392*(q*((a*8^u)*(b*8^v)))≤K)
  (hR1 : 0<R1) (hR1bound : R1≤400*(n+2))
  (hR2 : 0<R2)
  (hR2bound : alpha+3*u≤n-3*s → R2≤600*(n+2))
  (hR3 : 0<R3)
  (hR3bound : beta+3*v≤(n-3*s)-(alpha+3*u) → R3≤600*(n+2))
  (hEbound : gamma+3*r≤((n-3*s)-(alpha+3*u))-(beta+3*v) → E≤2000*(n+2))
  (heq : K*p=(a*8^u)*((b*8^v)*((c*8^r)*E+R3)+R2)+R1) : False := by
  let X := n+2
  let A1 := a*8^u
  let A2 := b*8^v
  let A3 := c*8^r
  let e := n-3*s
  let t1 := alpha+3*u
  let t2 := beta+3*v
  let t3 := gamma+3*r
  have hX : 1≤X := by dsimp [X]; omega
  have hqpos : 0<q := by rw [hq]; exact Nat.pow_pos (by decide)
  have hA1pos : 0<A1 := Nat.mul_pos (by rw [ha]; exact Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  have hA2pos : 0<A2 := Nat.mul_pos (by rw [hb]; exact Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  have hA3pos : 0<A3 := Nat.mul_pos (by rw [hc]; exact Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  have hA1 : A1=2^t1 := by
    dsimp [A1,t1]
    rw [ha,show (8:Nat)=2^3 by decide, ←Nat.pow_mul, Nat.pow_add]
  have hA2 : A2=2^t2 := by
    dsimp [A2,t2]
    rw [hb,show (8:Nat)=2^3 by decide, ←Nat.pow_mul, Nat.pow_add]
  have hA3 : A3=2^t3 := by
    dsimp [A3,t3]
    rw [hc,show (8:Nat)=2^3 by decide, ←Nat.pow_mul, Nat.pow_add]
  have hqle : q≤21*X := by
    obtain ⟨d,hd⟩ := hqd
    have hdpos : 0<d := by
      by_cases hzero : d=0
      · rw [hzero] at hd
        simp at hd
      · omega
    have hle : q≤q*d := by
      simpa using (Nat.mul_le_mul_left q hdpos)
    dsimp [X]
    omega
  have hx23 : X^2≤X^3 := by
    calc
      X^2 = X^2*1 := by omega
      _ ≤ X^2*X := Nat.mul_le_mul_left _ hX
      _ = X^3 := (Nat.pow_succ X 2).symm
  have hx34 : X^3≤X^4 := by
    calc
      X^3 = X^3*1 := by omega
      _ ≤ X^3*X := Nat.mul_le_mul_left _ hX
      _ = X^4 := (Nat.pow_succ X 3).symm
  have hgap := quartic_gap_58 n hn
  have hGapX : 13440000000*X^4<2^n := by simpa [X] using hgap
  have hR1prod : q*R1≤8400*X^2 := by
    calc
      q*R1 ≤ (21*X)*(400*X) := Nat.mul_le_mul hqle hR1bound
      _ = 8400*X^2 := by
        rw [show (8400:Nat)=21*400 by decide]
        simp only [Nat.pow_succ,Nat.pow_zero]
        ac_rfl
  have hR1prodSmall : q*R1<2^n := by
    have hsmall : 8400*X^2≤13440000000*X^4 := by
      calc
        8400*X^2 ≤ 8400*X^3 := Nat.mul_le_mul_left 8400 hx23
        _ ≤ 8400*X^4 := Nat.mul_le_mul_left 8400 hx34
        _ ≤ 13440000000*X^4 := Nat.mul_le_mul_right _ (by decide : 8400≤13440000000)
    exact Nat.lt_of_le_of_lt (Nat.le_trans hR1prod hsmall) hGapX
  have hR1small : R1<2^e := by
    have hh : q*R1<q*p := by rw [hqp]; exact hR1prodSmall
    have hp : R1<p := Nat.lt_of_mul_lt_mul_left hh
    simpa only [hExp,e] using hp
  have hEq1 : K*2^e = (A2*(A3*E+R3)+R2)*2^t1+R1 := by
    rw [←hExp,←hA1]
    simpa only [A1,A2,A3,Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using heq
  obtain ⟨d1,ht1le,hR1eq,hEq2,hd1le,hA1le⟩ :=
    residue_peel e t1 K (A2*(A3*E+R3)+R2) R1 hR1 hR1small hEq1
  have hA1Bound : A1≤400*X := by rw [hA1]; exact Nat.le_trans hA1le hR1bound
  have hR2small : R2≤600*X := hR2bound (by simpa only [t1,e] using ht1le)
  have hRem2Pos : 0<R2+d1 := by omega
  have hRem2Bound : R2+d1≤1000*X := by
    have hd1Bound := Nat.le_trans hd1le hR1bound
    omega
  have hqA1Bound : q*A1≤8400*X^2 := by
    calc
      q*A1 ≤ (21*X)*(400*X) := Nat.mul_le_mul hqle hA1Bound
      _ = 8400*X^2 := by
        rw [show (8400:Nat)=21*400 by decide]
        simp only [Nat.pow_succ,Nat.pow_zero]
        ac_rfl
  have hqA1RemBound : q*A1*(R2+d1)≤8400000*X^3 := by
    calc
      q*A1*(R2+d1) ≤ (8400*X^2)*(1000*X) := Nat.mul_le_mul hqA1Bound hRem2Bound
      _ = 8400000*X^3 := by
        rw [show (8400000:Nat)=8400*1000 by decide]
        simp only [Nat.pow_succ,Nat.pow_zero]
        ac_rfl
  have hprod1 : (q*A1)*2^(e-t1)=2^n := by
    calc
      (q*A1)*2^(e-t1) = q*(2^t1*2^(e-t1)) := by rw [hA1]; ac_rfl
      _ = q*2^e := by
        rw [←Nat.pow_add]
        have heqT : t1+(e-t1)=e := by omega
        rw [heqT]
      _ = 2^n := by rw [←hExp]; exact hqp
  have hRem2Small : R2+d1<2^(e-t1) := by
    have hbound : 8400000*X^3≤13440000000*X^4 := by
      calc
        8400000*X^3 ≤ 8400000*X^4 := Nat.mul_le_mul_left 8400000 hx34
        _ ≤ 13440000000*X^4 := Nat.mul_le_mul_right _ (by decide : 8400000≤13440000000)
    have hb : (q*A1)*(R2+d1)<(q*A1)*2^(e-t1) := by
      rw [hprod1]
      exact Nat.lt_of_le_of_lt (Nat.le_trans hqA1RemBound hbound) hGapX
    exact Nat.lt_of_mul_lt_mul_left hb
  have hEq2' : K*2^(e-t1)=(A3*E+R3)*2^t2+(R2+d1) := by
    rw [←hA2]
    simpa only [Nat.mul_add,Nat.add_assoc,Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using hEq2
  obtain ⟨d2,ht2le,hR2eq,hEq3,hd2le,hA2le⟩ :=
    residue_peel (e-t1) t2 K (A3*E+R3) (R2+d1) hRem2Pos hRem2Small hEq2'
  have hA2Bound : A2≤1000*X := by rw [hA2]; exact Nat.le_trans hA2le hRem2Bound
  have hR3small : R3≤600*X := hR3bound (by simpa only [t2,e,t1] using ht2le)
  have hRem3Pos : 0<R3+d2 := by omega
  have hRem3Bound : R3+d2≤1600*X := by
    have hd2bound := Nat.le_trans hd2le hRem2Bound
    omega
  have hqA1A2Bound : q*A1*A2≤8400000*X^3 := by
    calc
      q*A1*A2 ≤ (8400*X^2)*(1000*X) := Nat.mul_le_mul hqA1Bound hA2Bound
      _ = 8400000*X^3 := by
        rw [show (8400000:Nat)=8400*1000 by decide]
        simp only [Nat.pow_succ,Nat.pow_zero]
        ac_rfl
  have hqA1A2RemBound : q*A1*A2*(R3+d2)≤13440000000*X^4 := by
    calc
      q*A1*A2*(R3+d2) ≤ (8400000*X^3)*(1600*X) := Nat.mul_le_mul hqA1A2Bound hRem3Bound
      _ = 13440000000*X^4 := by
        rw [show (13440000000:Nat)=8400000*1600 by decide]
        simp only [Nat.pow_succ,Nat.pow_zero]
        ac_rfl
  have hprod2 : (q*A1*A2)*2^((e-t1)-t2)=2^n := by
    calc
      (q*A1*A2)*2^((e-t1)-t2) = (q*A1)*(2^t2*2^((e-t1)-t2)) := by rw [hA2]; ac_rfl
      _ = (q*A1)*2^(e-t1) := by
        rw [←Nat.pow_add]
        have heqT : t2+((e-t1)-t2)=e-t1 := by omega
        rw [heqT]
      _ = 2^n := hprod1
  have hRem3Small : R3+d2<2^((e-t1)-t2) := by
    have hb : (q*A1*A2)*(R3+d2)<(q*A1*A2)*2^((e-t1)-t2) := by
      rw [hprod2]
      exact Nat.lt_of_le_of_lt hqA1A2RemBound hGapX
    exact Nat.lt_of_mul_lt_mul_left hb
  have hEq3' : K*2^((e-t1)-t2)=E*2^t3+(R3+d2) := by
    rw [←hA3]
    simpa only [Nat.add_assoc,Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using hEq3
  obtain ⟨d3,ht3le,hR3eq,hEq4,hd3le,hA3le⟩ :=
    residue_peel ((e-t1)-t2) t3 K E (R3+d2) hRem3Pos hRem3Small hEq3'
  have hEsmall : E≤2000*X := hEbound (by simpa only [t3,e,t1,t2] using ht3le)
  have hUpper : K*2^((e-t1)-t2)≤(R3+d2)*(E+1) := by
    have hA : A3*E≤(R3+d2)*E := Nat.mul_le_mul_right E (by simpa [hA3] using hA3le)
    have hdist : (R3+d2)*(E+1)=(R3+d2)*E+(R3+d2) := by rw [Nat.mul_add]; simp
    rw [hEq3,hdist]
    omega
  have hUpperX : (R3+d2)*(E+1)≤3201600*X^2 := by
    have hE : E+1≤2001*X := by omega
    calc
      (R3+d2)*(E+1) ≤ (1600*X)*(2001*X) := Nat.mul_le_mul hRem3Bound hE
      _ = 3201600*X^2 := by
        rw [show (3201600:Nat)=1600*2001 by decide]
        simp only [Nat.pow_succ,Nat.pow_zero]
        ac_rfl
  have hLower : 392*2^n≤K*2^((e-t1)-t2) := by
    have hh := Nat.mul_le_mul_right (2^((e-t1)-t2)) hK
    have hc : 392*2^n = (392*(q*(A1*A2)))*2^((e-t1)-t2) := by
      rw [←hprod2]
      dsimp [A1,A2]
      ac_rfl
    rw [hc]
    simpa only [A1,A2,Nat.mul_assoc] using hh
  have hSmallFinal : 3201600*X^2<2^n := by
    have hsmall : 3201600*X^2≤13440000000*X^4 := by
      calc
        3201600*X^2≤3201600*X^3 := Nat.mul_le_mul_left 3201600 hx23
        _ ≤3201600*X^4 := Nat.mul_le_mul_left 3201600 hx34
        _ ≤13440000000*X^4 := Nat.mul_le_mul_right _ (by decide : 3201600≤13440000000)
    exact Nat.lt_of_le_of_lt hsmall hGapX
  omega

#print axioms three_layer_abstract_barrier
end BB6.Agent43ThreeLayer
