import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43TwoLayer

/-- A binary power with a smaller positive remainder cannot hide its
power-of-two divisor in the exponent factor. -/
theorem binary_remainder
    (e t K A R : Nat) (hpos : 0 < R) (hsmall : R < 2^e)
    (heq : K*2^e = A*2^t+R) :
    t ≤ e ∧ 2^t ≤ R := by
  by_cases h : t ≤ e
  · have hdiv : 2^t ∣ 2^e := Nat.pow_dvd_pow 2 h
    obtain ⟨q,hq⟩ := hdiv
    have hleft : 2^t ∣ K*2^e := by
      refine ⟨K*q, ?_⟩
      rw [hq]
      ac_rfl
    have hright : 2^t ∣ A*2^t := Nat.dvd_mul_left _ _
    have hd := Nat.dvd_sub hleft hright
    have hdiff : K*2^e-A*2^t=R := by omega
    rw [hdiff] at hd
    exact ⟨h, Nat.le_of_dvd hpos hd⟩
  · have hrev : e ≤ t := by omega
    have hdiv : 2^e ∣ 2^t := Nat.pow_dvd_pow 2 hrev
    obtain ⟨q,hq⟩ := hdiv
    have hleft : 2^e ∣ K*2^e := Nat.dvd_mul_left _ _
    have hright : 2^e ∣ A*2^t := by
      refine ⟨A*q, ?_⟩
      rw [hq]
      ac_rfl
    have hd := Nat.dvd_sub hleft hright
    have hdiff : K*2^e-A*2^t=R := by omega
    rw [hdiff] at hd
    have hge := Nat.le_of_dvd hpos hd
    omega

/-- Cubic separation after 48, proved by four-index growth. -/
theorem cubic_bound_48 (n : Nat) (hn : 48 ≤ n) :
    8400000*(n+2)^3 < 2^n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hsmall : n < 52
    · have hc : n=48 ∨ n=49 ∨ n=50 ∨ n=51 := by omega
      rcases hc with h|h|h|h <;> subst n <;> decide
    · have hnprev : 48 ≤ n-4 := by omega
      have hi := ih (n-4) (by omega) hnprev
      have hlin : n+2 ≤ 2*((n-4)+2) := by omega
      have hg := Nat.pow_le_pow_left hlin 3
      have hcube : (n+2)^3 ≤ 8*((n-4)+2)^3 := by
        calc
          (n+2)^3 ≤ (2*((n-4)+2))^3 := hg
          _ = 8*((n-4)+2)^3 := by
              rw [show (8:Nat) = 2*2*2 by decide]
              simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one]
              ac_rfl
      have hscale : 8400000*(n+2)^3 ≤
          8*(8400000*((n-4)+2)^3) := by
        have hh := Nat.mul_le_mul_left 8400000 hcube
        calc
          8400000*(n+2)^3 ≤ 8400000*(8*((n-4)+2)^3) := hh
          _ = 8*(8400000*((n-4)+2)^3) := by ac_rfl
      have hpow : 2^n=16*2^(n-4) := by
        have he : n=(n-4)+4 := by omega
        rw [he,Nat.pow_add]
        simp [Nat.mul_comm]
      omega

#print axioms BB6.Agent43TwoLayer.binary_remainder
#print axioms BB6.Agent43TwoLayer.cubic_bound_48
end BB6.Agent43TwoLayer

namespace BB6.Agent43TwoLayer

/-- A second shallow transition needs a large power-of-two remainder;
this abstract theorem rules it out whenever the first two residues
stay linear and the terminal defect is linearly bounded. -/
theorem two_layer_abstract_barrier
    (n s u r alpha beta q p a b K R1 R2 E : Nat)
    (hn : 48 ≤ n)
    (hqp : q*p = 2^n)
    (hqd : ∃ d, q*d = 14*n+92)
    (hq : q = 8^s)
    (hExp : p = 2^(n-3*s)) (hs : 3*s≤n)
    (ha : a = 2^alpha) (hb : b=2^beta)
    (hz : alpha≤2) (hzpos : 1≤alpha)
    (hbeta : beta≤2) (hbetapos : 1≤beta)
    (hK : 392*(q*(a*8^u)) ≤ K)
    (hR1 : 0<R1) (hR1bound : R1≤400*(n+2))
    (hR2 : 0<R2)
    (hR2bound : alpha+3*u≤n-3*s → R2≤600*(n+2))
    (hEbound : beta+3*r≤(n-3*s)-(alpha+3*u) → E≤2000*(n+2))
    (heq : K*p = (a*8^u)*(b*8^r*E+R2)+R1) : False := by
  let X := n+2
  let z := a*8^u
  let v := b*8^r
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hpNat : 0<2^n := Nat.pow_pos (by decide)
  have hqpos : 0<q := by rw [hq]; exact Nat.pow_pos (by decide)
  have hapos : 0<a := by rw [ha]; exact Nat.pow_pos (by decide)
  have hbpos : 0<b := by rw [hb]; exact Nat.pow_pos (by decide)
  have hzpos2 : 0<z := Nat.mul_pos hapos (Nat.pow_pos (by decide))
  have hvpos : 0<v := Nat.mul_pos hbpos (Nat.pow_pos (by decide))
  have hqle : q≤21*X := by
    obtain ⟨d,hd⟩ := hqd
    have hdp : 1≤d := by
      by_cases hzero : d=0
      · rw [hzero] at hd
        simp at hd
      · omega
    have hle : q≤q*d := by
      simpa using (Nat.mul_le_mul_left q hdp)
    dsimp [X]
    omega
  have hX23 : X^2≤X^3 := by
    calc
      X^2 = X^2*1 := by omega
      _ ≤ X^2*X := Nat.mul_le_mul_left _ hX
      _ = X^3 := (Nat.pow_succ X 2).symm
  have htwoPow : (8:Nat)^u = 2^(3*u) := by
    simpa only [show (8:Nat)=2^3 by decide] using
      (Nat.pow_mul 2 3 u).symm
  have htwoPowR : (8:Nat)^r = 2^(3*r) := by
    simpa only [show (8:Nat)=2^3 by decide] using
      (Nat.pow_mul 2 3 r).symm
  have hzPow : z=2^(alpha+3*u) := by
    dsimp [z]
    rw [ha,htwoPow, Nat.pow_add]
  have hvPow : v=2^(beta+3*r) := by
    dsimp [v]
    rw [hb,htwoPowR, Nat.pow_add]
  have hqR1 : q*R1 ≤ 8400*X^2 := by
    calc
      q*R1 ≤ (21*X)*(400*X) := Nat.mul_le_mul hqle hR1bound
      _ = 8400*X^2 := by
        rw [show (8400:Nat)=21*400 by decide]
        simp only [Nat.pow_succ,Nat.pow_zero]
        ac_rfl
  have hsmallSq : 8400*X^2 ≤ 8400000*X^3 := by
    calc
      8400*X^2 ≤8400*X^3 := Nat.mul_le_mul_left 8400 hX23
      _ ≤8400000*X^3 := Nat.mul_le_mul_right _ (by decide : 8400≤8400000)
  have hgap := cubic_bound_48 n hn
  have hR1small : R1 < p := by
    have hh : q*R1 < q*p := by rw [hqp]; exact Nat.lt_of_le_of_lt (Nat.le_trans hqR1 hsmallSq) hgap
    exact Nat.lt_of_mul_lt_mul_left hh
  have hEq1 : K*2^(n-3*s) = (v*E+R2)*2^(alpha+3*u)+R1 := by
    rw [←hExp, ←hzPow]
    simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, z, v] using heq
  obtain ⟨hpart1, hzLe⟩ := binary_remainder (n-3*s) (alpha+3*u) K (v*E+R2) R1
    hR1 (by simpa only [hExp] using hR1small) hEq1
  have hzDvdP : z ∣ p := by
    rw [hzPow,hExp]
    exact Nat.pow_dvd_pow 2 hpart1
  obtain ⟨p2,hp2⟩ := hzDvdP
  have hzDvdR1 : z ∣ R1 := by
    have hleft : z ∣ K*p := by
      refine ⟨K*p2, ?_⟩
      rw [hp2]
      ac_rfl
    have hright : z ∣ z*(v*E+R2) := by
      exact ⟨v*E+R2,rfl⟩
    have hh := Nat.dvd_sub hleft hright
    have hdiff : K*p - z*(v*E+R2)=R1 := by
      simpa only [z,v] using (show K*p - (a*8^u)*(b*8^r*E+R2)=R1 by omega)
    rw [hdiff] at hh
    exact hh
  obtain ⟨d1,hd1⟩ := hzDvdR1
  have hd1le : d1≤R1 := by
    have hh : d1 ≤ z*d1 := by
      have hzp :1≤z := hzpos2
      simpa using (Nat.mul_le_mul_right d1 hzp)
    rw [hd1]
    exact hh
  have hR2small : R2≤600*X := hR2bound hpart1
  have hRsmall : R2+d1≤1000*X := by
    have hd1b :d1≤400*X := Nat.le_trans hd1le hR1bound
    dsimp [X]
    omega
  have hRpos : 0<R2+d1 := by omega
  have hqzBound : q*z≤8400*X^2 :=
    Nat.le_trans (Nat.mul_le_mul_left q (by simpa only [hzPow] using hzLe)) hqR1
  have hqzRBound : q*z*(R2+d1) ≤8400000*X^3 := by
    calc
      q*z*(R2+d1) ≤ (8400*X^2)*(1000*X) := Nat.mul_le_mul hqzBound hRsmall
      _ =8400000*X^3 := by
        rw [show (8400000:Nat)=8400*1000 by decide]
        simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one]
        ac_rfl
  have hRsmallp2 : R2+d1 < p2 := by
    have hprod : q*z*(R2+d1)<q*z*p2 := by
      have ht :q*z*p2=2^n := by
        rw [←hqp,hp2]
        ac_rfl
      rw [ht]
      exact Nat.lt_of_le_of_lt hqzRBound hgap
    have hprod' : (q*z)*(R2+d1)<(q*z)*p2 := by simpa [Nat.mul_assoc] using hprod
    exact Nat.lt_of_mul_lt_mul_left hprod'
  have hp2Pow : p2=2^((n-3*s)-(alpha+3*u)) := by
    have hpSplit : 2^(n-3*s) = 2^(alpha+3*u)*2^((n-3*s)-(alpha+3*u)) := by
      have he : (alpha+3*u)+((n-3*s)-(alpha+3*u))=n-3*s := by omega
      calc
        2^(n-3*s) = 2^((alpha+3*u)+((n-3*s)-(alpha+3*u))) := by rw [he]
        _ = 2^(alpha+3*u)*2^((n-3*s)-(alpha+3*u)) := Nat.pow_add _ _ _
    have hc : z*p2=z*2^((n-3*s)-(alpha+3*u)) := by
      rw [hzPow,hExp] at hp2
      rw [hzPow, ← hp2, hpSplit]
    exact Nat.eq_of_mul_eq_mul_left hzpos2 hc
  have hEq2 : K*p2=v*E+(R2+d1) := by
    have hc : z*(K*p2)=z*(v*E+(R2+d1)) := by
      calc
        z*(K*p2) = K*p := by rw [hp2]; ac_rfl
        _ = z*(v*E+R2)+R1 := by simpa [z,v] using heq
        _ = z*(v*E+(R2+d1)) := by rw [hd1]; simp [Nat.mul_add]; ac_rfl
    exact Nat.eq_of_mul_eq_mul_left hzpos2 hc
  have hEq3 : K*2^((n-3*s)-(alpha+3*u)) = E*2^(beta+3*r)+(R2+d1) := by
    rw [←hp2Pow, ←hvPow]
    simpa only [Nat.mul_comm,Nat.mul_assoc] using hEq2
  obtain ⟨hpart2,hvLe⟩ := binary_remainder
      ((n-3*s)-(alpha+3*u)) (beta+3*r) K E (R2+d1) hRpos (by simpa only [hp2Pow] using hRsmallp2) hEq3
  have hUpper : K*p2≤(R2+d1)*(E+1) := by
    have hval : v*E≤(R2+d1)*E := Nat.mul_le_mul_right E (by simpa [hvPow] using hvLe)
    have hdist : (R2+d1)*(E+1)=(R2+d1)*E+(R2+d1) := by
      rw [Nat.mul_add]
      simp
    rw [hEq2,hdist]
    omega
  have hEsmall : E≤2000*X := hEbound hpart2
  have hUpperX : (R2+d1)*(E+1)≤2001000*X^2 := by
    have he : E+1≤2001*X := by omega
    calc
      (R2+d1)*(E+1) ≤ (1000*X)*(2001*X) := Nat.mul_le_mul hRsmall he
      _ = 2001000*X^2 := by
        rw [show (2001000:Nat)=1000*2001 by decide]
        simp only [Nat.pow_succ,Nat.pow_zero]
        ac_rfl
  have hLower :392*2^n≤K*p2 := by
    have hh := Nat.mul_le_mul_right p2 hK
    calc
      392*2^n = (392*(q*z))*p2 := by
        rw [←hqp,hp2]
        dsimp [z]
        ac_rfl
      _ ≤K*p2 := hh
  have hSmallFinal : 2001000*X^2 < 2^n := by
    have hconst : 2001000*X^2≤8400000*X^3 :=
      calc
        2001000*X^2≤2001000*X^3 := Nat.mul_le_mul_left 2001000 hX23
        _ ≤8400000*X^3 := Nat.mul_le_mul_right _ (by decide : 2001000≤8400000)
    exact Nat.lt_of_le_of_lt hconst hgap
  omega

#print axioms BB6.Agent43TwoLayer.two_layer_abstract_barrier
end BB6.Agent43TwoLayer