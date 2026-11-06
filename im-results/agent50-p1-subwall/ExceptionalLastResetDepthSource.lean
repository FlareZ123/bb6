import CountedWallStrongGateSource

namespace BB6.Agent50ExceptionalDepth

open BB6.Agent28
open BB6.Agent1Quarter
open BB6.Agent1UpperTail
open BB6.Agent47P1
open BB6.Agent43LastResetDraft
open BB6.Agent43LastResetStrength

private theorem five_mul_le_pow (n : Nat) (hn : 5 ≤ n) :
    5*n ≤ 2^n := by
  have hb : ∀ k : Nat, 5*(k+5) ≤ 2^(k+5) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have hidx : (k+1)+5 = (k+5)+1 := by omega
      rw [hidx, Nat.pow_succ]
      omega
  have heq : (n-5)+5 = n := by omega
  simpa only [heq] using hb (n-5)

/-- An exceptional right-five terminal in the original P1 counted inverse
history, below the explicit 2.5*2^n cost threshold, has a uniquely determined
last positive reset depth. The final inverseAt is exactly n+1, its source
counter is c=1, and the preceding hub lies on the displayed affine line.
This is a source theorem about genuine CountCone histories, with no depth
cutoff or simulation assumption. -/
theorem source_mid_cost_exceptional_last_reset_depth
    (n b d m z : Nat)
    (hn : 14 ≤ n)
    (hcost : 2*m+n+2 ≤ 5*2^n)
    (hz : 1 ≤ z)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hd : d=5) :
    ∃ bp dp mp zp k,
      CountCone (14*2^n-2*n-16) 3 bp dp mp zp ∧
      z=zp+1 ∧
      inverseAt bp dp (n+1)=some (k,1) ∧
      b=2*k-4 ∧
      k+m+n+7=7*2^n ∧
      bp+4*m+12=12*2^n ∧
      dp=2*2^n+2*m+3 ∧
      mp+n+2=m := by
  obtain ⟨bp,dp,mp,zp,t,k,c,s,
      hpre,hzEq,hbp,hbp4,hdp,hip,hkp,hcp,htp,htail⟩ :=
    counted_last_positive_reset
      (14*2^n-2*n-16) 3 b d m z h hz
  have hoddEnd : OddCone (14*2^n-2*n-16) 3 b d m :=
    counted_to_odd_cone _ _ _ _ _ _ h
  have hmassEnd := odd_cone_mass
    (14*2^n-2*n-16) 3 b d m hoddEnd
  have hmassEnd' : b+5+2*m=14*2^n-2*n-13 := by
    rw [hd] at hmassEnd
    omega
  have h5n : 5*n ≤ 2^n := five_mul_le_pow n (by omega)
  have hPgap : n+4 < 2*(2^n) := by omega
  have hbigEnd : 7*2^n < b+12 := by omega

  have hoddPre : OddCone (14*2^n-2*n-16) 3 bp dp mp :=
    counted_to_odd_cone _ _ _ _ _ _ hpre
  have hoddReset : OddCone (14*2^n-2*n-16) 3
      (2*k-4) (c+4) (mp+t+1) :=
    OddCone.parent bp dp mp t k c
      hoddPre hbp hbp4 hdp hip hkp hcp
  have hmassReset := odd_cone_mass
    (14*2^n-2*n-16) 3 (2*k-4) (c+4) (mp+t+1) hoddReset
  have hsmallReset : (2*k-4)+12 ≤ 14*2^n := by omega
  have hdyadic := upper_tail_dyadic
    (2*k-4) (c+4) (mp+t+1) b d m s htail
  have hspow : 2^s*(b+12)=(2*k-4)+12 := hdyadic.1
  have hsZero : s=0 := by
    by_cases hs : s=0
    · exact hs
    · have hsp : 1≤s := by omega
      have hpow : (2:Nat)^1 ≤ 2^s :=
        Nat.pow_le_pow_right (by decide) hsp
      simp only [Nat.pow_one] at hpow
      have hmult : 2*(b+12) ≤ 2^s*(b+12) :=
        Nat.mul_le_mul_right (b+12) hpow
      omega
  subst s
  cases htail with
  | root =>
    have hc1 : c=1 := by omega
    have hpowerMass := (inverseAt_iff_power_mass bp dp t k c
      (by omega) hbp4 hdp).mp hip
    rcases hpowerMass with ⟨hpow,hmass⟩
    have hpow1 : dp+bp/2+3=2^(t+2) := by
      simpa [hc1, Nat.pow_add] using hpow
    have hmass1 : 2*k+2*t+3=bp+dp := by
      simpa [hc1] using hmass
    have hbpEven : bp%2=0 := by omega
    have hbpDiv : 2*(bp/2)=bp := by omega
    have hpowStep : 2^(t+3)=2*2^(t+2) := by
      rw [show t+3=t+2+1 by omega, Nat.pow_succ]
      ring
    have hbpEq : bp+2^(t+3)=4*k+4*t+12 := by
      rw [hpowStep, ← hpow1]
      omega
    have hkm : k+m+n+7=7*2^n := by omega
    have hpow4 : 2^(n+4)=16*2^n := by
      rw [Nat.pow_add]
      norm_num
    have hpow3 : 2^(n+3)=8*2^n := by
      rw [Nat.pow_add]
      norm_num
    have hpow2 : 2^(n+2)=4*2^n := by
      rw [Nat.pow_add]
      norm_num
    have hpowUpper : 2^(t+2)<16*2^n := by
      rw [← hpow1]
      have hhalf : bp/2≤bp := by omega
      omega
    have htUpper : t≤n+1 := by
      by_contra hnot
      have hle : n+4≤t+2 := by omega
      have hmono : 2^(n+4)≤2^(t+2) :=
        Nat.pow_le_pow_right (by decide) hle
      rw [hpow4] at hmono
      omega
    have hcostDouble : 4*m+2*n+4≤10*2^n := by omega
    have hk4 : 18*2^n≤4*k+2*n+24 := by omega
    have hdpPos : 1≤dp := by omega
    have htLower : n≤t := by
      by_contra hnot
      have hle : t+3≤n+2 := by omega
      have hmono : 2^(t+3)≤2^(n+2) :=
        Nat.pow_le_pow_right (by decide) hle
      have hmono' : 2^(t+3)≤4*2^n := by
        rw [hpow2] at hmono
        exact hmono
      have hbpLower : 14*2^n≤bp+2*n+12 := by omega
      have hbpUpper : bp+2*n+14≤14*2^n := by omega
      omega
    have htEq : t=n+1 := by
      by_contra hnot
      have htN : t=n := by omega
      have hbpAtN : bp+8*2^n=4*k+4*n+12 := by
        rw [htN,hpow3] at hbpEq
        exact hbpEq
      have hbpAtN' : bp+4*m+16=20*2^n := by omega
      have hmpAtN : mp+n+1=m := by omega
      have hdpAtN : dp+6*2^n=2*m+5 := by omega
      omega
    have hbpAtN1 : bp+16*2^n=4*k+4*n+16 := by
      rw [htEq,hpow4] at hbpEq
      omega
    have hbpExact : bp+4*m+12=12*2^n := by omega
    have hbpdpExact : bp+dp+2*m=14*2^n-9 := by
      rw [htEq] at hmass1
      omega
    have hdpExact : dp=2*2^n+2*m+3 := by omega
    have hmpExact : mp+n+2=m := by omega
    have hipExact : inverseAt bp dp (n+1)=some (k,1) := by
      simpa [htEq,hc1] using hip
    exact ⟨bp,dp,mp,zp,k,hpre,hzEq,hipExact,rfl,hkm,
      hbpExact,hdpExact,hmpExact⟩

#print axioms BB6.Agent50ExceptionalDepth.source_mid_cost_exceptional_last_reset_depth

end BB6.Agent50ExceptionalDepth
