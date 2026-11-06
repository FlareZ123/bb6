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

/-- Every counted right-five endpoint has zero depth-zero tail after
its last positive reset. This is unconditional in n and in the endpoint cost:
the OddCone mass identity and the exact dyadic tail identity are incompatible
with even one zero-depth tail step. -/
theorem source_right_five_last_positive_reset_no_tail
    (n b m z : Nat)
    (hz : 1 ≤ z)
    (h : CountCone (14*2^n-2*n-16) 3 b 5 m z) :
    ∃ bp dp mp zp t k c,
      CountCone (14*2^n-2*n-16) 3 bp dp mp zp ∧
      z=zp+1 ∧
      8≤bp ∧ bp%4=0 ∧ dp%2=1 ∧
      inverseAt bp dp t=some (k,c) ∧
      2≤k ∧ c%2=1 ∧ 1≤t ∧
      UpperTail (2*k-4) (c+4) (mp+t+1) b 5 m 0 := by
  obtain ⟨bp,dp,mp,zp,t,k,c,s,
      hpre,hzEq,hbp,hbp4,hdp,hip,hkp,hcp,htp,htail⟩ :=
    counted_last_positive_reset
      (14*2^n-2*n-16) 3 b 5 m z h hz
  have hoddEnd : OddCone (14*2^n-2*n-16) 3 b 5 m :=
    counted_to_odd_cone _ _ _ _ _ _ h
  have hmassEnd := odd_cone_mass
    (14*2^n-2*n-16) 3 b 5 m hoddEnd
  have hmassEnd' : b+5+2*m=14*2^n-2*n-13 := by omega
  have hoddPre : OddCone (14*2^n-2*n-16) 3 bp dp mp :=
    counted_to_odd_cone _ _ _ _ _ _ hpre
  have hoddReset : OddCone (14*2^n-2*n-16) 3
      (2*k-4) (c+4) (mp+t+1) :=
    OddCone.parent bp dp mp t k c
      hoddPre hbp hbp4 hdp hip hkp hcp
  have hmassReset := odd_cone_mass
    (14*2^n-2*n-16) 3 (2*k-4) (c+4) (mp+t+1) hoddReset
  have hdyadic := upper_tail_dyadic
    (2*k-4) (c+4) (mp+t+1) b 5 m s htail
  have hspow : 2^s*(b+12)=2*k+8 := by omega
  have hcost : m=mp+t+1+s := hdyadic.2
  have hmassEq : 2*k+c+2*(mp+t+1)=b+5+2*m := by omega
  have hreset : 2*k+c=b+5+2*s := by
    rw [hcost] at hmassEq
    omega
  have hrel : 2^s*(b+12)=b+13+2*s-c := by omega
  have hsZero : s=0 := by
    by_cases hs : s=0
    · exact hs
    · have hsp : 1≤s := by omega
      have hcpos : 1≤c := by omega
      have hlin : ∀ q : Nat, q+1≤2^q := by
        intro q
        induction q with
        | zero => decide
        | succ q ih =>
          rw [Nat.pow_succ]
          omega
      have hpos : 12≤b+12 := by omega
      have hmul : 12*s≤s*(b+12) := by
        have hmul' := Nat.mul_le_mul_left s hpos
        omega
      have hstrict : 2*s<12*s := by omega
      have hprod : b+12+s*(b+12)=(s+1)*(b+12) := by
        rw [Nat.add_mul]
        omega
      have hpowmul : (s+1)*(b+12)≤2^s*(b+12) :=
        Nat.mul_le_mul_right (b+12) (hlin s)
      have hlarge : b+12+2*s<2^s*(b+12) := by
        calc
          b+12+2*s < b+12+12*s := by omega
          _ ≤ b+12+s*(b+12) := by omega
          _ = (s+1)*(b+12) := hprod
          _ ≤ 2^s*(b+12) := hpowmul
      omega
  subst s
  exact ⟨bp,dp,mp,zp,t,k,c,hpre,hzEq,hbp,hbp4,hdp,hip,hkp,hcp,htp,htail⟩

#print axioms BB6.Agent50ExceptionalDepth.source_right_five_last_positive_reset_no_tail

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
        Nat.pow_le_pow_right (show 0 < (2:Nat) from by decide) hsp
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
      have hmass' : 2*k+1+2*t+1+1=bp+dp := by
        simpa [hc1] using hmass
      omega
    have hbpEven : bp%2=0 := by omega
    have hbpDiv : 2*(bp/2)=bp := by omega
    have hpowStep : 2^(t+3)=2*2^(t+2) := by
      rw [show t+3=t+2+1 by omega, Nat.pow_succ]
      omega
    have hbpEq : bp+2^(t+3)=4*k+4*t+12 := by
      rw [hpowStep, ← hpow1]
      omega
    have hkm : k+(mp+t+1)+n+7=7*2^n := by omega
    have hpow4 : 2^(n+4)=16*2^n := by
      rw [Nat.pow_add]
      omega
    have hpow3 : 2^(n+3)=8*2^n := by
      rw [Nat.pow_add]
      omega
    have hpow2 : 2^(n+2)=4*2^n := by
      rw [Nat.pow_add]
      omega
    have hpowUpper : 2^(t+2)<16*2^n := by
      rw [← hpow1]
      have hhalf : bp/2≤bp := by omega
      omega
    have hcostDouble : 4*(mp+t+1)+2*n+4≤10*2^n := by omega
    have hdpPos : 1≤dp := by omega
    have hbpUpper : bp+2*n+14≤14*2^n := by omega
    have hpowLower : 4*2^n+4*t+2≤2^(t+3) := by omega
    have hpowN2lt : 2^(n+2)<2^(t+3) := by
      rw [hpow2]
      omega
    have htLower : n≤t := by
      have hexp : n+2<t+3 :=
        (Nat.pow_lt_pow_iff_right (show 1<(2:Nat) from by decide)).mp hpowN2lt
      omega
    have htUpper : t≤n+1 := by
      have hpowLt : 2^(t+2)<2^(n+4) := by
        rw [hpow4]
        exact hpowUpper
      have hexp : t+2<n+4 :=
        (Nat.pow_lt_pow_iff_right (show 1<(2:Nat) from by decide)).mp hpowLt
      omega
    have htEq : t=n+1 := by
      by_cases htN : t=n
      · have hbpAtN : bp+8*2^n=4*k+4*n+12 := by
          rw [htN,hpow3] at hbpEq
          exact hbpEq
        have hbpAtN' : bp+4*(mp+n+1)+16=20*2^n := by omega
        have hdpAtN : dp+6*2^n=2*mp+2*n+7 := by omega
        have hcostN : 2*(mp+n+1)+n+2≤5*2^n := by
          simpa [htN] using hcost
        omega
      · omega
    have hbpAtN1 : bp+16*2^n=4*k+4*n+16 := by
      rw [htEq,hpow4] at hbpEq
      omega
    have hbpExact : bp+4*(mp+t+1)+12=12*2^n := by omega
    have hbpdpExact : bp+dp+2*(mp+t+1)=14*2^n-9 := by
      rw [htEq] at hmass1
      omega
    have hdpExact : dp=2*2^n+2*(mp+t+1)+3 := by omega
    have hmpExact : mp+n+2=mp+t+1 := by omega
    have hipExact : inverseAt bp dp (n+1)=some (k,1) := by
      simpa [htEq,hc1] using hip
    exact ⟨bp,dp,mp,zp,k,hpre,hzEq,hipExact,rfl,hkm,
      hbpExact,hdpExact,hmpExact⟩

/-- Under the full no-zero-tail budget, every exceptional right-five
terminal has one of exactly two adjacent final reset depths. The two cost
bands are separated by a two-integer gap in which no such CountCone history
exists. -/
theorem source_exceptional_last_reset_two_depths
    (n b d m z : Nat)
    (hn : 14 ≤ n)
    (hbudget : 2*m+2*n+7 ≤ 10*2^n)
    (hz : 1 ≤ z)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hd : d=5) :
    ∃ bp dp mp zp k,
      CountCone (14*2^n-2*n-16) 3 bp dp mp zp ∧
      z=zp+1 ∧
      b=2*k-4 ∧
      k+m+n+7=7*2^n ∧
      (
        (inverseAt bp dp n=some (k,1) ∧
          bp+4*m+16=20*2^n ∧
          dp+6*2^n=2*m+5 ∧
          mp+n+1=m ∧
          3*2^n-2≤m)
        ∨
        (inverseAt bp dp (n+1)=some (k,1) ∧
          bp+4*m+12=12*2^n ∧
          dp=2*2^n+2*m+3 ∧
          mp+n+2=m ∧
          m≤3*2^n-5)
      ) := by
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
  have hbigEnd : 7*2^n < b+12 := by omega

  have hoddPre : OddCone (14*2^n-2*n-16) 3 bp dp mp :=
    counted_to_odd_cone _ _ _ _ _ _ hpre
  have hmassPre := odd_cone_mass
    (14*2^n-2*n-16) 3 bp dp mp hoddPre
  have hmassPre' : bp+dp+2*mp=14*2^n-2*n-13 := by omega
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
        Nat.pow_le_pow_right (show 0 < (2:Nat) from by decide) hsp
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
      have hmass' : 2*k+1+2*t+1+1=bp+dp := by
        simpa [hc1] using hmass
      omega
    have hbpEven : bp%2=0 := by omega
    have hbpDiv : 2*(bp/2)=bp := by omega
    have hpowStep : 2^(t+3)=2*2^(t+2) := by
      rw [show t+3=t+2+1 by omega, Nat.pow_succ]
      omega
    have hbpEq : bp+2^(t+3)=4*k+4*t+12 := by
      rw [hpowStep, ← hpow1]
      omega
    have hkm : k+(mp+t+1)+n+7=7*2^n := by omega
    have hpow4 : 2^(n+4)=16*2^n := by
      rw [Nat.pow_add]
      omega
    have hpow3 : 2^(n+3)=8*2^n := by
      rw [Nat.pow_add]
      omega
    have hpow2 : 2^(n+2)=4*2^n := by
      rw [Nat.pow_add]
      omega
    have h5n : 5*n≤2^n := five_mul_le_pow n (by omega)
    have hpowUpper : 2^(t+2)<16*2^n := by
      rw [← hpow1]
      have hhalf : bp/2≤bp := by omega
      omega
    have htUpper : t≤n+1 := by
      have hpowLt : 2^(t+2)<2^(n+4) := by
        rw [hpow4]
        exact hpowUpper
      have hexp : t+2<n+4 :=
        (Nat.pow_lt_pow_iff_right (show 1<(2:Nat) from by decide)).mp hpowLt
      omega
    have hbudgetPrefix : 2*mp+2*n+7≤10*2^n := by omega
    have hdpPos : 1≤dp := by omega
    have hdpFormula : dp+14*2^n=2^(t+3)+2*mp+2*n+7 := by omega
    have htLower : n≤t := by
      by_cases hle : t+3≤n+2
      · have hpowLe : 2^(t+3)≤4*2^n := by
          have hmono : 2^(t+3)≤2^(n+2) :=
            Nat.pow_le_pow_right (show 0<(2:Nat) from by decide) hle
          rw [hpow2] at hmono
          exact hmono
        have hdpBound : dp+14*2^n≤14*2^n := by omega
        omega
      · omega
    have htCases : t=n ∨ t=n+1 := by omega
    rcases htCases with htN | htN1
    · have hbpAtN : bp+8*2^n=4*k+4*n+12 := by
        rw [htN,hpow3] at hbpEq
        exact hbpEq
      have hkmN : k+(mp+n+1)+n+7=7*2^n := by
        rw [htN] at hkm
        exact hkm
      have hbpExact : bp+4*(mp+t+1)+16=20*2^n := by
        rw [htN]
        omega
      have hdpFormulaN := hdpFormula
      rw [htN,hpow3] at hdpFormulaN
      have hdpExact : dp+6*2^n=2*(mp+t+1)+5 := by
        rw [htN]
        omega
      have hmpExact : mp+n+1=mp+t+1 := by
        rw [htN]
      have hmLower : 3*2^n-2≤mp+t+1 := by
        rw [htN]
        omega
      have hipExact : inverseAt bp dp n=some (k,1) := by
        simpa [htN,hc1] using hip
      exact ⟨bp,dp,mp,zp,k,hpre,hzEq,rfl,hkm,
        Or.inl ⟨hipExact,hbpExact,hdpExact,hmpExact,hmLower⟩⟩
    · have hbpAtN1 : bp+16*2^n=4*k+4*n+16 := by
        rw [htN1,hpow4] at hbpEq
        omega
      have hkmN1 : k+(mp+n+2)+n+7=7*2^n := by
        rw [htN1] at hkm
        exact hkm
      have hbpExact : bp+4*(mp+t+1)+12=12*2^n := by
        rw [htN1]
        omega
      have hdpFormulaN1 := hdpFormula
      rw [htN1,show n+1+3=n+4 by omega,hpow4] at hdpFormulaN1
      have hdpExact : dp=2*2^n+2*(mp+t+1)+3 := by
        rw [htN1]
        omega
      have hmpExact : mp+n+2=mp+t+1 := by
        rw [htN1]
      have hmUpper : mp+t+1≤3*2^n-5 := by
        rw [htN1]
        omega
      have hipExact : inverseAt bp dp (n+1)=some (k,1) := by
        simpa [htN1,hc1] using hip
      exact ⟨bp,dp,mp,zp,k,hpre,hzEq,rfl,hkm,
        Or.inr ⟨hipExact,hbpExact,hdpExact,hmpExact,hmUpper⟩⟩

#print axioms BB6.Agent50ExceptionalDepth.source_exceptional_last_reset_two_depths

#print axioms BB6.Agent50ExceptionalDepth.source_mid_cost_exceptional_last_reset_depth

end BB6.Agent50ExceptionalDepth
