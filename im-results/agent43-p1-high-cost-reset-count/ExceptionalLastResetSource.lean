import CountedWallStrongGateSource

namespace BB6.Agent43Exceptional

open BB6.Agent28 BB6.Agent1Quarter BB6.Agent1UpperTail BB6.Agent47P1
open BB6.Agent43LastResetDraft BB6.Agent43LastResetStrength

private theorem n_le_two_pow (n : Nat) : n ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    have hp : 0 < (2:Nat)^n := Nat.pow_pos (by decide)
    omega

/-- A genuine critical P1 inverse path ending at exceptional right coordinate
    d=5 with total cost at most 2^n and at least one positive reset cannot end
    with any zero-depth inverse step. Its final transition itself is a
    positive-depth original inverseAt parent of the actual CountCone. -/
theorem source_low_cost_exceptional_ends_in_positive_reset
    (n b d m z : Nat) (hn : 14 ≤ n) (hz : 1 ≤ z)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hd : d=5) (hm : m ≤ 2^n) :
    ∃ bp dp mp zp t k c,
      CountCone (14*2^n-2*n-16) 3 bp dp mp zp ∧
      z=zp+1 ∧ inverseAt bp dp t=some (k,c) ∧ 1≤t ∧
      b=2*k-4 ∧ d=c+4 ∧ m=mp+t+1 := by
  obtain ⟨bp,dp,mp,zp,t,k,c,s,hpre,hzEq,hbp,hbp4,hdp,hip,hkp,hcp,htp,htail⟩ :=
    counted_last_positive_reset
      (14*2^n-2*n-16) 3 b d m z h hz
  have hoddEnd : OddCone (14*2^n-2*n-16) 3 b d m :=
    counted_to_odd_cone _ _ _ _ _ _ h
  have hmassEnd := odd_cone_mass
    (14*2^n-2*n-16) 3 b d m hoddEnd
  have hnP : n ≤ 2^n := n_le_two_pow n
  have hP4 : 4 ≤ (2:Nat)^n :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hroot : (14*2^n-2*n-16)+2*n+16=14*2^n := by omega
  have hbigEnd : 7*2^n < b+12 := by omega
  have hoddPre : OddCone (14*2^n-2*n-16) 3 bp dp mp :=
    counted_to_odd_cone _ _ _ _ _ _ hpre
  have hoddReset : OddCone (14*2^n-2*n-16) 3
      (2*k-4) (c+4) (mp+t+1) :=
    OddCone.parent bp dp mp t k c
      hoddPre hbp hbp4 hdp hip hkp hcp
  have hmassReset := odd_cone_mass
    (14*2^n-2*n-16) 3
    (2*k-4) (c+4) (mp+t+1) hoddReset
  have hsmallReset : (2*k-4)+12 ≤ 14*2^n := by omega
  have hdyadic := upper_tail_dyadic
    (2*k-4) (c+4) (mp+t+1) b d m s htail
  have hspow : 2^s*(b+12)=(2*k-4)+12 := hdyadic.1
  have hsZero : s=0 := by
    by_cases hs : s=0
    · exact hs
    · have hsp : 1 ≤ s := by omega
      have hpow : (2:Nat)^1 ≤ 2^s :=
        Nat.pow_le_pow_right (by decide) hsp
      simp only [Nat.pow_one] at hpow
      have hmult : 2*(b+12) ≤ 2^s*(b+12) :=
        Nat.mul_le_mul_right (b+12) hpow
      omega
  subst s
  cases htail with
  | root =>
      exact ⟨bp,dp,mp,zp,t,k,c,hpre,hzEq,hip,htp,rfl,rfl,rfl⟩

#print axioms BB6.Agent43Exceptional.source_low_cost_exceptional_ends_in_positive_reset

end BB6.Agent43Exceptional
