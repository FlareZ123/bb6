import OneResetCount

namespace BB6.Agent43LastResetDraft

open BB6.Agent28 BB6.Agent1UpperTail BB6.Agent47P1

/-- Necessary counting invariant of every *original* CountCone constructor.
    Draft source module: original-source Lean compilation is pending. -/
theorem counted_cost_at_least_twice_resets
    (b0 d0 b d m z : Nat)
    (h : CountCone b0 d0 b d m z) : 2*z ≤ m := by
  induction h with
  | root => omega
  | parent b d m z t k c hp hb hb4 hd hi hk hc ih =>
    by_cases ht : t = 0
    · have hw : 2*z ≤ m+1 := by omega
      simpa [ht] using hw
    · have htp : 1 ≤ t := by omega
      have hw : 2*(z+1) ≤ m+t+1 := by omega
      simpa [ht] using hw

/-- Last positive-depth inverse step, retaining the *same counted history*.
    In particular the prefix count is exactly z-1, even when an endpoint
    admits multiple separate inverse-word histories. -/
theorem counted_last_positive_reset
    (b0 d0 b d m z : Nat)
    (h : CountCone b0 d0 b d m z)
    (hz : 1 ≤ z) :
    ∃ bp dp mp zp t k c s,
      CountCone b0 d0 bp dp mp zp ∧
      z = zp+1 ∧
      8 ≤ bp ∧ bp%4=0 ∧ dp%2=1 ∧
      inverseAt bp dp t = some (k,c) ∧
      2 ≤ k ∧ c%2=1 ∧ 1 ≤ t ∧
      UpperTail (2*k-4) (c+4) (mp+t+1) b d m s := by
  induction h with
  | root => omega
  | parent b d m z t k c hp hb hb4 hd hi hk hc ih =>
    by_cases ht : t = 0
    · have hzpre : 1 ≤ z := by simpa [ht] using hz
      obtain ⟨bp,dp,mp,zp,tp,kp,cp,s,
        hpre,hcount,hbp,hbp4,hdp,hip,hkp,hcp,htp,htail⟩ := ih hzpre
      have htaily := UpperTail.step b d m s k c htail hb hb4 hd
        (by simpa [ht] using hi) hk hc
      refine ⟨bp,dp,mp,zp,tp,kp,cp,s+1,
        hpre,?_,hbp,hbp4,hdp,hip,hkp,hcp,htp,?_⟩
      · simpa [ht] using hcount
      · simpa [ht] using htaily
    · have htp : 1 ≤ t := by omega
      refine ⟨b,d,m,z,t,k,c,0,
        hp,?_,hb,hb4,hd,hi,hk,hc,htp,UpperTail.root⟩
      simp [ht]

/-- Immediate exact cost consequence of the counted last-reset factorization. -/
theorem counted_last_reset_has_cost
    (b0 d0 b d m z : Nat)
    (h : CountCone b0 d0 b d m z)
    (hz : 1 ≤ z) :
    ∃ bp dp mp zp t k c s,
      CountCone b0 d0 bp dp mp zp ∧ z=zp+1 ∧
      inverseAt bp dp t=some (k,c) ∧ 1≤t ∧
      UpperTail (2*k-4) (c+4) (mp+t+1) b d m s ∧
      2*z ≤ mp+t+1 := by
  obtain ⟨bp,dp,mp,zp,t,k,c,s,hpre,hzc,
    _,_,_,hi,_,_,ht,htail⟩ :=
      counted_last_positive_reset b0 d0 b d m z h hz
  have hprefix := counted_cost_at_least_twice_resets b0 d0 bp dp mp zp hpre
  refine ⟨bp,dp,mp,zp,t,k,c,s,hpre,hzc,hi,ht,htail,?_⟩
  omega

#print axioms BB6.Agent43LastResetDraft.counted_cost_at_least_twice_resets
#print axioms BB6.Agent43LastResetDraft.counted_last_positive_reset
#print axioms BB6.Agent43LastResetDraft.counted_last_reset_has_cost

end BB6.Agent43LastResetDraft
