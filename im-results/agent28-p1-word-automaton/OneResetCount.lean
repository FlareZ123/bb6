import OneResetZero

namespace BB6.Agent28
open BB6.Agent1Quarter BB6.Agent1UpperTail BB6.Agent47P1

/-- Annotated original-source odd inverse histories counting true t≥1 resets. -/
inductive CountCone (b0 d0 : Nat) : Nat → Nat → Nat → Nat → Prop where
  | root : CountCone b0 d0 b0 d0 0 0
  | parent (b d m z t k c : Nat)
      (hprev : CountCone b0 d0 b d m z)
      (hb : 8≤b) (hb4 : b%4=0) (hd : d%2=1)
      (hi : inverseAt b d t = some (k,c))
      (hk : 2≤k) (hc : c%2=1) :
      CountCone b0 d0 (2*k-4) (c+4) (m+t+1)
        (z + if t=0 then 0 else 1)

theorem odd_cone_has_count (b0 d0 b d m : Nat)
    (h : OddCone b0 d0 b d m) :
    ∃ z, CountCone b0 d0 b d m z := by
  induction h with
  | root => exact ⟨0, CountCone.root⟩
  | parent b d m t k c hp hb hb4 hd hi hk hc ih =>
      obtain ⟨z,hz⟩ := ih
      exact ⟨z + if t=0 then 0 else 1,
        CountCone.parent b d m z t k c hz hb hb4 hd hi hk hc⟩

/-- Faithful zero/one reset decomposition. -/
theorem cone_shape (b0 d0 b d m z : Nat)
    (h:CountCone b0 d0 b d m z) :
    (z=0 → ∃ n, UpperTail b0 d0 0 b d m n) ∧
    (z=1 → ∃ bp dp mp r t k c n,
      UpperTail b0 d0 0 bp dp mp r ∧
      8≤bp ∧ bp%4=0 ∧ dp%2=1 ∧
      inverseAt bp dp t = some (k,c) ∧
      2≤k ∧ c%2=1 ∧ 1≤t ∧
      UpperTail (2*k-4) (c+4) (mp+t+1) b d m n) := by
  induction h with
  | root =>
    constructor
    · intro _
      exact ⟨0,UpperTail.root⟩
    · intro hz
      omega
  | parent b d m z t k c hp hb hb4 hd hi hk hc ih =>
    constructor
    · intro hz0
      have ht : t=0 := by
        by_cases h0:t=0
        · exact h0
        · simp [h0] at hz0
      have hz : z=0 := by simpa [ht] using hz0
      obtain ⟨r,hu⟩ := ih.1 hz
      have hs := UpperTail.step b d m r k c hu hb hb4 hd (by simpa [ht] using hi) hk hc
      exact ⟨r+1, by simpa only [ht,Nat.zero_add] using hs⟩
    · intro hz1
      by_cases ht : t=0
      · have hz : z=1 := by simpa [ht] using hz1
        obtain ⟨bp,dp,mp,r,tp,kp,cp,s,hpre,hbp,hbp4,hdp,hip,hkp,hcp,htp,hpost⟩ := ih.2 hz
        have hs := UpperTail.step b d m s k c hpost hb hb4 hd (by simpa [ht] using hi) hk hc
        exact ⟨bp,dp,mp,r,tp,kp,cp,s+1,hpre,hbp,hbp4,hdp,hip,hkp,hcp,htp,
          by simpa only [ht,Nat.zero_add] using hs⟩
      · have htpos : 1≤t := by omega
        have hz : z=0 := by simp [ht] at hz1; omega
        obtain ⟨r,hpre⟩ := ih.1 hz
        exact ⟨b,d,m,r,t,k,c,0,hpre,hb,hb4,hd,hi,hk,hc,htpos,UpperTail.root⟩

/-- Source-true quantified restriction for all critical n≥30: every finite
    odd inverse history on the low-cost affine wall needs at least two resets. -/
theorem source_critical_wall_needs_two_resets
    (n b d m : Nat) (hn:30≤n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hwall : b=4*(m+n)) :
    ∃ z, CountCone (14*2^n-2*n-16) 3 b d m z ∧ 2≤z := by
  obtain ⟨z,hz⟩ := odd_cone_has_count _ _ b d m hcone
  refine ⟨z,hz,?_⟩
  by_cases hzbig : 2≤z
  · exact hzbig
  have hz01 : z=0 ∨ z=1 := by omega
  have hs := cone_shape _ _ b d m z hz
  rcases hz01 with h0 | h1
  · obtain ⟨r,hu⟩ := hs.1 h0
    exact False.elim (source_critical_zero_reset_no_wall n b d m r hn hu hwall)
  · obtain ⟨bp,dp,mp,r,t,k,c,s,hu,hbp,hbp4,hdp,hi,hk,hc,ht,hpost⟩ := hs.2 h1
    exact False.elim (source_critical_one_reset_no_wall n bp dp mp r t k c b d m s
      hn ht hu hbp hbp4 hdp hi hk hc hpost hcone hwall)

#print axioms BB6.Agent28.source_critical_wall_needs_two_resets
end BB6.Agent28
