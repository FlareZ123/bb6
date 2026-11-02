import PosEvenForm

namespace BB6.P1Rank
open BB6.Agent1

/-- The accelerated drain G increases the additive rank 2*k+c by at least two. -/
theorem G_sum_growth (k c : Nat) :
    2*k+c+2 ≤ (G k c).1+(G k c).2 := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases h : c < 2*k
    · rw [G]
      simp only [h, dite_true]
      have hs := ih (k-(c/2+1)) (by omega) (2*c+3)
      omega
    · by_cases hm : c ≤ 2*k+1
      · rw [G]
        simp [h,hm]
        omega
      · rw [G]
        simp [h,hm]
        omega

/-- At the special c=3 input, G(k,1) grows enough for strict rank progress. -/
theorem G_one_growth (k : Nat) :
    2*k+4 < (G k 1).1+(G k 1).2 := by
  by_cases hk : k=0
  · subst k
    simp [G]
  · have hlo : 1 < 2*k := by omega
    have hG : G k 1 = G (k-1) 5 := by
      rw [G]
      simp [hlo]
    rw [hG]
    have hs := G_sum_growth (k-1) 5
    omega

/-- Every defined step of the original Agent1 accelerated P1 map
    strictly increases a+c. This is independent of halting status. -/
theorem T_sum_growth (a c b d : Nat) (h : T a c = some (b,d)) :
    a+c < b+d := by
  unfold T at h
  by_cases hz : c=0
  · simp [hz] at h
    omega
  · by_cases ho : c=1
    · simp [hz,ho] at h
      omega
    · by_cases he : a%2=0
      · simp [hz,ho,he] at h
        omega
      · by_cases ht : c=2
        · simp [hz,ho,he,ht] at h
        · by_cases hthree : c=3
          · simp [hz,ho,he,ht,hthree] at h
            have hs := G_one_growth (a/2)
            have heq : G (a/2) 1 = (b,d) := by simpa using h
            rw [heq] at hs
            simp only [Prod.fst,Prod.snd] at hs
            omega
          · simp [hz,ho,he,ht,hthree] at h
            have hs := G_sum_growth (a/2+1) (c-2)
            have heq : G (a/2+1) (c-2) = (b,d) := by simpa using h
            rw [heq] at hs
            simp only [Prod.fst,Prod.snd] at hs
            omega

inductive Iter : Nat → Nat → Nat → Nat → Nat → Prop where
  | refl (a c : Nat) : Iter 0 a c a c
  | step (n a c b d e f : Nat) :
      Iter n a c b d → T b d = some (e,f) → Iter (n+1) a c e f

/-- Every reachable accelerated state has total rank at least the blank
    entry rank 3. -/
theorem reach_rank_lower (a c:Nat) (hr:Reach a c) : 3≤a+c := by
  induction hr with
  | init => omega
  | next a c b d hpre ht ih =>
    have hg := T_sum_growth a c b d ht
    omega

/-- Completeness bound for any fixed target: a state (a,c) of rank R
    can only be reached from blank in at most R-3 accelerated steps. -/
theorem reach_bounded_trace (a c:Nat) (hr:Reach a c) :
    ∃ n, Iter n 2 1 a c ∧ n+3≤a+c := by
  induction hr with
  | init =>
      exact ⟨0,Iter.refl 2 1,by omega⟩
  | next a c b d hr ht ih =>
      obtain ⟨n,hn,hbound⟩ := ih
      have hg := T_sum_growth a c b d ht
      refine ⟨n+1,Iter.step n 2 1 a c b d hn ht,?_⟩
      omega

#print axioms BB6.P1Rank.G_sum_growth
#print axioms BB6.P1Rank.G_one_growth
#print axioms BB6.P1Rank.T_sum_growth
#print axioms BB6.P1Rank.reach_rank_lower
#print axioms BB6.P1Rank.reach_bounded_trace
end BB6.P1Rank
