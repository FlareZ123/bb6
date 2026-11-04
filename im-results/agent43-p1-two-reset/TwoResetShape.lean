import OneResetCount

namespace BB6.Agent43
open BB6.Agent28 BB6.Agent1Quarter BB6.Agent1UpperTail BB6.Agent47P1

/-- Pure combinatorial decomposition of exactly two positive-depth inverse
    transitions, allowing arbitrary t=0 upper edges before/between/after. -/
theorem counted_cone_two_reset_shape
    (b0 d0 b d m z : Nat)
    (h : CountCone b0 d0 b d m z) (hz : z=2) :
    ∃ b1 d1 m1 r t1 k1 c1 b2 d2 m2 s t2 k2 c2 u,
      UpperTail b0 d0 0 b1 d1 m1 r ∧
      8≤b1 ∧ b1%4=0 ∧ d1%2=1 ∧
      inverseAt b1 d1 t1 = some (k1,c1) ∧
      2≤k1 ∧ c1%2=1 ∧ 1≤t1 ∧
      UpperTail (2*k1-4) (c1+4) (m1+t1+1) b2 d2 m2 s ∧
      8≤b2 ∧ b2%4=0 ∧ d2%2=1 ∧
      inverseAt b2 d2 t2 = some (k2,c2) ∧
      2≤k2 ∧ c2%2=1 ∧ 1≤t2 ∧
      UpperTail (2*k2-4) (c2+4) (m2+t2+1) b d m u := by
  induction h with
  | root => omega
  | parent b d m z t k c hp hb hb4 hd hi hk hc ih =>
    by_cases ht : t=0
    · have hzold : z=2 := by simp [ht] at hz; omega
      obtain ⟨b1,d1,m1,r,t1,k1,c1,b2,d2,m2,s,t2,k2,c2,u,
        hpre,hb1,hb14,hd1,hi1,hk1,hc1,ht1,hmiddle,
        hb2,hb24,hd2,hi2,hk2,hc2,ht2,hpost⟩ := ih hzold
      have hpost' : UpperTail (2*k2-4) (c2+4) (m2+t2+1)
          (2*k-4) (c+4) (m+t+1) (u+1) := by
        have hs := UpperTail.step b d m u k c hpost hb hb4 hd
          (by simpa [ht] using hi) hk hc
        simpa [ht] using hs
      exact ⟨b1,d1,m1,r,t1,k1,c1,b2,d2,m2,s,t2,k2,c2,u+1,
        hpre,hb1,hb14,hd1,hi1,hk1,hc1,ht1,hmiddle,
        hb2,hb24,hd2,hi2,hk2,hc2,ht2,hpost'⟩
    · have hzold : z=1 := by simp [ht] at hz; omega
      obtain ⟨b1,d1,m1,r,t1,k1,c1,s,
        hpre,hb1,hb14,hd1,hi1,hk1,hc1,ht1,hmiddle⟩ :=
        (cone_shape b0 d0 b d m z hp).2 hzold
      have htpos : 1≤t := by omega
      exact ⟨b1,d1,m1,r,t1,k1,c1,b,d,m,s,t,k,c,0,
        hpre,hb1,hb14,hd1,hi1,hk1,hc1,ht1,hmiddle,
        hb,hb4,hd,hi,hk,hc,htpos,UpperTail.root⟩

#print axioms BB6.Agent43.counted_cone_two_reset_shape
end BB6.Agent43
