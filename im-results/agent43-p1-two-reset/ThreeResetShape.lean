import SourceInterfaces
namespace BB6.Agent43
open BB6.Agent28 BB6.Agent1Quarter BB6.Agent1UpperTail BB6.Agent47P1

/-- Faithful three-reset decomposition of the exact counted odd inverse cone,
    including unrestricted zero-depth (upper-tail) transitions. -/
theorem counted_cone_three_reset_shape
    (b0 d0 b d m z : Nat)
    (h : CountCone b0 d0 b d m z) (hz : z=3) :
    ∃ b1 d1 m1 r t1 k1 c1 b2 d2 m2 s t2 k2 c2
      b3 d3 m3 v t3 k3 c3 u,
      UpperTail b0 d0 0 b1 d1 m1 r ∧
      8≤b1 ∧ b1%4=0 ∧ d1%2=1 ∧
      BB6.Agent47P1.inverseAt b1 d1 t1 = some (k1,c1) ∧
      2≤k1 ∧ c1%2=1 ∧ 1≤t1 ∧
      UpperTail (2*k1-4) (c1+4) (m1+t1+1) b2 d2 m2 s ∧
      8≤b2 ∧ b2%4=0 ∧ d2%2=1 ∧
      BB6.Agent47P1.inverseAt b2 d2 t2 = some (k2,c2) ∧
      2≤k2 ∧ c2%2=1 ∧ 1≤t2 ∧
      UpperTail (2*k2-4) (c2+4) (m2+t2+1) b3 d3 m3 v ∧
      8≤b3 ∧ b3%4=0 ∧ d3%2=1 ∧
      BB6.Agent47P1.inverseAt b3 d3 t3 = some (k3,c3) ∧
      2≤k3 ∧ c3%2=1 ∧ 1≤t3 ∧
      UpperTail (2*k3-4) (c3+4) (m3+t3+1) b d m u := by
  induction h with
  | root => omega
  | parent b d m z t k c hp hb hb4 hd hi hk hc ih =>
    by_cases ht : t=0
    · have hzold : z=3 := by simp [ht] at hz; omega
      obtain ⟨b1,d1,m1,r,t1,k1,c1,b2,d2,m2,s,t2,k2,c2,
        b3,d3,m3,v,t3,k3,c3,u,
        hpre,hb1,hb14,hd1,hi1,hk1,hc1,ht1,hmiddle,
        hb2,hb24,hd2,hi2,hk2,hc2,ht2,hmiddle2,
        hb3,hb34,hd3,hi3,hk3,hc3,ht3,hpost⟩ := ih hzold
      have hpost' : UpperTail (2*k3-4) (c3+4) (m3+t3+1)
          (2*k-4) (c+4) (m+t+1) (u+1) := by
        have hs := UpperTail.step b d m u k c hpost hb hb4 hd
          (by simpa [ht] using hi) hk hc
        simpa [ht] using hs
      exact ⟨b1,d1,m1,r,t1,k1,c1,b2,d2,m2,s,t2,k2,c2,
        b3,d3,m3,v,t3,k3,c3,u+1,
        hpre,hb1,hb14,hd1,hi1,hk1,hc1,ht1,hmiddle,
        hb2,hb24,hd2,hi2,hk2,hc2,ht2,hmiddle2,
        hb3,hb34,hd3,hi3,hk3,hc3,ht3,hpost'⟩
    · have hzold : z=2 := by simp [ht] at hz; omega
      obtain ⟨b1,d1,m1,r,t1,k1,c1,b2,d2,m2,s,t2,k2,c2,v,
        hpre,hb1,hb14,hd1,hi1,hk1,hc1,ht1,hmiddle,
        hb2,hb24,hd2,hi2,hk2,hc2,ht2,hmiddle2⟩ :=
        counted_cone_two_reset_shape b0 d0 b d m z hp hzold
      have htpos : 1≤t := by omega
      exact ⟨b1,d1,m1,r,t1,k1,c1,b2,d2,m2,s,t2,k2,c2,
        b,d,m,v,t,k,c,0,
        hpre,hb1,hb14,hd1,hi1,hk1,hc1,ht1,hmiddle,
        hb2,hb24,hd2,hi2,hk2,hc2,ht2,hmiddle2,
        hb,hb4,hd,hi,hk,hc,htpos,UpperTail.root⟩

#print axioms BB6.Agent43.counted_cone_three_reset_shape
end BB6.Agent43
