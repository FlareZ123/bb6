import OneResetCount
import P1InverseNoMerge

set_option maxHeartbeats 2000000
namespace BB6.Agent27Finite
open BB6.Agent28 BB6.Agent1Quarter BB6.Agent47P1

/-- The original counted inverse history preserves exact additive mass. -/
theorem counted_mass (b0 d0 b d m z : Nat)
    (h : CountCone b0 d0 b d m z) :
    b+d+2*m=b0+d0 := by
  induction h with
  | root => omega
  | parent b d m z t k c hp hb hb4 hd hi hk hc ih =>
      have hs := inverseAt_odd_cost b d t k c (by omega) hb4 hd hi hc
      omega

/-- Unrestricted elimination of the last exact original-source inverse edge,
retaining every parent coordinate, index and counter annotation. -/
theorem counted_last (b0 d0 b d m z : Nat)
    (h : CountCone b0 d0 b d m z) :
    (b=b0 ∧ d=d0 ∧ m=0 ∧ z=0) ∨
    ∃ B D M Z t k c,
      CountCone b0 d0 B D M Z ∧
      8≤B ∧ B%4=0 ∧ D%2=1 ∧
      inverseAt B D t=some (k,c) ∧
      2≤k ∧ c%2=1 ∧
      b=2*k-4 ∧ d=c+4 ∧
      m=M+t+1 ∧ z=Z+(if t=0 then 0 else 1) := by
  cases h with
  | root => exact Or.inl ⟨rfl,rfl,rfl,rfl⟩
  | parent B D M Z t k c hp hb hb4 hd hi hk hc =>
      exact Or.inr ⟨B,D,M,Z,t,k,c,hp,hb,hb4,hd,hi,hk,hc,
        rfl,rfl,rfl,rfl⟩

/-- A genuine original-source CountCone endpoint determines a unique total
cost and positive-depth reset count. No inverse-history cutoff is assumed. -/
theorem count_annotation_unique (b0 d0 b d m z : Nat)
    (h : CountCone b0 d0 b d m z) :
    ∀ m' z', CountCone b0 d0 b d m' z' → m=m' ∧ z=z' := by
  induction h with
  | root =>
      intro m' z' h'
      rcases counted_last _ _ _ _ _ _ h' with hroot | hstep
      · rcases hroot with ⟨_,_,hm,hz⟩
        exact ⟨hm.symm,hz.symm⟩
      · obtain ⟨B,D,M,Z,t,k,c,hp,hb,hb4,hd,hi,hk,hc,
          hB,hD,hM,hZ⟩ := hstep
        have hm := counted_mass _ _ B D M Z hp
        have hs := inverseAt_odd_cost B D t k c (by omega) hb4 hd hi hc
        omega
  | parent b d m z t k c hp hb hb4 hd hi hk hc ih =>
      intro m' z' h'
      rcases counted_last _ _ _ _ _ _ h' with hroot | hstep
      · rcases hroot with ⟨hB,hD,hM,hZ⟩
        have hm := counted_mass _ _ b d m z hp
        have hs := inverseAt_odd_cost b d t k c (by omega) hb4 hd hi hc
        omega
      · obtain ⟨B,D,M,Z,t',k',c',hp',hb',hb4',hd',hi',hk',hc',
          hB,hD,hM,hZ⟩ := hstep
        have hchild : (2*k-4,c+4)=(2*k'-4,c'+4) := by
          apply Prod.ext <;> omega
        obtain ⟨hbeq,hdeq,hteq⟩ :=
          unique_inverse_edge b d t k c B D t' k' c' hi hi' hk hk' hchild
        rw [← hbeq, ← hdeq] at hp'
        have hprev := ih M Z hp'
        rcases hprev with ⟨hmeq,hzeq⟩
        omega

#print axioms counted_mass
#print axioms counted_last
#print axioms count_annotation_unique
end BB6.Agent27Finite
