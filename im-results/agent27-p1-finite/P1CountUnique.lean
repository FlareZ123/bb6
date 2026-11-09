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

/-- The reset-count annotation, like the total inverse cost, is uniquely
determined by the endpoint of a genuine original-source CountCone. -/
theorem count_annotation_unique (b0 d0 b d m z : Nat)
    (h : CountCone b0 d0 b d m z) :
    ∀ m' z', CountCone b0 d0 b d m' z' → m=m' ∧ z=z' := by
  induction h with
  | root =>
      intro m' z' h'
      cases h' with
      | root => exact ⟨rfl,rfl⟩
      | parent b d m z t k c hp hb hb4 hd hi hk hc =>
          have hm := counted_mass b0 d0 b d m z hp
          have hs := inverseAt_odd_cost b d t k c (by omega) hb4 hd hi hc
          omega
  | parent b d m z t k c hp hb hb4 hd hi hk hc ih =>
      intro m' z' h'
      cases h' with
      | root =>
          have hm := counted_mass b0 d0 b d m z hp
          have hs := inverseAt_odd_cost b d t k c (by omega) hb4 hd hi hc
          omega
      | parent b' d' m' z' t' k' c' hp' hb' hb4' hd' hi' hk' hc' =>
          have hchild : (2*k-4,c+4)=(2*k'-4,c'+4) := by
            rfl
          obtain ⟨hbeq,hdeq,hteq⟩ :=
            unique_inverse_edge b d t k c b' d' t' k' c' hi hi' hk hk' hchild
          subst b'
          subst d'
          subst t'
          obtain ⟨hmeq,hzeq⟩ := ih m' z' hp'
          constructor
          · omega
          · omega

#print axioms counted_mass
#print axioms count_annotation_unique
end BB6.Agent27Finite
