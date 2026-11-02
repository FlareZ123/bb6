import GDepth

namespace BB6.Agent19.TwoDepth
open BB6.P1Reduction (GAncestor)

/-- Complete inverse fiber with shifted weight congruent 2 modulo 4. -/
def TwoShape (b d k c:Nat):Prop :=
 ∃ K,b=4*K+4 ∧ ((k=K ∧ c=d+2*K+2) ∨
  (2*c+3=d+2*K+2 ∧ k=K+c/2+1))

theorem ancestor_two_shapes (b d k c:Nat)(h:GAncestor b d k c):
 (d+b/2+3)%4=2 → TwoShape b d k c := by
 induction h with
 | upper k d => intro hm; exact ⟨k,rfl,Or.inl ⟨rfl,rfl⟩⟩
 | nest b d k c h ih =>
   intro hm
   obtain ⟨K,hb,hs⟩:=ih hm
   refine ⟨K,hb,?_⟩
   rcases hs with ⟨hk,hc⟩ | ⟨hc,hk⟩
   · right; exact ⟨hc,by omega⟩
   · exfalso;omega

theorem two_shape_sound (b d k c:Nat)(hshape:TwoShape b d k c):
    BB6.P1Reduction.G k c=(b,d) := by
 obtain ⟨K,hb,hs⟩:=hshape
 rcases hs with ⟨hk,hc⟩ | ⟨hc,hk⟩
 · have h:=BB6.P1Reduction.GAncestor_sound _ _ _ _ (GAncestor.upper K d)
   simpa [hb,hk,hc] using h
 · have hu:GAncestor (4*K+4) d K (2*c+3) := by
     simpa [hc] using (GAncestor.upper K d)
   have h:=BB6.P1Reduction.GAncestor_sound _ _ _ _ (GAncestor.nest (4*K+4) d K c hu)
   simpa [hb,hk] using h

theorem G_two_preimages (b d k c:Nat) (hb:0<b)
 (hm:(d+b/2+3)%4=2) :
    BB6.HaltingFunnel.G k c=(b,d) ↔ TwoShape b d k c := by
 constructor
 · intro h
   have hr:BB6.P1Reduction.G k c=(b,d) := by
     rw [BB6.Agent19.Depth.G_agree k c]
     exact h
   exact ancestor_two_shapes b d k c
     (BB6.P1Reduction.GAncestor_complete k c b d hr hb) hm
 · intro h
   have hr:=two_shape_sound b d k c h
   rw [BB6.Agent19.Depth.G_agree k c] at hr
   exact hr

#print axioms G_two_preimages
end BB6.Agent19.TwoDepth
