import GDepth

namespace BB6.Agent19.FourDepth
open BB6.P1Reduction (GAncestor)

/-- Four exact inverse layers of the independent P1 recursive G drain. -/
def FourShape (b d k c : Nat) : Prop :=
  ∃ K, b=4*K+4 ∧
    ((k=K ∧ c=d+2*K+2) ∨
     (2*c+3=d+2*K+2 ∧ k=K+c/2+1) ∨
     (2*(2*c+3)+3=d+2*K+2 ∧
       k=K+(2*c+3)/2+1+c/2+1) ∨
     (2*(2*(2*c+3)+3)+3=d+2*K+2 ∧
       k=K+(2*(2*c+3)+3)/2+1+(2*c+3)/2+1+c/2+1))

theorem ancestor_four_shapes (b d k c : Nat) (h:GAncestor b d k c) :
    (d+b/2+3)%16=8 → FourShape b d k c := by
  induction h with
  | upper k d =>
    intro hm
    refine ⟨k,rfl,Or.inl ⟨rfl,rfl⟩⟩
  | nest b d k c hh ih =>
    intro hm
    obtain ⟨K,hb,hs⟩ := ih hm
    refine ⟨K,hb,?_⟩
    rcases hs with ⟨hk,hc⟩ | ⟨hc,hk⟩ | ⟨hc,hk⟩ | ⟨hc,hk⟩
    · right; left; exact ⟨hc,by omega⟩
    · right; right; left; exact ⟨hc,by omega⟩
    · right; right; right; exact ⟨hc,by omega⟩
    · exfalso
      omega

theorem four_shape_sound (b d k c:Nat) (hshape:FourShape b d k c) :
    BB6.P1Reduction.G k c=(b,d) := by
  obtain ⟨K,hb,hs⟩ := hshape
  rcases hs with ⟨hk,hc⟩ | ⟨hc,hk⟩ | ⟨hc,hk⟩ | ⟨hc,hk⟩
  · have hanc : GAncestor (4*K+4) d K (d+2*K+2) := GAncestor.upper K d
    have h0 := BB6.P1Reduction.GAncestor_sound _ _ _ _ hanc
    simpa [hb,hk,hc] using h0
  · have hup : GAncestor (4*K+4) d K (2*c+3) := by
      simpa [hc] using (GAncestor.upper K d)
    have hanc : GAncestor (4*K+4) d (K+c/2+1) c :=
      GAncestor.nest (4*K+4) d K c hup
    have h0 := BB6.P1Reduction.GAncestor_sound _ _ _ _ hanc
    simpa [hb,hk] using h0
  · have hup : GAncestor (4*K+4) d K (2*(2*c+3)+3) := by
      simpa [hc] using (GAncestor.upper K d)
    have hone : GAncestor (4*K+4) d (K+(2*c+3)/2+1) (2*c+3) :=
      GAncestor.nest (4*K+4) d K (2*c+3) hup
    have hanc : GAncestor (4*K+4) d (K+(2*c+3)/2+1+c/2+1) c :=
      GAncestor.nest (4*K+4) d (K+(2*c+3)/2+1) c hone
    have h0 := BB6.P1Reduction.GAncestor_sound _ _ _ _ hanc
    simpa [hb,hk] using h0
  · have hup : GAncestor (4*K+4) d K (2*(2*(2*c+3)+3)+3) := by
      simpa [hc] using (GAncestor.upper K d)
    have hone : GAncestor (4*K+4) d (K+(2*(2*c+3)+3)/2+1) (2*(2*c+3)+3) :=
      GAncestor.nest (4*K+4) d K (2*(2*c+3)+3) hup
    have htwo : GAncestor (4*K+4) d (K+(2*(2*c+3)+3)/2+1+(2*c+3)/2+1) (2*c+3) :=
      GAncestor.nest (4*K+4) d (K+(2*(2*c+3)+3)/2+1) (2*c+3) hone
    have hanc : GAncestor (4*K+4) d (K+(2*(2*c+3)+3)/2+1+(2*c+3)/2+1+c/2+1) c :=
      GAncestor.nest (4*K+4) d (K+(2*(2*c+3)+3)/2+1+(2*c+3)/2+1) c htwo
    have h0 := BB6.P1Reduction.GAncestor_sound _ _ _ _ hanc
    simpa [hb,hk] using h0

/-- A complete four-branch inverse iff when the shifted G weight is 8 mod16. -/
theorem G_four_preimages (b d k c:Nat) (hb:0<b)
    (hm:(d+b/2+3)%16=8) :
    BB6.HaltingFunnel.G k c=(b,d) ↔ FourShape b d k c := by
  constructor
  · intro h
    have hr : BB6.P1Reduction.G k c=(b,d) := by
      rw [BB6.Agent19.Depth.G_agree k c]
      exact h
    exact ancestor_four_shapes b d k c
      (BB6.P1Reduction.GAncestor_complete k c b d hr hb) hm
  · intro h
    have hr:= four_shape_sound b d k c h
    rw [BB6.Agent19.Depth.G_agree k c] at hr
    exact hr

#print axioms G_four_preimages
#print axioms ancestor_four_shapes
#print axioms four_shape_sound
end BB6.Agent19.FourDepth
