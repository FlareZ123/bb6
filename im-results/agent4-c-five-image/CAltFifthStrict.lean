import CAltFifthSource
import ThreeConeProper
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Five
open BB6.Agent46

/-- Four authentic first-return edges can enter each target in the lattice. -/
theorem four_edges_exist (w t : Nat) (ht : 2≤t) :
    ∃ a0 b0 a1 b1 a2 b2 a3 b3,
      secNext (a0,b0)=some (a1,b1) ∧
      secNext (a1,b1)=some (a2,b2) ∧
      secNext (a2,b2)=some (a3,b3) ∧
      secNext (a3,b3)=some (64*w+25,64*t+14) := by
  let x := 64*w+25
  let y := 64*t+14
  let p := x+y-2
  let q := (y-2)/2
  let r := p+q-2
  let s := (q-2)/2
  have hlast : secNext (p,q)=some (x,y) :=
    BB6.Agent34ThreeProper.direct_predecessor x y (by omega) (by omega)
  have hpen : secNext (r,s)=some (p,q) := by
    dsimp [r,s]
    exact BB6.Agent34ThreeProper.direct_predecessor p q (by dsimp [q]; omega)
      (by dsimp [q]; omega)
  have hsector : ((r+s)%8=1 ∧ s%16=10) ∨
      ((r+s)%8=3 ∧ s%16=2) := by
    dsimp [r,s,p,q,x,y]
    right
    omega
  obtain ⟨⟨a,k,b,l,h0,h1⟩,_⟩ :=
    BB6.Agent34ThreeProper.exactly_two_not_three r s
      (by dsimp [r,s,p,q,x,y]; omega) hsector
  exact ⟨b,l,a,k,r,s,p,q,h0,h1,hpen,hlast⟩

/-- No fifth first-return edge sequence enters any target, from any source. -/
theorem five_edges_impossible
    (w t u v a b c d e f g h : Nat)
    (ht : 2≤t) (he : (w+t)%2=1)
    (h0 : secNext (u,v)=some (a,b))
    (h1 : secNext (a,b)=some (c,d))
    (h2 : secNext (c,d)=some (e,f))
    (h3 : secNext (e,f)=some (g,h))
    (h4 : secNext (g,h)=some (64*w+25,64*t+14)) : False := by
  have hInv : sectionPreimageAll g h (64*w+25) (64*t+14) :=
    (section_preimage_all_iff g h _ _).mp h4
  rcases two_parent_arithmetic g h w t hInv with hp | hh
  · have hP : secNext (e,f)=some (64*(w+t)+37,32*t+6) := by
      simpa [hp.1,hp.2] using h3
    have hpre : sectionPreimageAll e f _ _ :=
      (section_preimage_all_iff e f _ _).mp hP
    have hcopy : BB6.Agent34Broad.sectionPreimageAll e f _ _ := hpre
    obtain ⟨he0,hf0⟩ := BB6.Agent34Three.only_direct e f
      (64*(w+t)+37) (32*t+6)
      (by omega) (by omega) (Or.inr (by omega)) hcopy
    have heq : e=64*w+96*t+41 ∧ f=16*t+2 := by omega
    have hQ : secNext (c,d)=some (64*w+96*t+41,16*t+2) := by
      simpa [heq.1,heq.2] using h2
    have hsec : (((64*w+96*t+41)+(16*t+2))%8=1 ∧ (16*t+2)%16=10) ∨
      (((64*w+96*t+41)+(16*t+2))%8=3 ∧ (16*t+2)%16=2) := by
      right
      omega
    exact BB6.Agent34Three.no_three_edges
      u v a b c d (64*w+96*t+41) (16*t+2)
      (by omega) hsec h0 h1 hQ
  · have hH : secNext (e,f)=some (16*(w+t)+7,24*w+56*t+18) := by
      simpa [hh.1,hh.2] using h3
    have hpreH : sectionPreimageAll e f _ _ :=
      (section_preimage_all_iff e f _ _).mp hH
    obtain ⟨he0,hf0⟩ := BB6.Agent4Three.only_direct_mod4_one e f
      (16*(w+t)+7) (24*w+56*t+18)
      (by omega) (by omega) (by omega) hpreH
    have hD : secNext (c,d)=some (40*w+72*t+23,12*w+28*t+8) := by
      have heq : e=40*w+72*t+23 ∧ f=12*w+28*t+8 := by omega
      simpa [heq.1,heq.2] using h2
    have hpreD : sectionPreimageAll c d _ _ :=
      (section_preimage_all_iff c d _ _).mp hD
    have hcopy : BB6.Agent34Broad.sectionPreimageAll c d _ _ := hpreD
    obtain ⟨hc0,hd0⟩ := BB6.Agent34Three.only_direct c d
      (40*w+72*t+23) (12*w+28*t+8)
      (by omega) (by omega) (Or.inr (by omega)) hcopy
    have hE : secNext (a,b)=some (52*w+100*t+29,6*w+14*t+3) := by
      have heq : c=52*w+100*t+29 ∧ d=6*w+14*t+3 := by omega
      simpa [heq.1,heq.2] using h1
    have hp := BB6.Agent3.section_odd_image a b
      (52*w+100*t+29) (6*w+14*t+3) hE
      (by omega) (by omega)
    omega

/-- Exactly the fourth source image, outside the fifth, for all lattice points. -/
theorem exactly_four_not_five (w t : Nat)
    (ht : 2≤t) (he : (w+t)%2=1) :
    (∃ a0 b0 a1 b1 a2 b2 a3 b3,
      secNext (a0,b0)=some (a1,b1) ∧
      secNext (a1,b1)=some (a2,b2) ∧
      secNext (a2,b2)=some (a3,b3) ∧
      secNext (a3,b3)=some (64*w+25,64*t+14)) ∧
    (∀ u v a b c d e f g h,
      ¬ (secNext (u,v)=some (a,b) ∧
         secNext (a,b)=some (c,d) ∧
         secNext (c,d)=some (e,f) ∧
         secNext (e,f)=some (g,h) ∧
         secNext (g,h)=some (64*w+25,64*t+14))) := by
  refine ⟨four_edges_exist w t ht,?_⟩
  intro u v a b c d e f g h ⟨h0,h1,h2,h3,h4⟩
  exact five_edges_impossible w t u v a b c d e f g h ht he h0 h1 h2 h3 h4

#print axioms exactly_four_not_five
end BB6.Agent4Five
