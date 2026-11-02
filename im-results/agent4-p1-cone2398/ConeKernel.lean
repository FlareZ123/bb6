import P1ResidualReach

namespace BB6.Agent4Cone
open BB6.P1Reduction

/-- Finite proof trees for absolute blank-reachability exclusions. Every
constructor is justified by a source-proved global invariant; a feeder must
block every positive G input and the exceptional c=1 input. -/
inductive Blocked : Nat → Nat → Prop where
  | modLeaf (a c : Nat)
      (heven : a%2=0) (hpos : 0<c) (hlarge : 2<a) (hmod : a%4=2) :
      Blocked a c
  | powerLeaf (a c : Nat)
      (heven : a%2=0) (hpos : 0<c) (hceven : c%2=0)
      (hgap : ∀ j : Nat, a+12≠14*2^j) :
      Blocked a c
  | feeder (b d : Nat)
      (hb : 8≤b) (hmod : b%4=0) (hpos : 0<d)
      (hno : ∀ k, ¬GAncestor b d k 1)
      (hchildren : ∀ k v, GAncestor b d k v → 2≤v →
        Blocked (2*k-4) (v+4)) :
      Blocked b d

/-- Kernel-checked universal soundness of a finite inverse-cone proof object.
The inductive type ensures that a certificate has finite proof depth. -/
theorem blocked_no_reach (b d : Nat) (h : Blocked b d) :
    ¬BB6.Agent1.Reach b d := by
  induction h with
  | modLeaf a c heven hpos hlarge hmod =>
    intro hr
    have hm := BB6.Agent1.reachable_even_mod4 a c hr hpos heven
    rcases hm with hh | hh <;> omega
  | powerLeaf a c heven hpos hceven hgap =>
    intro hr
    obtain ⟨j,hj⟩ := BB6.Agent1.even_left_power_shape a c hr heven hpos hceven
    exact hgap j hj
  | feeder b d hb hmod hpos hno hchildren ih =>
    intro hr
    obtain ⟨k,v,hanc,hv,hreach⟩ := BB6.Agent50P1.positive_G_feeder
      b d hb hmod hpos hno hr
    exact (ih k v hanc hv) hreach

#print axioms BB6.Agent4Cone.blocked_no_reach
end BB6.Agent4Cone
