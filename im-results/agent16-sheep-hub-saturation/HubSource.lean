import Hub
import EvenEdge

namespace SheepHubs

/-- A genuinely legal first-even return exists from an arbitrarily high source
in the congruence class of any generic source with sufficiently long odd block.
Every assertion is quantified and refers to the original SheepEven.EvenEdge
relation, rather than to a hand-written approximation of that relation. -/
theorem genuine_hub_to_even_edge (a L n u W N : Nat)
    (ha : 1 ≤ a) (hu : 5 ≤ u) (huodd : u%2=1) (hnodd : n%2=1)
    (heq : 2*(1+2^L*W)+1=(2^(a+1)+1)*u+2*a) :
    ∃ t : Nat,
      N≤t ∧
      SheepEven.EvenEdge
        (2^a*(u+2^(L+1)*n*t))
        (1+3^L*(W+(2^(a+1)+1)*n*t)) ∧
      2^(a+L+1) ∣ 1+3^L*(W+(2^(a+1)+1)*n*t) ∧
      2^a*(u+2^(L+1)*n*t)=2^a*u+2^(a+L+1)*n*t := by
  obtain ⟨t,ht,hVmin,hVodd,hQodd,hF,hdiv,hsrc⟩ :=
    generic_hub_literal_return a L n u W N hu huodd hnodd heq
  let V := u+2^(L+1)*n*t
  let Q := W+(2^(a+1)+1)*n*t
  have hs : SheepEven.Step (2^a*V) (2^a*V+a+(V-1)/2) := by
    exact SheepEven.Step.generic a V hVodd hVmin
  have hp : 0<(2:Nat)^a := Nat.pow_pos (by decide)
  have hz5 : 5≤2^a*V+a+(V-1)/2 := by
    have hbound : V≤2^a*V := Nat.le_mul_of_pos_left V hp
    omega
  have hedge : SheepEven.EvenEdge (2^a*V) (1+3^L*Q) := by
    refine ⟨1+2^L*Q,L,Q,?_,?_,hQodd,rfl,rfl⟩
    · rw [←hF]
      exact hs
    · rw [←hF]
      exact hz5
  exact ⟨t,ht,hedge,hdiv,hsrc⟩

#print axioms genuine_hub_to_even_edge
end SheepHubs
