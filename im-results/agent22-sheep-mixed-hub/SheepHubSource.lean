module
public import SheepSourceBridge
public import SheepMixedHub

@[expose] public section
namespace BB6.Agent22.SheepHubSource

/-- These are authentic one-step returns of the original Cryptids-certified
Sheep section map; the source states are not assumed blank-reachable. -/
theorem zero_hub_source (p q s : Nat) (hp : 1 ≤ p)
    (hq : 0 < q) (hqodd : q%2=1)
    (hs : s < 2^p * q) (he : s%2=0) :
    ∃ x y : Nat, x % (2^p*q) = 0 ∧
      y % (2^p*q) = s ∧ x%2=0 ∧ y%2=0 ∧ SheepBridge.SectionNext x y := by
  obtain ⟨x,y,hx,hy,hxe,hye,hg⟩ :=
    BB6.SheepMixedHub.zero_hub_any_odd p q s hp hq hqodd hs he
  refine ⟨x,y,hx,hy,hxe,hye,?_⟩
  cases hg with
  | ofOdd a u hodd hu => exact SheepBridge.SectionNext.general a u hu hodd

#print axioms zero_hub_source
end BB6.Agent22.SheepHubSource
