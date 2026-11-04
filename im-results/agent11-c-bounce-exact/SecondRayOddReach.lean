import SecondRayOddCount
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Ray
open BB6.Agent46

def RayReach (p:Nat×Nat) : Prop :=
  ∃ n:Nat, BB6.Agent8Section.run secNext n (some (5,1))=some p

/-- A true target other than the seed is reached exactly when one of
    its incoming sources was reached a single section transition earlier. -/
theorem ray_reach_predecessor (q:Nat×Nat) (hne:q≠(5,1)) :
  RayReach q ↔ ∃ p, RayReach p ∧ secNext p=some q := by
  constructor
  · rintro ⟨n,hn⟩
    cases n with
    | zero =>
        have heq : q=(5,1) := by
          exact Option.some.inj (by simpa only [BB6.Agent8Section.run] using hn.symm)
        exact False.elim (hne heq)
    | succ n =>
        change (BB6.Agent8Section.run secNext n (some (5,1))).bind secNext=some q at hn
        cases hp:BB6.Agent8Section.run secNext n (some (5,1)) with
        | none => simp [hp] at hn
        | some p =>
            simp only [hp,Option.bind_some] at hn
            exact ⟨p,⟨n,hp⟩,hn⟩
  · rintro ⟨p,⟨n,hn⟩,hs⟩
    refine ⟨n+1,?_⟩
    change (BB6.Agent8Section.run secNext n (some (5,1))).bind secNext=some q
    rw [hn]
    exact hs

/-- Genuine blank-seed reachability of a second halting ray with odd m
    is equivalent to reachability of at least one member of its exact
    m+1-element source fibre. This holds for ALL times, with no cutoff. -/
theorem odd_ray_root_reduction (m:Nat) (hm:m%2=1) :
  RayReach (rayX m,rayY m) ↔
    ∃ i:Fin (m+1), RayReach (oddRayIndexed m i) := by
  have hnot : (rayX m,rayY m)≠(5,1) := by
    intro h
    have he : rayY m=1 := (Prod.mk.inj h).2
    have hlow := (rayFacts m).1
    omega
  rw [ray_reach_predecessor _ hnot]
  constructor
  · rintro ⟨⟨a,k⟩,hr,he⟩
    obtain ⟨i,hi⟩ := (oddRayIndexed_complete m a k hm).mp he
    refine ⟨i,?_⟩
    rw [hi]
    exact hr
  · rintro ⟨i,hr⟩
    refine ⟨oddRayIndexed m i,hr,?_⟩
    rcases hp : oddRayIndexed m i with ⟨a,k⟩
    exact (oddRayIndexed_complete m a k hm).mpr ⟨i,hp⟩

/-- Finite, source-exact immediate predecessor list; O(m) enumerated entries
    regardless of the exponential coordinate magnitude of the target. -/
def oddRayParentList (m:Nat) : List (Nat×Nat) :=
  List.ofFn (oddRayIndexed m)

theorem oddRayParentList_length (m:Nat) :
  (oddRayParentList m).length=m+1 := by
  exact List.length_ofFn

theorem oddRayParentList_exact (m a k:Nat) (hm:m%2=1) :
  (a,k)∈oddRayParentList m ↔ secNext (a,k)=some (rayX m,rayY m) := by
  rw [oddRayParentList,List.mem_ofFn]
  exact (oddRayIndexed_complete m a k hm).symm

#print axioms odd_ray_root_reduction
#print axioms oddRayParentList_exact
end BB6.Agent11Ray
