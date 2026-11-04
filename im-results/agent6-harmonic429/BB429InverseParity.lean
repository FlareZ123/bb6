import BB429NewGate
import Lean.Elab.Tactic.Omega
namespace BB429InverseParity
set_option maxHeartbeats 6000000

/-- Every input to a sufficiently large halting feeder belongs to one of two
    exact affine families. This is an exhaustive inversion of BB429.next. -/
theorem feeder_parent_two (t x y : Nat) (ht : 7≤t)
    (hs : BB429.next (x,y)=some (2*t+1,12*t+14)) :
    (x=t-1 ∧ y=14*t+15) ∨
    (x=5*t-2 ∧ y=6*t+9) := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- On a genuine blank-origin path, the parity invariant rules out exactly
    one of the two possible parents of any sufficiently large halting feeder. -/
theorem rooted_feeder_parent_unique (n t : Nat) (ht : 7≤t)
    (hr : BB429.run (n+1) (0,0)=some (2*t+1,12*t+14)) :
    (t%2=0 ∧ ∃ p, BB429.run n (0,0)=some p ∧
       p=(t-1,14*t+15)) ∨
    (t%2=1 ∧ ∃ p, BB429.run n (0,0)=some p ∧
       p=(5*t-2,6*t+9)) := by
  simp only [BB429.run] at hr
  cases hp : BB429.run n (0,0) with
  | none => simp [hp] at hr
  | some p =>
    simp only [hp, Option.bind_some] at hr
    rcases feeder_parent_two t p.1 p.2 ht hr with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · have hpar : t%2=0 := by
        by_cases hzero : t%2=0
        · exact hzero
        · have hpos : 0<p.1 := by omega
          have he : p.1%2=0 := by omega
          have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos he
          omega
      left
      refine ⟨hpar,p,rfl,?_⟩
      exact Prod.ext hx hy
    · have hpar : t%2=1 := by
        by_cases hone : t%2=1
        · exact hone
        · have hpos : 0<p.1 := by omega
          have he : p.1%2=0 := by omega
          have hm := BB429NoThree.reachable_even_positive n p.1 p.2 hp hpos he
          omega
      right
      refine ⟨hpar,p,rfl,?_⟩
      exact Prod.ext hx hy

#print axioms feeder_parent_two
#print axioms rooted_feeder_parent_unique
end BB429InverseParity

namespace BB429InverseParity
set_option maxHeartbeats 7000000

/-- An inverse from a non-first branch into the one-step halting ray
    with seed u=1(mod4) necessarily has an even-positive odd-w parent. -/
theorem nonfirst_seed_one_modfour_parent (x y u : Nat)
    (hnot : y < 2*x+3)
    (hs : BB429.next (x,y)=some (u,6*u+8))
    (hm : u%4=1) :
    0<x ∧ x%2=0 ∧ y%2=1 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- No genuinely blank-reachable non-first step can enter a positive
    one-step halting seed whose first counter is 1 modulo4. -/
theorem no_rooted_nonfirst_seed_one_modfour (n x y u : Nat)
    (hr : BB429.run n (0,0)=some (x,y))
    (hnot : y<2*x+3)
    (hs : BB429.next (x,y)=some (u,6*u+8))
    (hm : u%4=1) : False := by
  obtain ⟨hpos,he,ho⟩ := nonfirst_seed_one_modfour_parent x y u hnot hs hm
  have hm2 := BB429NoThree.reachable_even_positive n x y hr hpos he
  omega

#print axioms nonfirst_seed_one_modfour_parent
#print axioms no_rooted_nonfirst_seed_one_modfour
end BB429InverseParity
