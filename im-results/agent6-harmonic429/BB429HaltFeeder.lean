import BB429NoThree
import Lean.Elab.Tactic.Omega

namespace BB429HaltFeeder

set_option maxHeartbeats 5000000 in
/-- Every successful transition to the (odd-second-counter) halting line
    is necessarily the first branch, with an exact affine preimage. -/
theorem every_halt_incoming_is_first (x y a b : Nat)
    (hs : BB429.next (x,y)=some (a,b))
    (hg : b+1=2*a) : a=2*x+3 ∧ y=6*x+8 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- A potentially halting transition on the genuine blank orbit has an
    odd first counter at its immediate predecessor. -/
theorem every_blank_halt_feeder_odd (n x y a b : Nat)
    (hp : BB429.run n (0,0)=some (x,y))
    (hs : BB429.next (x,y)=some (a,b))
    (hg : b+1=2*a) : x%2=1 := by
  obtain ⟨ha,hy⟩ := every_halt_incoming_is_first x y a b hs hg
  by_cases hzero : x=0
  · subst x
    have hbad : BB429.run n (0,0)=some (0,8) := by
      simpa [hy] using hp
    exact False.elim ((BB429NoThree.no_reach_zero_eight n) hbad)
  · have hx : 0<x := by omega
    by_cases he : x%2=0
    · have hm := BB429NoThree.reachable_even_positive n x y hp hx he
      omega
    · omega

/-- A true terminal site necessarily has first counter one modulo four. -/
theorem every_blank_halt_one_mod_four (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hn : BB429.next (a,b)=none) : a%4=1 := by
  cases n with
  | zero =>
    simp only [BB429.run, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl,rfl⟩ := hr
    simp [BB429.next] at hn
  | succ k =>
    simp only [BB429.run] at hr
    cases hp : BB429.run k (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp, Option.bind_some] at hr
      obtain ⟨he,hf⟩ := every_halt_incoming_is_first p.1 p.2 a b hr
        ((BB429.next_none_iff_halt_line a b).mp hn)
      have hodd := every_blank_halt_feeder_odd k p.1 p.2 a b hp hr
        ((BB429.next_none_iff_halt_line a b).mp hn)
      omega

#print axioms every_halt_incoming_is_first
#print axioms every_blank_halt_feeder_odd
#print axioms every_blank_halt_one_mod_four
end BB429HaltFeeder
