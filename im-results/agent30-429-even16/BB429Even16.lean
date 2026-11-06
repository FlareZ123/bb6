import BB429RootEven8
import BB429NoThree
import Lean.Elab.Tactic.Omega

namespace BB429Even16
set_option maxHeartbeats 8000000

/-- An incoming reset to first coordinate zero has second coordinate at
least ten, independent of the previous state. -/
theorem incoming_zero_min_ten (u w b : Nat)
    (hs : BB429.next (u,w) = some (0,b)) : 10 ≤ b := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

theorem rooted_zero_min_ten (n b : Nat)
    (hr : BB429.run n (0,0) = some (0,b)) : b=0 ∨ 10 ≤ b := by
  cases n with
  | zero => simp [BB429.run] at hr; omega
  | succ k =>
    simp only [BB429.run] at hr
    cases hp : BB429.run k (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp, Option.bind_some] at hr
      exact Or.inr (incoming_zero_min_ten p.1 p.2 b hr)

/-- This output congruence forces the first branch and a positive-even
or zero first-coordinate parent with even second coordinate. -/
theorem incoming_odd_three_one (u w a b : Nat)
    (hs : BB429.next (u,w) = some (a,b))
    (ha : a%4=3) (hb : b%4=1) :
    a=2*u+3 ∧ w=a+b ∧ u%2=0 ∧ w%4=0 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- All-time, actual-blank-root restriction. Unlike a finite modular
invariant, this forces the first counter to the fixed value three. -/
theorem rooted_odd_three_one (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (ha : a%4=3) (hb : b%4=1) : a=3 ∧ 9≤b := by
  cases n with
  | zero => simp [BB429.run] at hr; omega
  | succ k =>
    simp only [BB429.run] at hr
    cases hp : BB429.run k (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp, Option.bind_some] at hr
      obtain ⟨ha',hw',he',hmod'⟩ :=
        incoming_odd_three_one p.1 p.2 a b hr ha hb
      by_cases hz : p.1=0
      · have hzero : BB429.run k (0,0)=some (0,a+b) := by
          have hp':p=(0,a+b) := Prod.ext hz hw'
          simpa [hp'] using hp
        have hmin := rooted_zero_min_ten k (a+b) hzero
        constructor <;> omega
      · have hpos : 0<p.1 := by omega
        have hmod :=
          BB429NoThree.reachable_even_positive k p.1 p.2 hp hpos he'
        omega

/-- New incoming positive-even modulo-16 rule, under the previously known
genuine-root positive-even modulo-eight invariant and rooted three-one rule. -/
theorem incoming_even_sixteen (u w a b : Nat)
    (hs : BB429.next (u,w)=some (a,b))
    (ha : 0<a) (he : a%2=0)
    (hparent_even : 0<u → u%2=0 → w%8=2)
    (hparent_odd : u%4=3 → w%4=1 → u=3 ∧ 9≤w) :
    (a%4=0 → b%16=2) ∧ (a%4=2 → b%16=10) := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals (by_cases hu : 0<u <;> by_cases he2 : u%2=0 <;>
    (try have hw := hparent_even hu he2) <;>
    (by_cases hu3 : u%4=3 <;> by_cases hw1 : w%4=1 <;>
       (try have hx := hparent_odd hu3 hw1) <;> omega))

/-- An all-time source-accurate refinement from modulo 8 to modulo 16. -/
theorem rooted_even_sixteen (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (ha : 0<a) (he : a%2=0) :
    (a%4=0 → b%16=2) ∧ (a%4=2 → b%16=10) := by
  cases n with
  | zero => simp [BB429.run] at hr; omega
  | succ k =>
    simp only [BB429.run] at hr
    cases hp : BB429.run k (0,0) with
    | none => simp [hp] at hr
    | some p =>
      simp only [hp, Option.bind_some] at hr
      exact incoming_even_sixteen p.1 p.2 a b hr ha he
        (fun hu he2 =>
          BB429RootEven8.rooted_positive_even_eight k p.1 p.2 hp hu he2)
        (fun hu3 hw1 => rooted_odd_three_one k p.1 p.2 hp hu3 hw1)

#print axioms rooted_odd_three_one
#print axioms rooted_even_sixteen
end BB429Even16
