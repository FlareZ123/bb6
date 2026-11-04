import BB429Rank
import Lean.Elab.Tactic.Omega

namespace BB429NoThree

set_option maxHeartbeats 4000000

/-- Every successful transition entering a positive even first counter
    has second counter congruent to 2 modulo 4. -/
theorem positive_even_successor (u w a b : Nat)
    (hs : BB429.next (u,w) = some (a,b))
    (ha : 0 < a) (he : a%2=0) : b%4=2 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- A successful step entering the halting line at u=3 modulo 4 must
    originate from (x, 6*x+8), with x even. -/
theorem incoming_three_halt (x y a b : Nat)
    (hs : BB429.next (x,y)=some (a,b))
    (hg : b+1=2*a)
    (hm : a%4=3) : x%2=0 ∧ y=6*x+8 := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- The only zero-first-counter predecessor compatible with such
    a halting transition is excluded by the strictly increasing rank. -/
theorem no_reach_zero_eight (n : Nat) :
    BB429.run n (0,0) ≠ some (0,8) := by
  intro h
  cases n with
  | zero => simp [BB429.run] at h
  | succ k =>
    have h1 : BB429.run 1 (0,0)=some (0,12) := by decide
    have hc : BB429.run (k+1) (0,0) = BB429.run k (0,12) := by
      rw [show k+1=1+k by omega, BB429.run_add, h1]
      rfl
    rw [hc] at h
    have hr := (BB429.run_rank_bounds (0,12) (0,8) k h).1
    simp only [BB429.rank] at hr
    omega

theorem reachable_even_positive (n a b : Nat)
    (hs : BB429.run n (0,0)=some (a,b))
    (ha : 0 < a) (he : a%2=0) : b%4=2 := by
  cases n with
  | zero => simp [BB429.run] at hs; omega
  | succ k =>
    simp only [BB429.run] at hs
    cases hp : BB429.run k (0,0) with
    | none => simp [hp] at hs
    | some p =>
      simp only [hp, Option.bind_some] at hs
      exact positive_even_successor p.1 p.2 a b hs ha he

/-- Uniform all-time blank-root exclusion of the entire u=3 mod 4
    halting class, including the previously surviving u=3 mod 32. -/
theorem blank_halt_not_three_mod_four (n a b : Nat)
    (hreach : BB429.run n (0,0)=some (a,b))
    (hhalt : BB429.next (a,b)=none) : a%4 ≠ 3 := by
  intro hm
  have hl := (BB429.next_none_iff_halt_line a b).mp hhalt
  cases n with
  | zero => simp [BB429.run] at hreach; omega
  | succ k =>
    simp only [BB429.run] at hreach
    cases hp : BB429.run k (0,0) with
    | none => simp [hp] at hreach
    | some p =>
      simp only [hp, Option.bind_some] at hreach
      obtain ⟨he,hy⟩ := incoming_three_halt p.1 p.2 a b hreach hl hm
      by_cases hz : p.1 = 0
      · have hz8 : p.2=8 := by omega
        have hpeq : p=(0,8) := Prod.ext hz hz8
        have hbad : BB429.run k (0,0)=some (0,8) := by
          simpa [hpeq] using hp
        exact (no_reach_zero_eight k) hbad
      · have hpos : 0 < p.1 := by omega
        have hmod := reachable_even_positive k p.1 p.2 hp hpos he
        omega

#print axioms positive_even_successor
#print axioms incoming_three_halt
#print axioms blank_halt_not_three_mod_four
end BB429NoThree
