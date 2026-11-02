import RankC
import PotentialCore

namespace BB6Rank
open Agent8Potential

theorem nextC_potential_step {s s' : Nat × Nat × Nat}
    (h : nextC s = some s') :
    potential (rankC s) s.1 + 2 ≤ potential (rankC s') s'.1 := by
  apply potential_step (rankC s) (rankC s') s.1 s'.1
  · rcases s with ⟨a, k, c⟩
    simp only [rankC]
    omega
  · rcases s' with ⟨a, k, c⟩
    simp only [rankC]
    omega
  · exact nextC_lex_progress h

theorem nextC_potential_growth (n : Nat) (s s' : Nat × Nat × Nat)
    (h : runSteps nextC n s = some s') :
    potential (rankC s) s.1 + 2*n ≤ potential (rankC s') s'.1 := by
  induction n generalizing s' with
  | zero =>
      simp only [runSteps, Option.some.injEq] at h
      subst s'
      omega
  | succ n ih =>
      cases hm : runSteps nextC n s with
      | none => simp [runSteps, hm] at h
      | some mid =>
          simp only [runSteps, hm, Option.bind_some] at h
          have h1 := ih mid hm
          have h2 := nextC_potential_step h
          omega

theorem nextC_critical_time_bound {n j : Nat}
    (h : runSteps nextC n (5,0,1) = some (0,2*j,5)) :
    44 + 2*n ≤ (4*j+5)*(4*j+8) := by
  have h1 := nextC_potential_growth n (5,0,1) (0,2*j,5) h
  have hstart : potential (rankC (5,0,1)) 5 = 44 := by decide
  have hend : potential (rankC (0,2*j,5)) 0 = (4*j+5)*(4*j+8) := by
    simp only [potential, rankC]
    have hr : (0 + 2 * (2*j) + 5) = 4*j+5 := by omega
    rw [hr]
    simp only [Nat.sub_zero, Nat.mul_add, Nat.add_mul, Nat.mul_one]
    omega
  rw [hstart, hend] at h1
  exact h1

#print axioms nextC_potential_step
#print axioms nextC_critical_time_bound
end BB6Rank
