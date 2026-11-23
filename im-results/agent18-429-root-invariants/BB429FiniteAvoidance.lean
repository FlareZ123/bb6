import BB429Rank
import Lean.Elab.Tactic.Omega

/-!
# Sound finite prefix exclusion for #429's strictly increasing rank

A Boolean single-path avoidance checker is proved sound for arbitrary
targets and horizons. If the verified path reaches a rank above a
target's rank, the rank monotonicity theorem excludes that target
globally, not merely up to the simulated time. No native_decide.
-/
namespace BB429FiniteAvoidance
set_option maxHeartbeats 20000000
set_option maxRecDepth 30000
open BB429

def avoid (target : State) : Nat → State → Bool
  | 0, s => decide (s ≠ target)
  | k+1, s =>
    decide (s ≠ target) &&
      match next s with
      | none => true
      | some t => avoid target k t

theorem avoid_sound (target : State) (k : Nat)
    (s : State) (h : avoid target k s = true)
    (n : Nat) (hn : n≤k) :
    run n s ≠ some target := by
  induction k generalizing s n with
  | zero =>
      have hz : n=0 := by omega
      subst n
      have hs : s≠target := by simpa [avoid] using h
      simpa [run] using hs
  | succ k ih =>
      have hh : (s≠target) ∧
          (match next s with
          | none => true
          | some t => avoid target k t) = true := by
        simpa [avoid] using h
      cases n with
      | zero =>
          simpa [run] using hh.1
      | succ n =>
          have hle : n≤k := by omega
          cases hnext : next s with
          | none =>
              have hz : run 1 s = none := by simp [run,hnext]
              rw [show n+1=1+n by omega, run_add, hz]
              simp
          | some t =>
              have htail : avoid target k t = true := by
                simpa [hnext] using hh.2
              have hno := ih t htail n hle
              rw [show n+1=1+n by omega, run_add]
              simpa [run,hnext] using hno

theorem no_reach_of_avoid
    (target : State) (k : Nat) (s t : State)
    (htrace : run k s = some t)
    (havoid : avoid target k s = true)
    (hrank : rank target < rank t) :
    ¬∃ n, run n s = some target := by
  rintro ⟨n,hn⟩
  by_cases hle : n≤k
  · exact avoid_sound target k s havoid n hle hn
  · have heq : n=k+(n-k) := by omega
    have htail : run (n-k) t = some target := by
      rw [heq,run_add,htrace] at hn
      simpa using hn
    have hp := (run_rank_bounds t target (n-k) htail).1
    omega

/-- The actual root's 1586th section is (3069,996), rank 7134,
which lies above target (11,7110), rank 7132. The checked prefix
avoids that target; the strict rank law therefore excludes it forever. -/
theorem no_root_11_7110 :
    ¬∃ n, run n (0,0) = some (11,7110) := by
  apply no_reach_of_avoid (11,7110) 1586 (0,0) (3069,996)
  · decide
  · decide
  · decide

#print axioms avoid_sound
#print axioms no_reach_of_avoid
#print axioms no_root_11_7110
end BB429FiniteAvoidance
