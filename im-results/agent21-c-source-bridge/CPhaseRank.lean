import CReachBridge
import Lean.Elab.Tactic.Omega

namespace BB6.CPhaseRank
open BB6.CReachBridge

/-- Lexicographic rank, encoded numerically, for the c>0 excursion. -/
def phaseRank : S → Nat
  | (a,_,c) => 2*c + if a=0 then 1 else 0

/-- Every defined accelerator step strictly reduces the right-counter
    phase rank, provided its source had a positive right counter. -/
theorem positive_phase_decrease (s t : S) (hc : 0 < s.2.2)
    (h : BB6CLine.nextC s = some t) : phaseRank t < phaseRank s := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · simp at hc
  · simp only [BB6CLine.nextC,Option.some.injEq] at h
    subst t
    simp only [phaseRank]
    by_cases ha : a=0
    · simp [ha] <;> omega
    · simp [ha] <;> omega
  · simp [BB6CLine.nextC] at h
  · simp only [BB6CLine.nextC,Option.some.injEq] at h
    subst t
    simp only [phaseRank]
    by_cases ha : a=0
    · simp [ha] <;> omega
    · simp [ha] <;> omega
  · rcases a with _|a
    · by_cases hk:k%2=0
      · simp only [BB6CLine.nextC,hk,↓reduceIte,Option.some.injEq] at h
        subst t
        simp [phaseRank] <;> omega
      · simp only [BB6CLine.nextC,hk,↓reduceIte,Option.some.injEq] at h
        subst t
        simp [phaseRank] <;> omega
    · simp only [BB6CLine.nextC,Option.some.injEq] at h
      subst t
      simp only [phaseRank]
      by_cases ha : a=0
      · simp [ha] <;> omega
      · simp [ha] <;> omega

/-- Every positive-right-counter excursion terminates in a zero-right-counter
    state or stops, within at most its decreasing phase rank. -/
theorem phase_exit_bound (s : S) :
    ∃ n : Nat, n ≤ phaseRank s ∧
      (runN n (some s) = none ∨
        ∃ a k : Nat, runN n (some s) = some (a,k,0)) := by
  have all : ∀ m : Nat, ∀ s : S, phaseRank s = m →
      ∃ n : Nat, n ≤ m ∧
        (runN n (some s) = none ∨
          ∃ a k : Nat, runN n (some s) = some (a,k,0)) := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
        intro s hm
        rcases s with ⟨a,k,c⟩
        by_cases hc : c=0
        · subst c
          exact ⟨0, by omega, Or.inr ⟨a,k,rfl⟩⟩
        · have hpos : 0<c := by omega
          cases hn : BB6CLine.nextC (a,k,c) with
          | none =>
              refine ⟨1, ?_, Or.inl ?_⟩
              · have hmu : 1 ≤ phaseRank (a,k,c) := by
                  simp [phaseRank]
                  omega
                omega
              · simp [runN, stepC, hn]
          | some t =>
              have hdec := positive_phase_decrease (a,k,c) t hpos hn
              have hlt : phaseRank t < m := by omega
              rcases ih (phaseRank t) hlt t rfl with ⟨n, hbound, hres⟩
              refine ⟨n+1, by omega, ?_⟩
              have hs : runN (n+1) (some (a,k,c)) = runN n (some t) := by
                rw [runN_succ_head]
                simp [stepC, hn]
              rw [hs]
              exact hres
  exact all (phaseRank s) s rfl

/-- A c=0 reset always enters an excursion with phase rank <= 4k+4. -/
theorem c0_first_rank (a k : Nat) :
    ∃ t : S, BB6CLine.nextC (a,k,0) = some t ∧ phaseRank t ≤ 4*k+4 := by
  rcases a with _ | _ | a
  · refine ⟨(1,0,2*k+2),rfl,?_⟩
    simp [phaseRank]
    omega
  · rcases k with _ | k
    · refine ⟨(5,0,1),rfl,?_⟩
      simp [phaseRank]
    · refine ⟨(2,2,2*k+1),rfl,?_⟩
      simp [phaseRank]
      omega
  · refine ⟨(a,1,2*k+1),rfl,?_⟩
    by_cases ha : a=0
    · simp [phaseRank,ha]
      omega
    · simp [phaseRank,ha]
      omega

/-- Every c=0 configuration returns to c=0, or halts, after at least one
    and at most 4k+5 accelerated steps, independent of the left counter a. -/
theorem c0_excursion_bound (a k : Nat) :
    ∃ n : Nat, 1 ≤ n ∧ n ≤ 4*k+5 ∧
      (runN n (some (a,k,0)) = none ∨
        ∃ a' k' : Nat, runN n (some (a,k,0)) = some (a',k',0)) := by
  obtain ⟨t,ht,hm⟩ := c0_first_rank a k
  obtain ⟨n,hn,hres⟩ := phase_exit_bound t
  refine ⟨n+1, by omega, by omega, ?_⟩
  have hs : runN (n+1) (some (a,k,0)) = runN n (some t) := by
    rw [runN_succ_head]
    simp [stepC,ht]
  rw [hs]
  exact hres

#print axioms positive_phase_decrease
#print axioms phase_exit_bound
#print axioms c0_excursion_bound
end BB6.CPhaseRank
