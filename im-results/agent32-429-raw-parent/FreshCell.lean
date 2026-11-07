import Frontier
import Lean.Elab.Tactic.Omega

namespace BB6Coverage

/-- Every one on a blank-origin tape was written at a previously scanned head position. -/
theorem marked_cell_previously_scanned (m : Machine) (n : Nat) (c : Config) (y : Int)
    (hr : run m n blank = some c) (hone : c.tape y = true) :
    ∃ k d, k < n ∧ run m k blank = some d ∧ d.head = y := by
  induction n generalizing c with
  | zero =>
      have hc : c = blank := by simpa [run] using hr.symm
      subst c
      simp [blank] at hone
  | succ n ih =>
      cases hp : run m n blank with
      | none => simp [run, hp] at hr
      | some d =>
          cases ht : m (readSlot d) with
          | none => simp [run, hp, rawStep, ht] at hr
          | some t =>
              have hc : c = applyMove d t := by
                simpa [run, hp, rawStep, ht] using hr.symm
              by_cases hy : y = d.head
              · exact ⟨n, d, Nat.lt_succ_self n, hp, hy.symm⟩
              · have hprev : d.tape y = true := by
                  rw [hc] at hone
                  simpa [applyMove, hy] using hone
                obtain ⟨k,e,hk,he,hhead⟩ := ih d hp hprev
                exact ⟨k,e,Nat.lt_trans hk (Nat.lt_succ_self n),he,hhead⟩

/-- A cell strictly to the right of every previously scanned head is still zero. -/
theorem blank_right_of_scanned_frontier (m : Machine) (n : Nat) (c : Config)
    (hr : run m n blank = some c)
    (hfront : ∀ k d, k < n → run m k blank = some d → d.head ≤ c.head) :
    c.tape (c.head + 1) = false := by
  by_cases h : c.tape (c.head + 1) = false
  · exact h
  · have hone : c.tape (c.head + 1) = true := by
      cases hc : c.tape (c.head + 1) <;> simp_all
    obtain ⟨k,d,hk,hd,hhead⟩ := marked_cell_previously_scanned m n c (c.head+1) hr hone
    have hb := hfront k d hk hd
    omega

#print axioms marked_cell_previously_scanned
#print axioms blank_right_of_scanned_frontier
end BB6Coverage
