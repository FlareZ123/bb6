import Frontier
import Lean.Elab.Tactic.Omega
namespace BB6Coverage

/-- On a physical blank-origin tape, any marked cell strictly right of the
current head was written by an earlier left-moving instruction. The witness
includes its exact prior transition row, rather than only its head location. -/
theorem right_marked_has_left_writer (m : Machine) (n : Nat) (c : Config) (y : Int)
    (hr : run m n blank = some c) (hpos : c.head < y) (hone : c.tape y = true) :
    ∃ k d t, k < n ∧ run m k blank = some d ∧ d.head = y ∧
      m (readSlot d) = some t ∧ t.write = true ∧ t.right = false := by
  induction n generalizing c with
  | zero =>
      have hc : c = blank := by simpa [run] using hr.symm
      subst c
      simp [blank] at hone
  | succ n ih =>
      cases hp : run m n blank with
      | none => simp [run, hp] at hr
      | some d =>
          cases hm : m (readSlot d) with
          | none => simp [run, hp, rawStep, hm] at hr
          | some t =>
              have hc : c = applyMove d t := by
                simpa [run, hp, rawStep, hm] using hr.symm
              by_cases hdy : d.head = y
              · have hw : t.write = true := by
                  rw [hc] at hone
                  simpa [applyMove, hdy] using hone
                have hl : t.right = false := by
                  rw [hc] at hpos
                  cases hright : t.right with
                  | false => rfl
                  | true =>
                      simp [applyMove, hright] at hpos
                      omega
                exact ⟨n, d, t, Nat.lt_succ_self n, hp, hdy, hm, hw, hl⟩
              · have hdp : d.head < y := by
                  rw [hc] at hpos
                  cases hright : t.right <;> simp [applyMove, hright] at hpos <;> omega
                have hdone : d.tape y = true := by
                  rw [hc] at hone
                  simpa [applyMove, Ne.symm hdy] using hone
                obtain ⟨k, e, v, hk, he, hxy, ha, hw, hl⟩ := ih d hp hdp hdone
                exact ⟨k, e, v, Nat.lt_trans hk (Nat.lt_succ_self n), he, hxy, ha, hw, hl⟩

#print axioms right_marked_has_left_writer
end BB6Coverage
