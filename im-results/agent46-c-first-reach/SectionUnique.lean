import SectionReachBridge
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46SectionReach
open BB6.Agent8Section

variable {α β : Type}
variable (f : α → Option α) (embed : β → α)
variable (time : β → Nat) (g : β → Option β)

/-- Exact first-return interpreters with different algorithms have the same
    output on every input. If both return a section point, their times agree. -/
theorem unique_first_section
    (hinj : Function.Injective embed)
    (time2 : β → Nat) (g2 : β → Option β)
    (hpos1 : ∀ p, 1 ≤ time p)
    (hpos2 : ∀ p, 1 ≤ time2 p)
    (hexact1 : ∀ p, run f (time p) (some (embed p)) = (g p).map embed)
    (hexact2 : ∀ p, run f (time2 p) (some (embed p)) = (g2 p).map embed)
    (hfirst1 : ∀ p j q, 1 ≤ j → j < time p →
      run f j (some (embed p)) ≠ some (embed q))
    (hfirst2 : ∀ p j q, 1 ≤ j → j < time2 p →
      run f j (some (embed p)) ≠ some (embed q))
    (p : β) : g p = g2 p := by
  cases h1 : g p with
  | none =>
      cases h2 : g2 p with
      | none => rfl
      | some q =>
          have he1 : run f (time p) (some (embed p)) = none := by
            simpa [h1] using hexact1 p
          have he2 : run f (time2 p) (some (embed p)) = some (embed q) := by
            simpa [h2] using hexact2 p
          by_cases hle : time p ≤ time2 p
          · have ha : time p + (time2 p-time p) = time2 p := by omega
            rw [←ha,run_add,he1,run_none] at he2
            contradiction
          · have hlt : time2 p < time p := by omega
            exact False.elim (hfirst1 p (time2 p) q (hpos2 p) hlt he2)
  | some q1 =>
      cases h2 : g2 p with
      | none =>
          have he1 : run f (time p) (some (embed p)) = some (embed q1) := by
            simpa [h1] using hexact1 p
          have he2 : run f (time2 p) (some (embed p)) = none := by
            simpa [h2] using hexact2 p
          by_cases hle : time2 p ≤ time p
          · have ha : time2 p + (time p-time2 p) = time p := by omega
            rw [←ha,run_add,he2,run_none] at he1
            contradiction
          · have hlt : time p < time2 p := by omega
            exact False.elim (hfirst2 p (time p) q1 (hpos1 p) hlt he1)
      | some q2 =>
          have he1 : run f (time p) (some (embed p)) = some (embed q1) := by
            simpa [h1] using hexact1 p
          have he2 : run f (time2 p) (some (embed p)) = some (embed q2) := by
            simpa [h2] using hexact2 p
          have ht : time p = time2 p := by
            by_cases ht : time p = time2 p
            · exact ht
            · by_cases hlt : time p < time2 p
              · exact False.elim (hfirst2 p (time p) q1 (hpos1 p) hlt he1)
              · have hgt : time2 p < time p := by omega
                exact False.elim (hfirst1 p (time2 p) q2 (hpos2 p) hgt he2)
          have hq : q1 = q2 := by
            rw [ht] at he1
            exact hinj (Option.some.inj (he1.symm.trans he2))
          change some q1 = some q2
          simp [hq]

#print axioms unique_first_section
end BB6.Agent46SectionReach
