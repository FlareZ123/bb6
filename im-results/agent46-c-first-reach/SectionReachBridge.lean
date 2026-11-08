import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46SectionReach
open BB6.Agent8Section

variable {α β : Type}
variable (f : α → Option α) (embed : β → α)
variable (time : β → Nat) (g : β → Option β)

/-- Every positive-time section visit is captured by a first-return section map. -/
theorem raw_reach_of_first
    (hinj : Function.Injective embed)
    (hpos : ∀ p, 1 ≤ time p)
    (hexact : ∀ p, run f (time p) (some (embed p)) = (g p).map embed)
    (hfirst : ∀ p j q, 1 ≤ j → j < time p →
      run f j (some (embed p)) ≠ some (embed q))
    (n : Nat) (p q : β)
    (h : run f n (some (embed p)) = some (embed q)) :
    ∃ m, run g m (some p) = some q := by
  induction n using Nat.strongRecOn generalizing p q with
  | ind n ih =>
      by_cases hz : n = 0
      · subst n
        have heq : embed p = embed q := by simpa [run] using h
        have heq' : p = q := hinj heq
        subst q
        exact ⟨0, rfl⟩
      · have hn : 1 ≤ n := by omega
        by_cases hlt : n < time p
        · exact False.elim (hfirst p n q hn hlt h)
        · have hle : time p ≤ n := by omega
          have hrest : run f (n-time p) ((g p).map embed) = some (embed q) := by
            have heq : time p + (n-time p) = n := by omega
            rw [←heq,run_add,hexact] at h
            exact h
          cases hg : g p with
          | none =>
              simp [hg,run_none] at hrest
          | some r =>
              have htail : run f (n-time p) (some (embed r)) = some (embed q) := by
                simpa [hg] using hrest
              obtain ⟨m,hm⟩ := ih (n-time p) (by have hp:=hpos p; omega) r q htail
              refine ⟨m+1, ?_⟩
              rw [run_succ_head]
              simpa [hg] using hm

/-- Every accelerated section orbit point is also a raw reachable state. -/
theorem raw_of_section
    (hexact : ∀ p, run f (time p) (some (embed p)) = (g p).map embed)
    (n : Nat) (p q : β)
    (h : run g n (some p) = some q) :
    ∃ k, run f k (some (embed p)) = some (embed q) := by
  induction n generalizing p with
  | zero =>
      have hp : p=q := by simpa [run] using h
      subst q
      exact ⟨0, rfl⟩
  | succ n ih =>
      rw [run_succ_head] at h
      cases hg : g p with
      | none => simp [hg,run_none] at h
      | some r =>
          have htail : run g n (some r) = some q := by simpa [hg] using h
          obtain ⟨m,hm⟩ := ih r htail
          refine ⟨time p+m, ?_⟩
          rw [run_add,hexact]
          simpa [hg] using hm

#print axioms raw_reach_of_first
#print axioms raw_of_section
end BB6.Agent46SectionReach
