import CLine
import M32U5Cells
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent32U5Backward

def Main (a k c : Nat) : Prop :=
  4 ≤ c ∧ c ≤ a ∧ a % 64 = (c + 19) % 64 ∧ (k + c) % 64 = 45

def Side (a k c : Nat) : Prop :=
  4 ≤ c ∧ a ≤ c ∧ c % 64 = (a + 46) % 64 ∧ (a + k) % 32 = 30

/-- The finite modular backward cone of the target (22,45,0). -/
def Bad (a k c : Nat) : Prop :=
  (c = 0 ∧ a % 64 = 22 ∧ k % 64 = 45) ∨
  (c = 1 ∧ a % 64 = 22 ∧ k % 64 = 44) ∨
  (c = 3 ∧ a % 64 = 22 ∧ k % 64 = 42) ∨
  Main a k c ∨
  Side a k c

def Forbidden (a k c : Nat) : Prop :=
  c = 0 ∧ CCert.u5ForbiddenCells a k

private theorem side_parent_forbidden (a c : Nat)
    (hac : a ≤ c) (ha : (a + 1) % 32 = 30)
    (hc : c % 64 = (a + 46) % 64) :
    CCert.u5ForbiddenCells (a + 2) ((c - 1) / 2) := by
  have ha32 : a % 32 = 29 := by omega
  have ha64 : a % 64 = 29 ∨ a % 64 = 61 := by omega
  have hc64 : c % 64 = 11 ∨ c % 64 = 43 := by omega
  rcases hc64 with hc11 | hc43
  · have hbig : 75 ≤ c := by omega
    constructor
    · omega
    · left
      omega
  · constructor
    · omega
    · right
      omega

/-- Every immediate predecessor of a Bad state is either Bad itself or
    lies in one of the two M32-certified forbidden c=0 families. -/
theorem bad_predecessor (a k c a' k' c' : Nat)
    (hstep : BB6CLine.nextC (a,k,c) = some (a',k',c'))
    (hbad : Bad a' k' c') :
    Bad a k c ∨ Forbidden a k c := by
  simp only [Bad] at hbad
  cases c with
  | zero =>
      cases a with
      | zero =>
          simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at hstep
          rcases hstep with ⟨rfl, rfl, rfl⟩
          rcases hbad with h0 | h1 | h2 | hm | hs
          all_goals simp_all [Main, Side] <;> omega
      | succ a =>
          cases a with
          | zero =>
              cases k with
              | zero =>
                  simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at hstep
                  rcases hstep with ⟨rfl, rfl, rfl⟩
                  rcases hbad with h0 | h1 | h2 | hm | hs
                  all_goals simp_all [Main, Side] <;> omega
              | succ k =>
                  simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at hstep
                  rcases hstep with ⟨rfl, rfl, rfl⟩
                  rcases hbad with h0 | h1 | h2 | hm | hs
                  all_goals simp_all [Main, Side] <;> omega
          | succ a =>
              simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at hstep
              rcases hstep with ⟨rfl, rfl, rfl⟩
              rcases hbad with h0 | h1 | h2 | hm | hs
              · simp_all [Main, Side] <;> omega
              · simp_all [Main, Side] <;> omega
              · simp_all [Main, Side] <;> omega
              · simp_all [Main, Side] <;> omega
              · rcases hs with ⟨hc, hac, hcm, hak⟩
                right
                refine ⟨rfl, ?_⟩
                have hF := side_parent_forbidden a (2*k+1) hac (by simpa using hak)
                  (by simpa using hcm)
                have hdiv : (2*k+1-1)/2 = k := by omega
                rw [hdiv] at hF
                exact hF
  | succ c =>
      cases c with
      | zero =>
          -- source c=1: the only Bad target has c=0 (T0).
          simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at hstep
          rcases hstep with ⟨rfl, rfl, rfl⟩
          rcases hbad with h0 | h1 | h2 | hm | hs
          · rcases h0 with ⟨hc, ha, hk⟩
            left
            exact Or.inr (Or.inl ⟨rfl, ha, by omega⟩)
          · simp_all [Main, Side] <;> omega
          · simp_all [Main, Side] <;> omega
          · simp_all [Main, Side] <;> omega
          · simp_all [Main, Side] <;> omega
      | succ c =>
          cases c with
          | zero =>
              simp [BB6CLine.nextC] at hstep
          | succ c =>
              cases c with
              | zero =>
                  -- source c=3: the only Bad target has c=1 (T1).
                  simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at hstep
                  rcases hstep with ⟨rfl, rfl, rfl⟩
                  rcases hbad with h0 | h1 | h2 | hm | hs
                  · simp_all [Main, Side] <;> omega
                  · rcases h1 with ⟨hc, ha, hk⟩
                    left
                    exact Or.inr (Or.inr (Or.inl ⟨rfl, ha, by omega⟩))
                  · simp_all [Main, Side] <;> omega
                  · simp_all [Main, Side] <;> omega
                  · simp_all [Main, Side] <;> omega
              | succ d =>
                  -- source c=d+4
                  cases a with
                  | zero =>
                      by_cases he : k % 2 = 0
                      · simp only [BB6CLine.nextC, he, ↓reduceIte,
                          Option.some.injEq, Prod.mk.injEq] at hstep
                        rcases hstep with ⟨rfl, rfl, rfl⟩
                        rcases hbad with h0 | h1 | h2 | hm | hs
                        · simp_all [Main, Side] <;> omega
                        · simp_all [Main, Side] <;> omega
                        · simp_all [Main, Side] <;> omega
                        · rcases hm with ⟨hc, hca, ham, hkc⟩
                          left
                          exact Or.inr (Or.inr (Or.inr (Or.inr
                            ⟨by omega, by omega, by omega, by omega⟩))
                          )
                        · rcases hs with ⟨hc, hac, hcm, hak⟩
                          omega
                      · simp only [BB6CLine.nextC, he, ↓reduceIte,
                          Option.some.injEq, Prod.mk.injEq] at hstep
                        rcases hstep with ⟨rfl, rfl, rfl⟩
                        rcases hbad with h0 | h1 | h2 | hm | hs
                        all_goals simp_all [Main, Side] <;> omega
                  | succ a =>
                      simp only [BB6CLine.nextC, Option.some.injEq, Prod.mk.injEq] at hstep
                      rcases hstep with ⟨rfl, rfl, rfl⟩
                      rcases hbad with h0 | h1 | h2 | hm | hs
                      · simp_all [Main, Side] <;> omega
                      · simp_all [Main, Side] <;> omega
                      · rcases h2 with ⟨hc, ha, hk⟩
                        have hd : d = 0 := by omega
                        subst d
                        left
                        exact Or.inr (Or.inr (Or.inr (Or.inl
                          ⟨by omega, by omega, by omega, by omega⟩)))
                      · rcases hm with ⟨hc, hca, ham, hkc⟩
                        left
                        exact Or.inr (Or.inr (Or.inr (Or.inl
                          ⟨by omega, by omega, by omega, by omega⟩)))
                      · rcases hs with ⟨hc, hac, hcm, hak⟩
                        left
                        exact Or.inr (Or.inr (Or.inr (Or.inr
                          ⟨by omega, by omega, by omega, by omega⟩)))

private theorem forbidden_unreachable {a k c : Nat}
    (hf : Forbidden a k c) :
    ¬ BB6CLine.Reach (a,k,c) := by
  rcases hf with ⟨rfl, hcells⟩
  exact CCert.original_u5_forbidden_unreachable a k hcells

/-- The backward cone is disjoint from the original blank CLine orbit. -/
theorem bad_unreachable {a k c : Nat} (hbad : Bad a k c) :
    ¬ BB6CLine.Reach (a,k,c) := by
  have hall : ∀ s : Nat × Nat × Nat, BB6CLine.Reach s →
      Bad s.1 s.2.1 s.2.2 → False := by
    intro s hr
    induction hr with
    | init =>
        simp [Bad, Main, Side]
    | @next p t hp hstep ih =>
        intro hbad'
        rcases p with ⟨a,k,c⟩
        rcases t with ⟨a',k',c'⟩
        rcases bad_predecessor a k c a' k' c' hstep hbad' with hprev | hforbidden
        · exact ih hprev
        · exact forbidden_unreachable hforbidden hp
  intro hr
  exact hall (a,k,c) hr hbad

/-- Uniform original-CLine exclusion of the mixed 2-adic parent residue
    a=22 (mod 64), k=45 (mod 64), at c=0. -/
theorem original_no_22_45 (a k : Nat)
    (ha : a % 64 = 22) (hk : k % 64 = 45) :
    ¬ BB6CLine.Reach (a,k,0) := by
  apply bad_unreachable
  exact Or.inl ⟨rfl, ha, hk⟩

#print axioms original_no_22_45
end BB6.Agent32U5Backward
