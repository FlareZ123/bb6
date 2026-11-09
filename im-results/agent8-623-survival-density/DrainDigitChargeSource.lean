import Agent49FlatDrainSource

/-!
Exact ternary digit-charge cocycle for the ORIGINAL Cryptids #623 complete
B-drain. The imported Agent49FlatDrainSource.flatB_eq_drainB theorem
identifies the one-level interpreter with the unmodified machine source.
The result applies to arbitrary natural inputs and every successful drain,
not to an asserted blank-root decision.
-/

namespace BB6.Agent8DigitChargeSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49FlatDrainSource

/-- Terminal first counter and exact third-counter excess. Each ternary
reduction has a fixed charge: residues 0,1,2 at positive first counter
cost 0,4,2; residue 2 at zero first counter costs 1. -/
def digitCode (a b : Nat) : Option (Nat × Nat) :=
  if b=0 then some (a,0)
  else if b%3=0 then digitCode (a+1) (b/3-1)
  else if b%3=1 then
    if a=0 then none else (digitCode (a-1) (b/3)).map (fun p => (p.1, p.2+4))
  else if a=0 then (digitCode 0 (b/3)).map (fun p => (p.1, p.2+1))
  else (digitCode (a-1) (b/3+1)).map (fun p => (p.1, p.2+2))
termination_by b
decreasing_by
  all_goals
    have hdiv : b = 3*(b/3)+b%3 := by omega
    omega

def realize (d b : Nat) (p : Nat × Nat) : HighLevelState :=
  .D p.1 (d+3*b+p.2)

/-- Source-connected equality of the entire successful output and of failure.
In particular, the term 3*b is exact and the remainder is an independently
computable, nonnegative digit charge. -/
theorem flatB_digitCode (b : Nat) :
    ∀ a d : Nat, flatB a b d = (digitCode a b).map (realize d b) := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d
    rw [flatB, digitCode]
    by_cases hz : b=0
    · subst b
      simp [realize]
    · simp only [if_neg hz]
      have hdiv : b=3*(b/3)+b%3 := by omega
      by_cases hr0 : b%3=0
      · simp only [if_pos hr0]
        have hsmall : b/3-1<b := by omega
        rw [ih (b/3-1) hsmall (a+1) (d+2*b+3)]
        cases hc : digitCode (a+1) (b/3-1) with
        | none => simp [hc]
        | some p =>
          rcases p with ⟨aa,c⟩
          simp [hc,realize]
          omega
      · simp only [if_neg hr0]
        by_cases hr1 : b%3=1
        · simp only [if_pos hr1]
          by_cases ha : a=0
          · simp [ha]
          · simp only [if_neg ha]
            have hsmall : b/3<b := by omega
            rw [ih (b/3) hsmall (a-1) (d+2*b+5)]
            cases hc : digitCode (a-1) (b/3) with
            | none => simp [hc]
            | some p =>
              rcases p with ⟨aa,c⟩
              simp [hc,realize]
              omega
        · simp only [if_neg hr1]
          by_cases ha : a=0
          · simp only [if_pos ha]
            have hsmall : b/3<b := by omega
            rw [ih (b/3) hsmall 0 (d+2*b+3)]
            cases hc : digitCode 0 (b/3) with
            | none => simp [hc]
            | some p =>
              rcases p with ⟨aa,c⟩
              simp [hc,realize]
              omega
          · simp only [if_neg ha]
            have hsmall : b/3+1<b := by omega
            rw [ih (b/3+1) hsmall (a-1) (d+2*b+1)]
            cases hc : digitCode (a-1) (b/3+1) with
            | none => simp [hc]
            | some p =>
              rcases p with ⟨aa,c⟩
              simp [hc,realize]
              omega

/-- Exact original-source drain output, not merely a copied-model theorem. -/
theorem drainB_digitCode (a b d : Nat) :
    drainB a b d = (digitCode a b).map (realize d b) := by
  rw [← flatB_eq_drainB b a d]
  exact flatB_digitCode b a d

/-- Every completed source drain has a unique intrinsic digit charge. -/
theorem drainB_charge_witness (a b d aa dd : Nat)
    (h : drainB a b d = some (.D aa dd)) :
    ∃ c : Nat, digitCode a b = some (aa,c) ∧ dd=d+3*b+c := by
  rw [drainB_digitCode] at h
  cases hc : digitCode a b with
  | none => simp [hc] at h
  | some p =>
    rcases p with ⟨x,c⟩
    simp only [hc, Option.map_some, realize, HighLevelState.D.injEq] at h
    obtain ⟨h1,h2⟩ := h
    subst x
    subst dd
    exact ⟨c,hc,rfl⟩

#print axioms flatB_digitCode
#print axioms drainB_digitCode
#print axioms drainB_charge_witness
end BB6.Agent8DigitChargeSource
