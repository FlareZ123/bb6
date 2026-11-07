import Agent8GateRepulsionSource

/-!
Uniform original-source upper and lower affine envelopes for the complete
#623 B-drain. All inputs are quantified; no blank-root machine decision.
-/

namespace BB6.Agent8DrainSectorSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-- A successful source evaluator loses at most k+1 in its first counter. -/
theorem evalA_first_lower (a : Nat) :
    ∀ k m aa bb dd : Nat, evalA a k m = some (aa,bb,dd) → a ≤ aa+k+1 := by
  induction a with
  | zero =>
    intro k m aa bb dd h
    omega
  | succ a ih =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3=2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k%3=0
      · simp [h2,h0] at h
        cases h
        omega
      · simp [h2,h0] at h
        have hi := ih (k/3) (m+2*(k/3)+3) aa bb dd h
        omega

/-- A successful evaluator grows its third counter by at most 5k+2. -/
theorem evalA_third_upper (a : Nat) :
    ∀ k m aa bb dd : Nat, evalA a k m = some (aa,bb,dd) → dd ≤ m+5*k+2 := by
  induction a with
  | zero =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3=2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k%3=0
      · simp [h2,h0] at h
      · simp [h2,h0] at h
        cases h
        omega
  | succ a ih =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3=2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k%3=0
      · simp [h2,h0] at h
        cases h
        omega
      · simp [h2,h0] at h
        have hi := ih (k/3) (m+2*(k/3)+3) aa bb dd h
        omega

/-- Source B-drain lower bound on first counter, independent of a,d. -/
theorem drainB_first_lower (b : Nat) :
    ∀ a d aa dd : Nat, drainB a b d = some (.D aa dd) → a ≤ aa+2*b := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d aa dd h
    rw [drainB] at h
    by_cases hb : b=0
    · simp [hb] at h
      cases h
      omega
    · simp only [if_neg hb] at h
      cases he : evalA a (b-1) (d+2*b+3) with
      | none => simp [he] at h
      | some p =>
        rcases p with ⟨a1,b1,d1⟩
        simp only [he,Option.bind_some] at h
        by_cases hlt : b1<b
        · simp only [if_pos hlt] at h
          have hfirst := evalA_first_lower a (b-1) (d+2*b+3) a1 b1 d1 he
          have hquot := BB6.Agent8DrainLogDepthSource.evalA_second_le_quotient
            a (b-1) (d+2*b+3) a1 b1 d1 he
          have hrec := ih b1 hlt a1 d1 aa dd h
          omega
        · simp [hlt] at h

/-- Third counter of every successful source B-drain grows by at most 17b. -/
theorem drainB_third_upper (b : Nat) :
    ∀ a d aa dd : Nat, drainB a b d = some (.D aa dd) → dd ≤ d+17*b := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d aa dd h
    rw [drainB] at h
    by_cases hb : b=0
    · simp [hb] at h
      cases h
      omega
    · simp only [if_neg hb] at h
      cases he : evalA a (b-1) (d+2*b+3) with
      | none => simp [he] at h
      | some p =>
        rcases p with ⟨a1,b1,d1⟩
        simp only [he,Option.bind_some] at h
        by_cases hlt : b1<b
        · simp only [if_pos hlt] at h
          have hthird := evalA_third_upper a (b-1) (d+2*b+3) a1 b1 d1 he
          have hquot := BB6.Agent8DrainLogDepthSource.evalA_second_le_quotient
            a (b-1) (d+2*b+3) a1 b1 d1 he
          have hrec := ih b1 hlt a1 d1 aa dd h
          omega
        · simp [hlt] at h

/-- All successful drains from strong leftward initial counter imbalance
return to the unconditional far-left safe cone for a following step. -/
theorem drainB_left_sector (a b d aa dd : Nat)
    (h : drainB a b d = some (.D aa dd))
    (hfar : 2*d+36*b+8 ≤ a) :
    2*dd+8 ≤ aa := by
  have ha := drainB_first_lower b a d aa dd h
  have hd := drainB_third_upper b a d aa dd h
  omega

#print axioms evalA_first_lower
#print axioms evalA_third_upper
#print axioms drainB_first_lower
#print axioms drainB_third_upper
#print axioms drainB_left_sector
end BB6.Agent8DrainSectorSource
