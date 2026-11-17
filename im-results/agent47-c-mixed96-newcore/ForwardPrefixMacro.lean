import CLine

namespace BB6CLine.Agent47ForwardPrefix

abbrev State := Nat × Nat × Nat

def Boundary (s : State) : Prop := s.1 = 0 ∨ s.2.2 ≤ 3

/-- One ordinary CLine step followed by a maximal high-branch run. -/
def macroNext (s : State) : Option State :=
  match nextC s with
  | none => none
  | some (a,k,c) =>
      if 1 ≤ a ∧ 4 ≤ c then
        let n := min a (c - 3)
        some (a - n, k + n, c - n)
      else
        some (a,k,c)

/-- Repeating the rank-preserving high branch for n steps. -/
theorem highRun_reach (a k c n : Nat)
    (h : Reach (a,k,c))
    (hna : n ≤ a)
    (hnc : n ≤ c - 3) :
    Reach (a-n,k+n,c-n) := by
  induction n with
  | zero =>
      simpa using h
  | succ n ih =>
      have hna' : n ≤ a := by omega
      have hnc' : n ≤ c - 3 := by omega
      have hreach : Reach (a-n,k+n,c-n) := ih hna' hnc'
      have ha : a-n = (a-n-1)+1 := by omega
      have hc : c-n = (c-n-4)+4 := by omega
      have hstep :
          nextC (a-n,k+n,c-n) =
            some (a-(n+1),k+(n+1),c-(n+1)) := by
        rw [ha, hc]
        simp [nextC]
        congr 1 <;> omega
      exact Reach.next _ _ hreach hstep

/-- A macro step is a genuine finite sequence of ordinary CLine steps. -/
theorem macroNext_sound {s t : State}
    (hreach : Reach s)
    (hmacro : macroNext s = some t) :
    Reach t := by
  unfold macroNext at hmacro
  cases hnext : nextC s with
  | none =>
      simp [hnext] at hmacro
  | some u =>
      rcases u with ⟨a,k,c⟩
      by_cases hhigh : 1 ≤ a ∧ 4 ≤ c
      · simp [hnext,hhigh] at hmacro
        subst t
        have hu : Reach (a,k,c) := Reach.next _ _ hreach hnext
        exact highRun_reach a k c (min a (c-3)) hu
          (Nat.min_le_left _ _) (Nat.min_le_right _ _)
      · simp [hnext,hhigh] at hmacro
        subst t
        exact Reach.next _ _ hreach hnext

/-- Every successful macro step ends on the boundary a=0 or c<=3. -/
theorem macroNext_boundary {s t : State}
    (hmacro : macroNext s = some t) :
    Boundary t := by
  unfold macroNext at hmacro
  cases hnext : nextC s with
  | none =>
      simp [hnext] at hmacro
  | some u =>
      rcases u with ⟨a,k,c⟩
      by_cases hhigh : 1 ≤ a ∧ 4 ≤ c
      · simp [hnext,hhigh] at hmacro
        subst t
        dsimp [Boundary]
        by_cases hle : a ≤ c - 3
        · simp [Nat.min_eq_left hle]
        · have hle' : c - 3 ≤ a := Nat.le_of_not_ge hle
          simp [Nat.min_eq_right hle']
      · simp [hnext,hhigh] at hmacro
        subst t
        dsimp [Boundary]
        push_neg at hhigh
        omega

/-- The macro step is also rank-nondecreasing. -/
theorem macroNext_rank_mono {s t : State}
    (hmacro : macroNext s = some t) :
    rankC s ≤ rankC t := by
  unfold macroNext at hmacro
  cases hnext : nextC s with
  | none =>
      simp [hnext] at hmacro
  | some u =>
      rcases u with ⟨a,k,c⟩
      have hrank := rank_mono hnext
      by_cases hhigh : 1 ≤ a ∧ 4 ≤ c
      · simp [hnext,hhigh] at hmacro
        subst t
        have heq :
            rankC (a-min a (c-3),k+min a (c-3),c-min a (c-3))
              = rankC (a,k,c) := by
          simp [rankC]
          omega
        rw [heq]
        exact hrank
      · simp [hnext,hhigh] at hmacro
        subst t
        exact hrank

/-- Iterate successful macro steps; if the orbit halts, retain its last state. -/
def macroRun : Nat → State → State
  | 0, s => s
  | n+1, s =>
      match macroNext s with
      | none => s
      | some t => macroRun n t

theorem macroRun_reach (n : Nat) {s : State}
    (hreach : Reach s) :
    Reach (macroRun n s) := by
  induction n generalizing s with
  | zero =>
      simpa [macroRun] using hreach
  | succ n ih =>
      simp only [macroRun]
      cases hmacro : macroNext s with
      | none =>
          simpa [hmacro] using hreach
      | some t =>
          simpa [hmacro] using ih (macroNext_sound hreach hmacro)

theorem macroRun_rank_mono (n : Nat) (s : State) :
    rankC s ≤ rankC (macroRun n s) := by
  induction n generalizing s with
  | zero =>
      simp [macroRun]
  | succ n ih =>
      simp only [macroRun]
      cases hmacro : macroNext s with
      | none =>
          simp [hmacro]
      | some t =>
          have hfirst : rankC s ≤ rankC t := macroNext_rank_mono hmacro
          exact hfirst.trans (ih t)

end BB6CLine.Agent47ForwardPrefix
