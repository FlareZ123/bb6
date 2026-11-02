import Lean.Elab.Tactic.Omega

namespace BB6Agent42

abbrev S := Nat × Nat × Nat

def nextC : S → Option S
  | (a,k,1) => some (a,k+1,0)
  | (_,_,2) => none
  | (a,k,3) => some (a,k+2,1)
  | (0,k,0) => some (1,0,2*k+2)
  | (1,0,0) => some (5,0,1)
  | (1,k+1,0) => some (2,2,2*k+1)
  | (a+2,k,0) => some (a,1,2*k+1)
  | (0,k,d+4) => if k%2=0 then some (4*(k/2)+2,2,d+1)
                    else some (4*(k/2)+5,0,d+4)
  | (a+1,k,d+4) => some (a,k+1,d+3)

def rank : S → Nat | (a,k,c) => a+2*k+c

def potential : S → Nat | (a,_,c) => a+c

def Strict (s t : S) : Prop :=
  rank s < rank t ∨ (rank s = rank t ∧ potential t < potential s)

theorem strict_step (s t : S) (h : nextC s = some t) : Strict s t := by
  rcases s with ⟨a,k,c⟩
  rcases c with _|_|_|_|d
  · rcases a with _|_|a
    · simp only [nextC,Option.some.injEq] at h
      subst t; left; simp only [rank]; omega
    · rcases k with _|k
      · simp only [nextC,Option.some.injEq] at h
        subst t; left; simp only [rank]; omega
      · simp only [nextC,Option.some.injEq] at h
        subst t; left; simp only [rank]; omega
    · simp only [nextC,Option.some.injEq] at h
      subst t; left; simp only [rank]; omega
  · simp only [nextC,Option.some.injEq] at h
    subst t; left; simp only [rank]; omega
  · simp [nextC] at h
  · simp only [nextC,Option.some.injEq] at h
    subst t; left; simp only [rank]; omega
  · rcases a with _|a
    · by_cases hk : k % 2 = 0
      · simp only [nextC,hk,↓reduceIte,Option.some.injEq] at h
        subst t; left
        simp only [rank]; omega
      · simp only [nextC,hk,↓reduceIte,Option.some.injEq] at h
        subst t; left
        simp only [rank]; omega
    · simp only [nextC,Option.some.injEq] at h
      subst t; right
      simp [rank,potential]
      omega

theorem strict_trans {s t u : S} (hst : Strict s t) (htu : Strict t u) : Strict s u := by
  unfold Strict at *
  rcases hst with hst|⟨he,hp⟩
  · rcases htu with htu|⟨he2,hp2⟩
    · left; omega
    · left; omega
  · rcases htu with htu|⟨he2,hp2⟩
    · left; omega
    · right; constructor <;> omega

theorem strict_irrefl (s : S) : ¬ Strict s s := by
  simp [Strict]

def run : Nat → Option S → Option S
  | 0, o => o
  | n+1, o => run n (o.bind nextC)

theorem run_none (n : Nat) : run n none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [run] using ih

theorem strict_run (n : Nat) (hn : 0 < n) (s t : S)
    (h : run n (some s) = some t) : Strict s t := by
  induction n generalizing s t with
  | zero => omega
  | succ n ih =>
      cases hs : nextC s with
      | none => simp [run,hs,run_none] at h
      | some u =>
          have hrest : run n (some u) = some t := by
            simpa [run,hs] using h
          have hhead := strict_step s u hs
          cases n with
          | zero =>
              have hsame : u = t := by simpa [run] using hrest
              subst t
              exact hhead
          | succ m =>
              have htail := ih (by omega) u t hrest
              exact strict_trans hhead htail

/-- No positive-length successful orbit of the exact Machine C accelerator
    can return to its starting state, from any natural counter triple. -/
theorem no_positive_cycle (s : S) (n : Nat) :
    run (n+1) (some s) ≠ some s := by
  intro h
  exact strict_irrefl s (strict_run (n+1) (by omega) s s h)

/-- The weighted rank never falls on a successful finite accelerator run. -/
theorem rank_run_mono (n : Nat) (s t : S)
    (h : run n (some s) = some t) : rank s ≤ rank t := by
  cases n with
  | zero =>
      have he : s = t := by simpa [run] using h
      subst t
      omega
  | succ n =>
      have hs := strict_run (n+1) (by omega) s t h
      unfold Strict at hs
      omega

/-- A finite run that stays on one rank level spends at least one unit of
    the nonnegative secondary potential per successful transition. -/
theorem rank_plateau_bound (n : Nat) (s t : S)
    (h : run n (some s) = some t) (he : rank s = rank t) :
    potential t + n ≤ potential s := by
  induction n generalizing s t with
  | zero =>
      have hs : s = t := by simpa [run] using h
      subst t
      omega
  | succ n ih =>
      cases hs : nextC s with
      | none => simp [run,hs,run_none] at h
      | some u =>
          have hr : run n (some u) = some t := by
            simpa [run,hs] using h
          have hstep := strict_step s u hs
          have hm := rank_run_mono n u t hr
          have hsame : rank s = rank u ∧ rank u = rank t := by
            unfold Strict at hstep
            omega
          have hd : potential u < potential s := by
            unfold Strict at hstep
            omega
          have hp := ih u t hr hsame.2
          omega

/-- After a successful interval longer than the initial potential, the
    weighted rank must have increased. -/
theorem rank_growth_after_potential (s t : S)
    (h : run (potential s + 1) (some s) = some t) :
    rank s < rank t := by
  have hm := rank_run_mono (potential s + 1) s t h
  by_cases hh : rank s < rank t
  · exact hh
  · have he : rank s = rank t := by omega
    have hp := rank_plateau_bound (potential s + 1) s t h he
    omega

/-- The coarser state-independent rank bound also suffices. -/
theorem rank_growth_after_rank (s t : S)
    (h : run (rank s + 1) (some s) = some t) :
    rank s < rank t := by
  have hm := rank_run_mono (rank s + 1) s t h
  by_cases hh : rank s < rank t
  · exact hh
  · have he : rank s = rank t := by omega
    have hp := rank_plateau_bound (rank s + 1) s t h he
    rcases s with ⟨a,k,c⟩
    simp only [potential,rank] at hp
    omega

#print axioms rank_growth_after_rank
#print axioms rank_plateau_bound
#print axioms no_positive_cycle
end BB6Agent42
