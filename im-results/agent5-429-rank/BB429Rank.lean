import Lean.Elab.Tactic.Omega

namespace BB429

abbrev State := Nat × Nat

def next : State → Option State
  | (u,w) =>
    let m := w / 2
    if w ≥ 2*u+3 then some (2*u+3, w-2*u-3)
    else if w = 2*u+2 then some (0, 4*u+18)
    else if w = 2*u+1 then some (11,4*u+2)
    else if w = 2*u then some (0,4*u+12)
    else
      let d := u-m
      if w%2=0 then
        if d=1 then some (0,2*w+12)
        else if d%2=0 then some (11,2*u+w-2)
        else some (0,2*u+w+10)
      else
        if d=1 then none
        else if d=2 then some (0,2*w+8)
        else if d%2=0 then
          if w=1 then some (11,2*u+10)
          else some (d+7,2*w-4)
        else some (d+3,2*w)

def rank (s : State) : Nat := 2*s.1 + s.2

theorem next_rank_interval (u w u' w' : Nat)
    (h : next (u,w) = some (u',w')) :
    2*u+w+3 ≤ 2*u'+w' ∧ 2*u'+w' ≤ 2*u+w+31 := by
  simp only [next] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    omega
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      omega
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        omega
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          omega
        · split at h
          · split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              omega
            · split at h
              · simp only [Option.some.injEq, Prod.mk.injEq] at h
                omega
              · simp only [Option.some.injEq, Prod.mk.injEq] at h
                omega
          · split at h
            · simp at h
            · split at h
              · simp only [Option.some.injEq, Prod.mk.injEq] at h
                omega
              · split at h
                · split at h
                  · simp only [Option.some.injEq, Prod.mk.injEq] at h
                    omega
                  · simp only [Option.some.injEq, Prod.mk.injEq] at h
                    omega
                · simp only [Option.some.injEq, Prod.mk.injEq] at h
                  omega


/-- Every surviving macro-step advances the linear rank by between 3 and 31. -/
def run (n : Nat) (s : State) : Option State :=
  match n with
  | 0 => some s
  | k+1 => (run k s).bind next

theorem run_rank_bounds (s t : State) (n : Nat)
    (h : run n s = some t) :
    rank s + 3*n ≤ rank t ∧ rank t ≤ rank s + 31*n := by
  induction n generalizing t with
  | zero =>
    simp [run] at h
    subst t
    simp
  | succ n ih =>
    simp only [run] at h
    cases hm : run n s with
    | none => simp [hm] at h
    | some mid =>
      simp only [hm, Option.bind_some] at h
      obtain ⟨hlo, hhi⟩ := ih mid hm
      have hn := next_rank_interval mid.1 mid.2 t.1 t.2 h
      simp only [rank] at hlo hhi ⊢
      omega

theorem run_add (n k : Nat) (s : State) :
    run (n+k) s = (run n s).bind (run k) := by
  induction k with
  | zero =>
    simp [run]
  | succ k ih =>
    rw [Nat.add_succ]
    simp only [run, ih]
    cases h : run n s with
    | none => simp [h]
    | some t =>
      simp [h, run]

/-- Distinct successful times cannot have exactly the same accelerated state. -/
theorem no_positive_loop (s t : State) (i j : Nat)
    (hij : i < j) (hi : run i s = some t) (hj : run j s = some t) : False := by
  have heq : j = i + (j-i) := by omega
  rw [heq, run_add, hi] at hj
  simp only [Option.bind_some] at hj
  have hr := (run_rank_bounds t t (j-i) hj).1
  have hpos : 0 < j-i := by omega
  omega

/-- Reachability of any fixed accelerated state admits a state-dependent exact finite cutoff. -/
theorem reach_target_iff_bounded (s t : State) :
    (∃ n, run n s = some t) ↔
    (∃ n, n ≤ rank t / 3 ∧ run n s = some t) := by
  constructor
  · rintro ⟨n, hn⟩
    have hr := (run_rank_bounds s t n hn).1
    refine ⟨n, ?_, hn⟩
    omega
  · rintro ⟨n, _, hn⟩
    exact ⟨n, hn⟩


/-- A finite mod-six abstract invariant for first-branch segments. -/
def shield (u w : Nat) : Prop :=
  (w % 6 = 0 ∨ w % 6 = 4) ∨
  (u % 6 = 1 ∧ (w % 6 = 3 ∨ w % 6 = 5)) ∨
  (u % 6 = 3 ∧ (w % 6 = 1 ∨ w % 6 = 3)) ∨
  (u % 6 = 5 ∧ (w % 6 = 1 ∨ w % 6 = 5))

theorem shield_of_seed (u w : Nat)
  (h : w % 6 = 0 ∨ w % 6 = 4) : shield u w := Or.inl h

theorem shield_survives_first (u w : Nat) (hs : shield u w)
  (hw : 2*u+3 ≤ w) : shield (2*u+3) (w-2*u-3) := by
  simp only [shield] at hs ⊢
  omega

theorem shield_excludes_halt (u w : Nat) (hs : shield u w) :
  w + 1 ≠ 2*u := by
  simp only [shield] at hs
  omega


/-- The unique halting gateway is exactly the odd line w = 2u - 1. -/
theorem next_none_iff_halt_line (u w : Nat) :
    next (u,w) = none ↔ w+1 = 2*u := by
  constructor
  · intro h
    simp only [next] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · split at h
              · cases h
              · split at h
                · cases h
                · cases h
            · split at h
              · omega
              · split at h
                · cases h
                · split at h
                  · split at h
                    · cases h
                    · cases h
                  · cases h
  · intro hl
    have hw : ¬(w ≥ 2*u+3) := by omega
    have hw2 : w ≠ 2*u+2 := by omega
    have hw1 : w ≠ 2*u+1 := by omega
    have hw0 : w ≠ 2*u := by omega
    have hp : w % 2 ≠ 0 := by omega
    have hd : u-w/2=1 := by omega
    simp [next, hw, hw2, hw1, hw0, hp, hd]

/-- For the complete source macro map, an abstract first-branch shield forbids
    halting at the next exit; no other step can halt directly. -/
theorem shield_next_not_halt (u w : Nat) (hs : shield u w) :
    next (u,w) ≠ none := by
  intro h
  exact shield_excludes_halt u w hs ((next_none_iff_halt_line u w).mp h)


/-- The repeatedly applied first (subtraction/doubling) branch only. -/
def firstStep (s : State) : Option State :=
  if 2*s.1+3 ≤ s.2 then
    some (2*s.1+3,s.2-2*s.1-3)
  else none

def firstRun (n : Nat) (s : State) : Option State :=
  match n with
  | 0 => some s
  | k+1 => (firstRun k s).bind firstStep

theorem firstStep_is_next (u w : Nat) (h : 2*u+3 ≤ w) :
    firstStep (u,w) = next (u,w) := by
  simp [firstStep,next,h]

theorem firstRun_shield (s t : State) (n : Nat)
    (hs : shield s.1 s.2) (h : firstRun n s = some t) :
    shield t.1 t.2 := by
  induction n generalizing t with
  | zero =>
    simp [firstRun] at h
    subst t
    exact hs
  | succ n ih =>
    simp only [firstRun] at h
    cases hprev : firstRun n s with
    | none => simp [hprev] at h
    | some p =>
      simp only [hprev, Option.bind_some] at h
      have hps := ih p hprev
      simp only [firstStep] at h
      split at h
      · simp only [Option.some.injEq] at h
        cases h
        exact shield_survives_first p.1 p.2 hps (by assumption)
      · simp at h

/-- Two thirds of even-w starting residue classes cannot halt within
    their current (potentially arbitrarily long) first-branch burst. -/
theorem two_thirds_first_burst_safe (u w n : Nat) (t : State)
    (hseed : w % 6 = 0 ∨ w % 6 = 4)
    (htrace : firstRun n (u,w) = some t) :
    next t ≠ none := by
  exact shield_next_not_halt t.1 t.2
    (firstRun_shield (u,w) t n (shield_of_seed u w hseed) htrace)

#print axioms firstStep_is_next
#print axioms firstRun_shield
#print axioms two_thirds_first_burst_safe

#print axioms next_none_iff_halt_line
#print axioms shield_next_not_halt

#print axioms shield_survives_first
#print axioms shield_excludes_halt

#print axioms run_rank_bounds
#print axioms no_positive_loop
#print axioms reach_target_iff_bounded

#print axioms next_rank_interval
end BB429
