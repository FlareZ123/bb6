import ChampionSpeed
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent24Speed

/-- A physical tape reached after n moves is supported on at most n
    positions which have been written at some time in that prefix. We
    deliberately permit duplicate write locations. -/
def Footprint (n : Nat) (c : Config) : Prop :=
  ∃ writes : List Int, writes.length ≤ n ∧
    ∀ x : Int, c.tape x = true → x ∈ writes

theorem footprint_applyMove (n : Nat) (c : Config) (t : Move)
    (h : Footprint n c) : Footprint (n+1) (applyMove c t) := by
  obtain ⟨writes,hcount,hcover⟩ := h
  refine ⟨c.head :: writes, ?_, ?_⟩
  · simp only [List.length_cons]
    omega
  · intro x hx
    by_cases heq : x = c.head
    · simp [heq]
    · have hsame : (applyMove c t).tape x = c.tape x := by
        simp [applyMove, heq]
      have hmark : c.tape x = true := by
        rw [hsame] at hx
        exact hx
      simp [hcover x hmark]

theorem footprint_rawStep (m : Machine) (n : Nat)
    (c d : Config) (h : Footprint n c)
    (hs : rawStep m c = some d) : Footprint (n+1) d := by
  simp only [rawStep] at hs
  cases hmove : m (readSlot c) with
  | none => simp [hmove] at hs
  | some t =>
    simp [hmove] at hs
    subst d
    exact footprint_applyMove n c t h

theorem footprint_run (m : Machine) (n : Nat) (c : Config)
    (h : run m n blank = some c) : Footprint n c := by
  induction n generalizing c with
  | zero =>
    simp [run] at h
    subst c
    exact ⟨[], by simp, by simp [blank]⟩
  | succ n ih =>
    simp only [run] at h
    cases hprev : run m n blank with
    | none => simp [hprev] at h
    | some prev =>
      simp [hprev] at h
      exact footprint_rawStep m n prev c (ih prev hprev) h

/-- If k distinct physical tape cells all contain one, a blank-origin
    run must have completed at least k ordinary moves. -/
theorem distinct_marks_below_steps (m : Machine) (n : Nat)
    (c : Config) (h : run m n blank = some c)
    (cells : List Int) (huniq : cells.Nodup)
    (hmarks : ∀ x, x ∈ cells → c.tape x = true) :
    cells.length ≤ n := by
  obtain ⟨writes,hwrites,hcover⟩ := footprint_run m n c h
  have hsubset : cells ⊆ writes := by
    intro x hx
    exact hcover x (hmarks x hx)
  exact Nat.le_trans (List.Nodup.length_le_of_subset huniq hsubset) hwrites

/-- Same bound on any eventual halting score. -/
theorem halt_score_at_least_number_of_distinct_marks (m : Machine)
    (n k : Nat) (c : Config) (hrun : run m n blank = some c)
    (hhalt : HaltsAfter m k)
    (cells : List Int) (huniq : cells.Nodup)
    (hmarks : ∀ x, x ∈ cells → c.tape x = true) :
    cells.length + 1 ≤ k + 1 := by
  have hcount := distinct_marks_below_steps m n c hrun cells huniq hmarks
  have htime := halt_time_at_least_checkpoint m n k c hrun hhalt
  omega


/-- A consecutive run of three-one symbols repeated b+1 times in the
    right half of the tape. The first repeated 1 lies seven positions
    to the right of the head, in the published TM63 S1 macro encoding. -/
def RightTripleBlock (b : Nat) (c : Config) : Prop :=
  ∀ i : Nat, i < 3*(b+1) → c.tape (c.head+7+(i : Int)) = true

/-- Any actual blank run with the complete right-hand triple block must
    have executed at least one write per 1 in that block. -/
theorem right_triple_count_lower (m : Machine) (n b : Nat)
    (c : Config) (hrun : run m n blank = some c)
    (hblock : RightTripleBlock b c) :
    3*(b+1) ≤ n := by
  let cells : List Int := (List.range (3*(b+1))).map
    (fun (i : Nat) => c.head + 7 + (i : Int))
  have huniq : cells.Nodup := by
    dsimp [cells]
    apply (List.Pairwise.map
      (R := fun (a d : Nat) => a ≠ d)
      (S := fun (a d : Int) => a ≠ d))
    · intro a d hne heq
      apply hne
      omega
    · exact List.nodup_range
  have hmarks : ∀ x, x ∈ cells → c.tape x = true := by
    intro x hx
    simp only [cells, List.mem_map] at hx
    obtain ⟨i,hi,rfl⟩ := hx
    apply hblock i
    exact List.mem_range.mp hi
  have hcount := distinct_marks_below_steps m n c hrun cells huniq hmarks
  simpa only [cells, List.length_map, List.length_range] using hcount

/-- Runtime-score bound consumed from an original source-level right
    counter certificate plus a genuine halting theorem. -/
theorem right_triple_halt_score_lower (m : Machine) (n k b : Nat)
    (c : Config) (hrun : run m n blank = some c)
    (hblock : RightTripleBlock b c) (hh : HaltsAfter m k) :
    3*(b+1)+1 ≤ k+1 := by
  have hwrites := right_triple_count_lower m n b c hrun hblock
  have htime := halt_time_at_least_checkpoint m n k c hrun hh
  omega

#print axioms footprint_run
#print axioms right_triple_count_lower
#print axioms right_triple_halt_score_lower
#print axioms distinct_marks_below_steps
#print axioms halt_score_at_least_number_of_distinct_marks
end BB6Coverage.Agent24Speed
