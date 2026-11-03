import Frontier
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent24Speed

/-- A configuration within n successful blank-origin steps has its head
    inside [-n,n] and has never written beyond [-n,n). -/
def Within (n : Nat) (c : Config) : Prop :=
  -(n : Int) ≤ c.head ∧ c.head ≤ (n : Int) ∧
  ∀ x : Int, x < -(n : Int) ∨ (n : Int) ≤ x → c.tape x = false

theorem move_within (n : Nat) (c : Config) (t : Move)
    (h : Within n c) : Within (n+1) (applyMove c t) := by
  rcases h with ⟨hleft, hright, htape⟩
  unfold Within applyMove
  constructor
  · cases hdir : t.right <;> simp only [hdir, ↓reduceIte] <;> omega
  constructor
  · cases hdir : t.right <;> simp only [hdir, ↓reduceIte] <;> omega
  · intro x hx
    have hnot : x ≠ c.head := by omega
    have houtside : x < -(n : Int) ∨ (n : Int) ≤ x := by omega
    simp only [hnot, ↓reduceIte]
    exact htape x houtside

theorem rawStep_within (m : Machine) (n : Nat) (c d : Config)
    (h : Within n c) (hs : rawStep m c = some d) : Within (n+1) d := by
  simp only [rawStep] at hs
  cases hmove : m (readSlot c) with
  | none => simp [hmove] at hs
  | some t =>
    simp [hmove] at hs
    subst d
    exact move_within n c t h

theorem run_within (m : Machine) (n : Nat) (c : Config)
    (h : run m n blank = some c) : Within n c := by
  induction n generalizing c with
  | zero =>
    simp [run] at h
    subst c
    simp [Within, blank]
  | succ n ih =>
    simp only [run] at h
    cases hprev : run m n blank with
    | none => simp [hprev] at h
    | some prev =>
      simp [hprev] at h
      exact rawStep_within m n prev c (ih prev hprev) h

/-- Any 1 found at positive position x after n blank-origin moves
    certifies that the machine has executed strictly more than x moves. -/
theorem marked_right_below_steps (m : Machine) (n : Nat)
    (c : Config) (h : run m n blank = some c)
    (x : Int) (hx : c.tape x = true) : x < (n : Int) := by
  have hbound := (run_within m n c h).2.2
  by_cases hn : x < (n : Int)
  · exact hn
  · have hzero := hbound x (Or.inr (by omega))
    simp [hx] at hzero

/-- The same time lower bound holds for a 1 far to the left. -/
theorem marked_left_below_steps (m : Machine) (n : Nat)
    (c : Config) (h : run m n blank = some c)
    (x : Int) (hx : c.tape x = true) : -(n : Int) ≤ x := by
  have hbound := (run_within m n c h).2.2
  by_cases hn : -(n : Int) ≤ x
  · exact hn
  · have hzero := hbound x (Or.inl (by omega))
    simp [hx] at hzero

/-- A known far-right marked cell at any live checkpoint gives a lower bound
    on the eventual halt time, without needing to compute that time. -/
theorem halt_time_at_least_checkpoint (m : Machine) (n k : Nat)
    (c : Config) (h : run m n blank = some c) (hk : HaltsAfter m k) : n ≤ k := by
  by_cases hn : n ≤ k
  · exact hn
  · have hle : k+1 ≤ n := by omega
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hle
    have hnone : run m n blank = none := by
      rw [hd]
      exact run_none_add m blank (k+1) d hk.2
    rw [hnone] at h
    cases h

theorem attained_score_gt_marked_right (m : Machine) (k n : Nat)
    (c : Config) (h : run m n blank = some c)
    (halt : HaltsAfter m k) (x : Int) (hx : c.tape x = true) :
    x < (k : Int) := by
  have ht : x < (n : Int) := marked_right_below_steps m n c h x hx
  have htime : n ≤ k := halt_time_at_least_checkpoint m n k c h halt
  omega

/-- A pair of marked cells at any one live checkpoint gives a spatially
    translation-invariant lower bound on the number of moves already made.
    This is suited to a symbolic tape with a long block far from its head. -/
theorem marked_span_below_steps (m : Machine) (n : Nat)
    (c : Config) (h : run m n blank = some c)
    (x y : Int) (hx : c.tape x = true) (hy : c.tape y = true) :
    y-x < 2*(n : Int) := by
  have hleft : -(n : Int) ≤ x := marked_left_below_steps m n c h x hx
  have hright : y < (n : Int) := marked_right_below_steps m n c h y hy
  omega

/-- A halting machine's elapsed moves exceed half the distance between
    any two marked cells witnessed earlier. No exact halt-time evaluation
    is required. -/
theorem halt_time_from_marked_span (m : Machine) (n k : Nat)
    (c : Config) (h : run m n blank = some c) (halt : HaltsAfter m k)
    (x y : Int) (hx : c.tape x = true) (hy : c.tape y = true) :
    y-x < 2*(k : Int) := by
  have hspan := marked_span_below_steps m n c h x y hx hy
  have ht := halt_time_at_least_checkpoint m n k c h halt
  omega

/-- A certificate expressed in coordinates relative to the head is enough
    to prove a strict lower bound on the final Busy Beaver score k+1. -/
theorem halt_score_from_relative_marks (m : Machine) (n k d : Nat)
    (c : Config) (h : run m n blank = some c) (halt : HaltsAfter m k)
    (a : Int) (hfirst : c.tape (c.head+a) = true)
    (hlast : c.tape (c.head+a+(d : Int)) = true) :
    d < 2*(k+1) := by
  have hs := halt_time_from_marked_span m n k c h halt
    (c.head+a) (c.head+a+(d:Int)) hfirst hlast
  omega

/-- A two-cell certificate for the right-hand unary counter pattern of
    Coq BusyCoq's TM63 S1 macro. The source macro itself must still be
    bridged to the Lean tape semantics before this hypothesis is usable. -/
def RightCounterMarkers (b : Nat) (c : Config) : Prop :=
  c.tape (c.head+2) = true ∧
  c.tape (c.head+9+3*(b:Int)) = true

/-- One live symbolic S1-counter checkpoint suffices to lower-bound the
    eventually halting machine's score, without evaluating its exact time. -/
theorem right_counter_score_lower (m : Machine) (b n k : Nat)
    (c : Config) (hrun : run m n blank = some c)
    (hmark : RightCounterMarkers b c) (hh : HaltsAfter m k) :
    3*b+7 < 2*(k+1) := by
  have hsource := halt_score_from_relative_marks m n k (3*b+7) c hrun hh
    2 (by exact hmark.1) (by
      have hloc : c.head+2+((3*b+7 : Nat):Int) =
        c.head+9+3*(b:Int) := by omega
      simpa only [hloc] using hmark.2)
  omega

/-- Conditional score attainability. The missing inputs are a genuine
    machine-specific live checkpoint and a halting witness, not implicit axioms. -/
theorem counter_checkpoint_attains_large_score (m : Machine) (b : Nat)
    (hreach : ∃ n c, run m n blank = some c ∧ RightCounterMarkers b c)
    (hhalt : ∃ k, HaltsAfter m k) :
    ∃ score, Attainable score ∧ 3*b+7 < 2*score := by
  obtain ⟨n,c,hrun,hmark⟩ := hreach
  obtain ⟨k,hk⟩ := hhalt
  refine ⟨k+1, ⟨m,k,hk,rfl⟩, ?_⟩
  exact right_counter_score_lower m b n k c hrun hmark hk

#print axioms run_within
#print axioms marked_right_below_steps
#print axioms marked_left_below_steps
#print axioms halt_time_at_least_checkpoint
#print axioms attained_score_gt_marked_right
#print axioms marked_span_below_steps
#print axioms halt_time_from_marked_span
#print axioms halt_score_from_relative_marks
#print axioms right_counter_score_lower
#print axioms counter_checkpoint_attains_large_score
end BB6Coverage.Agent24Speed
