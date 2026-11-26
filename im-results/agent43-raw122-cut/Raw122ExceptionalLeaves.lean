import Raw122SharpLate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent43Raw122Exceptional
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent29PackedRun
open BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole
open BB6.Agent10ZipAudit BB6.Agent47PartialAudit BB6Coverage.Agent10ZipAudit
open BB6.Agent43Raw122Sharp

/-- All rows except one are fixed ordinary instructions. A halting
completion therefore has exactly one possible table: halt at the hole. -/
theorem oneHole_halter_unique (p : PartialMachine) (s : Slot)
    (hrest : ∀ t, t ≠ s → ∃ mv, p t = some (some mv))
    (hu : p s = none) (m : Machine) (hm : compatible p m)
    (k : Nat) (hk : HaltsAfter m k) : m = fun t => (p t).getD none := by
  have hs : m s = none := by
    cases he : m s with
    | none => rfl
    | some mv =>
      have hn := all_ordinary_never m (by
        intro t
        by_cases ht : t = s
        · subst t
          exact ⟨mv, he⟩
        · obtain ⟨mv', hmv'⟩ := hrest t ht
          exact ⟨mv', hm t (some mv') hmv'⟩)
      have hbad := hn (k+1)
      rw [hk.2] at hbad
      contradiction
  funext t
  by_cases ht : t = s
  · subst t
    simp [hu, hs]
  · obtain ⟨mv, hmv⟩ := hrest t ht
    simpa [hmv] using hm t (some mv) hmv

def second : Machine := fun s => (late1 s).getD none

theorem second_compatible : compatible late1 second := by
  intro s t h
  simp [second,h]

theorem second_parent_compatible : compatible BB6.Agent43Raw122.parent second := by
  intro s t h
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first | contradiction | (cases h; rfl)

theorem second_ne_longest : second ≠ longest := by
  intro h
  have hn : second (0,true) ≠ longest (0,true) := by decide
  exact hn (congrFun h (0,true))

theorem second_halts : HaltsAfter second 1296924 := by
  have hread := late1_read
  rw [zipRead_eq] at hread
  cases hr : knownRun late1 1296924 with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = (1,true) := by simpa [hr] using hread
    have hrun := knownRun_sound late1 second second_compatible 1296924 c hr
    constructor
    · change (run second 1296924 blank).isSome = true
      rw [hrun]
      rfl
    · rw [run,hrun]
      have hh : second (1,true) = none := by decide
      simp [rawStep,hs,hh]

theorem second_delay : 1 ∈ delays (zeroNext second) 0 := by decide

theorem second_zero_delay : 0 ∈ delays (zeroNext second) 0 := by decide

private theorem late0_rest : ∀ s : Slot, s ≠ (0,true) → ∃ mv, late0 s = some (some mv) := by
  intro ⟨q,b⟩ hs
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first | exact False.elim (hs rfl) | exact ⟨_,rfl⟩

private theorem late1_rest : ∀ s : Slot, s ≠ (1,true) → ∃ mv, late1 s = some (some mv) := by
  intro ⟨q,b⟩ hs
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first | exact False.elim (hs rfl) | exact ⟨_,rfl⟩

theorem late0_halter_unique (m : Machine) (hm : compatible late0 m) (k : Nat)
    (hk : HaltsAfter m k) : m = longest :=
  oneHole_halter_unique late0 (0,true) late0_rest (by decide) m hm k hk

theorem late1_halter_unique (m : Machine) (hm : compatible late1 m) (k : Nat)
    (hk : HaltsAfter m k) : m = second :=
  oneHole_halter_unique late1 (1,true) late1_rest (by decide) m hm k hk

theorem late0_other_bound (m : Machine) (hm : compatible late0 m) (hne : m ≠ longest) : WeightedBound 7014 m := by
  intro k d hk hd
  exact False.elim (hne (late0_halter_unique m hm k hk))

theorem late1_other_bound (m : Machine) (hm : compatible late1 m) (hne : m ≠ second) : WeightedBound 7014 m := by
  intro k d hk hd
  exact False.elim (hne (late1_halter_unique m hm k hk))

#print axioms oneHole_halter_unique
#print axioms late0_halter_unique
#print axioms late1_halter_unique
#print axioms second_halts
#print axioms second_delay
end BB6.Agent43Raw122Exceptional
