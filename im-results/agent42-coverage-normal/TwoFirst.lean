import FirstStep
import Prune
import WriteOneDrift

namespace BB6Coverage

/-- The two nontrivial canonical first actions, both from blank A/0 to B. -/
def TwoFirst (m : Machine) : Prop :=
  m initialSlot = some ⟨false, true, (1 : Fin 6)⟩ ∨
  m initialSlot = some ⟨true, true, (1 : Fin 6)⟩

private theorem no_halt_if_live (m : Machine) (n : Nat)
    (hlive : NeverHalts m) (hh : HaltsAfter m n) : False := by
  have hs := hlive (n+1)
  rw [hh.2] at hs
  simp at hs

/-- A halting computation with at least one successful move cannot use any
    of the three trivial first instructions of FirstStep's canonical set. -/
theorem positive_halter_two_first (m : Machine) (n : Nat)
    (hn : 0 < n) (hh : HaltsAfter m n) :
    ∃ m' : Machine,
      TwoFirst m' ∧ (∀ k, HaltsAfter m' k ↔ HaltsAfter m k) := by
  obtain ⟨m', hequiv, hc⟩ := normalize_first m
  have hh' : HaltsAfter m' n := (hequiv n).mpr hh
  rcases hc with hhalt | ⟨w,hself⟩ | ⟨w,hother⟩
  · have hzero : HaltsAfter m' 0 := by
      constructor
      · rfl
      · simp [run, rawStep, blank_reads_initial, hhalt]
    have h_eq := halting_time_unique m' n 0 hh' hzero
    omega
  · cases w with
    | false =>
      have hlive : NeverHalts m' := by
        apply blankDrift_never m' true
        simpa [blankDrift] using hself
      exact False.elim (no_halt_if_live m' n hlive hh')
    | true =>
      have hlive : NeverHalts m' := by
        apply writeOneRight_never m'
        simpa [writeOneRight] using hself
      exact False.elim (no_halt_if_live m' n hlive hh')
  · refine ⟨m', ?_, hequiv⟩
    cases w with
    | false => exact Or.inl hother
    | true => exact Or.inr hother

/-- The only cases relevant for upper bounding halting scores >=2 are
    the two nontrivial canonical first moves. The score-one halt is handled
    explicitly, with no implicit finite-program or reachability assumption. -/
theorem upper_from_two_first_actions (B : Nat) (hb : 1 ≤ B)
    (h : ∀ m : Machine, TwoFirst m →
      ∀ n, HaltsAfter m n → n+1 ≤ B) :
    ∀ m n, HaltsAfter m n → n+1 ≤ B := by
  intro m n hh
  by_cases hn : n = 0
  · subst n
    simpa using hb
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨m', htwo, hequiv⟩ := positive_halter_two_first m n hpos hh
    exact h m' htwo n ((hequiv n).mpr hh)

#print axioms positive_halter_two_first
#print axioms upper_from_two_first_actions
end BB6Coverage
