import EntryMacroLeft
import Lean.Elab.Tactic.Omega

namespace BB6Coverage

/-- A frontier carries precisely one marker at the current head position,
    followed by zeros in all strictly later positions. -/
def markerPattern (x : Int) : Bool := decide (x = 0)

def markedSeed : FinRayCfg :=
  { state := 2, head := 0, ones := [0] }

def shiftedMarkedSeed : FinRayCfg :=
  { state := 2, head := 1, ones := [1] }

theorem embed_markedSeed :
    embedFinRay markedSeed = tailSeed 2 markerPattern := by
  apply congrArg (fun tape : Int → Bool =>
    ({state := 2, head := 0, tape := tape} : Config))
  funext x
  change ([0] : List Int).contains x =
    (if 0 <= x then markerPattern x else false)
  by_cases hx : x = 0
  · subst x
    decide
  · by_cases hpos : 0 <= x
    · simp [markerPattern, hx, hpos]
    · simp [markerPattern, hx, hpos]

theorem shifted_marked_tail (x : Int) (hx : 1 <= x) :
    (embedFinRay shiftedMarkedSeed).tape x =
      markerPattern (x-1) := by
  change ([1] : List Int).contains x = decide (x-1=0)
  by_cases hone : x = 1
  · subst x
    decide
  · have hother : x-1 ≠ 0 := by omega
    simp [hone, hother]

/-- Blank start enters marked state C after A0, B0; then C carries the
    single marker one cell right per three ordinary machine steps. -/
def markedTailPump : PartialMachine := fun slot =>
  if slot = (0,false) then some (some ⟨true,true,1⟩)
  else if slot = (1,false) then some (some ⟨false,false,2⟩)
  else if slot = (2,true) then some (some ⟨false,true,3⟩)
  else if slot = (3,false) then some (some ⟨true,false,4⟩)
  else if slot = (4,false) then some (some ⟨false,true,2⟩)
  else none

theorem marked_entry_check :
    finitePartialRun markedTailPump 2 finiteBlank = some markedSeed := by rfl

theorem marked_macro_check :
    finitePartialRun markedTailPump 3 markedSeed =
      some shiftedMarkedSeed := by rfl

theorem marked_window_check :
    (List.range 3).all (fun k =>
      match finitePartialRun markedTailPump k markedSeed with
      | none => false
      | some d => decide (0 <= d.head)) = true := by decide

theorem markedTailPump_nonhalting (bound : Nat) :
    Cover (DecidedBelow bound) markedTailPump := by
  apply Cover.leaf
  intro m hm
  left
  apply entry_tail_pattern_never m 2 markerPattern 2 3 1
    (by decide) (by decide)
  · refine ⟨embedFinRay markedSeed, ?_, ?_⟩
    · simpa only [embedFinRay_blank] using
        (finitePartialRun_sound markedTailPump m hm
          finiteBlank markedSeed 2 marked_entry_check)
    · rw [embed_markedSeed]
      constructor
      · rfl
      · intro x hx
        change (if 0 <= x then markerPattern x else false) =
          markerPattern (x-0)
        have hge : 0 ≤ x := by simpa only [tailSeed] using hx
        simpa only [if_pos hge, Int.sub_zero]
  · refine ⟨embedFinRay shiftedMarkedSeed, ?_, ?_, ?_, ?_⟩
    · simpa only [embed_markedSeed] using
        (finitePartialRun_sound markedTailPump m hm
          markedSeed shiftedMarkedSeed 3 marked_macro_check)
    · rfl
    · rfl
    · exact shifted_marked_tail
  · intro k hk d hrun
    have hflag :
        (match finitePartialRun markedTailPump k markedSeed with
        | none => false
        | some t => decide (0 <= t.head)) = true :=
      (List.all_eq_true.mp marked_window_check) k (List.mem_range.mpr hk)
    cases hfin : finitePartialRun markedTailPump k markedSeed with
    | none =>
        simp [hfin] at hflag
    | some t =>
        have hge : 0 <= t.head :=
          of_decide_eq_true (by simpa [hfin] using hflag)
        have hsource :
            run m k (tailSeed 2 markerPattern) =
              some (embedFinRay t) := by
          simpa only [embed_markedSeed] using
            (finitePartialRun_sound markedTailPump m hm
              markedSeed t k hfin)
        have heq : d = embedFinRay t :=
          Option.some.inj (hrun.symm.trans hsource)
        subst d
        simpa [embedFinRay] using hge

/-- The old fresh-blank entry oracle cannot see the carried marker. -/
theorem markedTailPump_fresh_entry_reject :
    finiteEntryMacroBiOracle markedTailPump 6 6 = false := by decide

#print axioms markedTailPump_nonhalting

end BB6Coverage
