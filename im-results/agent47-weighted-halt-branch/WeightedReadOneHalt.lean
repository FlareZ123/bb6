import WeightedTNFCertificate

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace BB6.Agent47WeightedHalt

open BB6Coverage
open BB6.Agent13BlankDelay

/-- Six states imply every incoming zero-prefix delay is at most five.
    Thus a first-hole halt after n ordinary moves is weighted-safe whenever
    n+6 <= B, without enumerating the possible delays. -/
theorem first_hole_weighted_halt_of_margin
    (B n : Nat) (p : PartialMachine) (c : Config)
    (hroot : p initialSlot = some (some ⟨true, true, 1⟩))
    (hrun : knownRun p n = some c)
    (hhole : p (readSlot c) = none)
    (hmargin : n + 6 <= B) :
    ∀ m, compatible (refine p (readSlot c) none) m → WeightedBound B m := by
  apply first_hole_weighted_halt B p n c hroot hrun hhole
  intro d hd
  have hmem : d ∈ List.range 6 := (List.mem_filter.mp hd).1
  have hlt : d < 6 := List.mem_range.mp hmem
  omega

/-- Parent at the genuine read-one first hole: A/0=1RB and B/0=0LA. -/
def readOneParent : PartialMachine := fun slot =>
  if slot = (⟨0, by decide⟩, false) then
    some (some ⟨true, true, ⟨1, by decide⟩⟩)
  else if slot = (⟨1, by decide⟩, false) then
    some (some ⟨false, false, ⟨0, by decide⟩⟩)
  else none

/-- After the two assigned moves the head is back at A over the marked one. -/
def readOneAfterTwo : Config :=
  { state := ⟨0, by decide⟩
    head := 0
    tape := fun x => if x = 0 then true else false }

theorem readOneAfterTwo_readSlot :
    readSlot readOneAfterTwo = (⟨0, by decide⟩, true) := by
  rfl

/-- The A/1 halt child of the parent. -/
def readOneHalter : PartialMachine :=
  refine readOneParent (readSlot readOneAfterTwo) none

theorem readOneParent_root :
    readOneParent initialSlot = some (some ⟨true, true, 1⟩) := by
  simp [readOneParent, initialSlot]

theorem readOneParent_run :
    knownRun readOneParent 2 = some readOneAfterTwo := by
  simp [knownRun, knownStep, readOneParent, readOneAfterTwo,
    readSlot, applyMove, blank, initialSlot]
  funext x
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;> simp [h0, h1]

theorem readOneParent_hole :
    readOneParent (readSlot readOneAfterTwo) = none := by
  rw [readOneAfterTwo_readSlot]
  simp [readOneParent]

theorem readOneHalter_root :
    readOneHalter initialSlot = some (some ⟨true, true, 1⟩) := by
  simp [readOneHalter, refine, readOneParent, initialSlot,
    readOneAfterTwo_readSlot]

theorem readOneHalter_hole_is_halt :
    readOneHalter (readSlot readOneAfterTwo) = some none := by
  simp [readOneHalter, refine]

/-- The fixed B/0=0LA edge already gives an incoming zero delay of one. -/
theorem readOneHalter_delay_one :
    1 ∈ possibleDelays readOneHalter 0 := by
  let m : Machine := weightedTNFDefaultCompletion readOneHalter
  have hm : compatible readOneHalter m :=
    weightedTNFDefaultCompletion_compatible readOneHalter
  have hterm : ∀ m', compatible readOneHalter m' → zeroNext m' 0 = none := by
    intro m' hm'
    exact firstOne_terminal readOneHalter readOneHalter_root m' hm'
  have hz0 : zeroNext m 0 = none := hterm m hm
  have hz1 : zeroNext m 1 = some 0 := by
    simp [zeroNext, m, weightedTNFDefaultCompletion,
      readOneHalter, readOneParent, refine, readOneAfterTwo_readSlot]
  have hp : TerminalPath (zeroNext m) 1 1 0 :=
    TerminalPath.step hz1 (TerminalPath.stop 0 hz0)
  have hd : 1 ∈ delays (zeroNext m) 0 :=
    (mem_delays_iff hz0).mpr ⟨1, hp⟩
  exact (possible_delay_iff readOneHalter 0 1 hterm).mpr ⟨m, hm, hd⟩

/-- The four free zero rows C,D,E,F can extend the fixed B->A edge to
    the simple five-step incoming path F->E->D->C->B->A. -/
theorem readOneHalter_path_five :
    SimplePath readOneHalter 0 [5, 4, 3, 2, 1, 0] := by
  apply SimplePath.step
  · simp [mayZero, readOneHalter, readOneParent, refine, readOneAfterTwo, readOneAfterTwo_readSlot]
  · decide
  · apply SimplePath.step
    · simp [mayZero, readOneHalter, readOneParent, refine, readOneAfterTwo, readOneAfterTwo_readSlot]
    · decide
    · apply SimplePath.step
      · simp [mayZero, readOneHalter, readOneParent, refine, readOneAfterTwo, readOneAfterTwo_readSlot]
      · decide
      · apply SimplePath.step
        · simp [mayZero, readOneHalter, readOneParent, refine, readOneAfterTwo, readOneAfterTwo_readSlot]
        · decide
        · apply SimplePath.step
          · simp [mayZero, readOneHalter, readOneParent, refine, readOneAfterTwo, readOneAfterTwo_readSlot]
          · decide
          · exact SimplePath.stop

theorem readOneHalter_delay_five :
    5 ∈ possibleDelays readOneHalter 0 := by
  have hpath : [5, 4, 3, 2, 1, 0] ∈ pathsTo readOneHalter 0 5 :=
    path_mem_pathsTo readOneHalter_path_five
  have hnonempty : pathsTo readOneHalter 0 5 ≠ [] :=
    List.ne_nil_of_mem hpath
  simp [possibleDelays, hnonempty]

/-- The exact halt-branch threshold is eight: n=2 and maximal delay d=5. -/
theorem readOneHalter_weight_threshold (B : Nat) :
    (∀ d ∈ possibleDelays readOneHalter 0, d + 2 + 1 <= B) ↔ 8 <= B := by
  constructor
  · intro h
    have h5 := h 5 readOneHalter_delay_five
    omega
  · intro hB d hd
    have hmem : d ∈ List.range 6 := (List.mem_filter.mp hd).1
    have hlt : d < 6 := List.mem_range.mp hmem
    omega

theorem readOneHalter_raw_halts (m : Machine)
    (hm : compatible readOneHalter m) : HaltsAfter m 2 := by
  exact first_hole_halts readOneParent 2 readOneAfterTwo
    readOneParent_run readOneParent_hole m (by simpa [readOneHalter] using hm)

theorem readOneHalter_raw_cover :
    Cover (DecidedBelow 3) readOneHalter := by
  apply Cover.leaf readOneHalter
  intro m hm
  exact Or.inr ⟨2, by decide, readOneHalter_raw_halts m hm⟩

/-- The raw score-three cover is not a weighted-bound-three leaf: re-rooting
    at B makes the same suffix a four-step blank-start halter. -/
theorem readOneHalter_not_weighted_three :
    ¬ (∀ m, compatible readOneHalter m → WeightedBound 3 m) := by
  intro h
  let m : Machine := weightedTNFDefaultCompletion readOneHalter
  have hm : compatible readOneHalter m :=
    weightedTNFDefaultCompletion_compatible readOneHalter
  have hh := readOneHalter_raw_halts m hm
  have hz0 : zeroNext m 0 = none :=
    firstOne_terminal readOneHalter readOneHalter_root m hm
  have hz1 : zeroNext m 1 = some 0 := by
    simp [zeroNext, m, weightedTNFDefaultCompletion,
      readOneHalter, readOneParent, refine, readOneAfterTwo_readSlot]
  have hp : TerminalPath (zeroNext m) 1 1 0 :=
    TerminalPath.step hz1 (TerminalPath.stop 0 hz0)
  have hd : 1 ∈ delays (zeroNext m) 0 :=
    (mem_delays_iff hz0).mpr ⟨1, hp⟩
  have hbound := h m hm 2 1 hh hd
  omega

/-- For B>=8 the read-one halt child is a valid weighted leaf. -/
theorem readOneHalter_weighted (B : Nat) (hB : 8 <= B) :
    ∀ m, compatible readOneHalter m → WeightedBound B m := by
  apply first_hole_weighted_halt_of_margin B 2 readOneParent readOneAfterTwo
  · exact readOneParent_root
  · exact readOneParent_run
  · exact readOneParent_hole
  · omega

theorem readOneHalter_weighted_cover (B : Nat) (hB : 8 <= B) :
    Cover (WeightedBound B) readOneHalter :=
  .leaf readOneHalter (readOneHalter_weighted B hB)

#print axioms first_hole_weighted_halt_of_margin
#print axioms readOneParent_run
#print axioms readOneHalter_delay_one
#print axioms readOneHalter_delay_five
#print axioms readOneHalter_weight_threshold
#print axioms readOneHalter_raw_halts
#print axioms readOneHalter_raw_cover
#print axioms readOneHalter_not_weighted_three
#print axioms readOneHalter_weighted
#print axioms readOneHalter_weighted_cover

end BB6.Agent47WeightedHalt
