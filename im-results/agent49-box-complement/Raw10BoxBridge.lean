import BoxComplement
import Root109Membership
import Canonical78Roster

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent49BoxBridge
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50RootFrontier
open BB6.Agent49Box BB6.Agent13CrossRouteHeldLeaf109

def slots : List Slot :=
  (List.finRange 6).flatMap fun q => [false,true].map fun b => (q,b)

theorem slots_complete (s : Slot) : s ∈ slots := by
  rcases s with ⟨q,b⟩
  have hb : b ∈ [false,true] := by cases b <;> simp
  exact List.mem_flatMap.mpr
    ⟨q, List.mem_finRange q, List.mem_map.mpr ⟨b,hb,rfl⟩⟩

def transitions : List Transition := none :: allMoves.map some

theorem transitions_complete (t : Transition) : t ∈ transitions := by
  cases t with
  | none => simp [transitions]
  | some mv =>
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨mv,allMoves_complete mv,rfl⟩)

def boxOf (p : PartialMachine) : Box Slot Transition :=
  fun s => match p s with
  | none => transitions
  | some t => [t]

theorem fits_boxOf (p : PartialMachine) (m : Machine) :
    Fits (boxOf p) m ↔ compatible p m := by
  constructor
  · intro h s t ht
    have hs := h s
    simpa [boxOf, ht] using hs
  · intro h s
    cases hp : p s with
    | none => simpa [boxOf, hp] using transitions_complete (m s)
    | some t => simpa [boxOf, hp] using h s t hp

def cubeOf (p : PartialMachine) : Cube Slot Transition :=
  slots.filterMap fun s => (p s).map fun t => (s,t)

theorem matches_cubeOf (p : PartialMachine) (m : Machine) :
    Matches (cubeOf p) m ↔ compatible p m := by
  constructor
  · intro h s t ht
    exact h (s,t) (List.mem_filterMap.mpr ⟨s,slots_complete s,by simp [ht]⟩)
  · intro h x hx
    obtain ⟨s, _, hs⟩ := List.mem_filterMap.mp hx
    cases hp : p s with
    | none => simp [hp] at hs
    | some t =>
      have he : (s,t) = x := by simpa [hp] using hs
      subst x
      exact h s t hp

/-- Exact residual rectangles for a parent after arbitrary certified
    cylinders, even when their fixed rows overlap or appear out of order. -/
def remainder (p : PartialMachine) (ps : List PartialMachine) :
    List (Box Slot Transition) :=
  subtractMany slots [boxOf p] (ps.map cubeOf)

theorem remainder_exact (p : PartialMachine) (ps : List PartialMachine)
    (m : Machine) :
    (∃ r ∈ remainder p ps, Fits r m) ↔
      compatible p m ∧ ∀ q ∈ ps, ¬ compatible q m := by
  rw [remainder, subtractMany_exact]
  constructor
  · rintro ⟨⟨b, hb, hm⟩, hn⟩
    have he : b = boxOf p := by simpa using hb
    subst b
    exact ⟨(fits_boxOf p m).mp hm, fun q hq hc =>
      hn (cubeOf q) (List.mem_map.mpr ⟨q,hq,rfl⟩) ((matches_cubeOf q m).mpr hc)⟩
  · rintro ⟨hp, hn⟩
    refine ⟨⟨boxOf p, by simp, (fits_boxOf p m).mpr hp⟩, ?_⟩
    intro c hc hm
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
    exact hn q hq ((matches_cubeOf q m).mp hm)

theorem remainder_disjoint (p : PartialMachine) (ps : List PartialMachine) :
    (remainder p ps).Pairwise Disjoint :=
  subtractMany_disjoint slots _ _ (by simp)

/-- Consuming theorem uses the existing Cover interface and its existing
    weighted score predicate; no change to the machine step convention. -/
def coverFromRemainder (B : Nat) (p : PartialMachine) (ps : List PartialMachine)
    (hclosed : ∀ q ∈ ps, ∀ m, compatible q m → WeightedBound B m)
    (hopen : ∀ r ∈ remainder p ps, ∀ m, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) p :=
  Cover.leaf p (fun m hm => consume slots (boxOf p) (ps.map cubeOf)
    (WeightedBound B)
    (fun c hc m' hmatch => by
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
      exact hclosed q hq m' ((matches_cubeOf q m').mp hmatch))
    hopen m ((fits_boxOf p m).mpr hm))

def sideTables : List PartialMachine :=
  b0_1lcSideWitnesses.map fun w => unpackTable w.table

def held : PartialMachine := toPartialMachine BB6CrossRouteHeldLeaf.heldTable

def raw10Remainder : List (Box Slot Transition) :=
  remainder firstOneB0_1LC (sideTables ++ [held])

theorem raw10_remainder_exact (m : Machine) :
    (∃ r ∈ raw10Remainder, Fits r m) ↔
    compatible firstOneB0_1LC m ∧
      (∀ w ∈ b0_1lcSideWitnesses, ¬ compatible (unpackTable w.table) m) ∧
      ¬ compatible held m := by
  rw [raw10Remainder, remainder_exact]
  simp only [List.mem_append, sideTables, List.mem_map, List.mem_singleton]
  constructor
  · rintro ⟨hp, hn⟩
    exact ⟨hp, fun w hw => hn _ (Or.inl ⟨w,hw,rfl⟩),
      hn held (Or.inr rfl)⟩
  · rintro ⟨hp, hs, hh⟩
    refine ⟨hp, ?_⟩
    intro q hq
    rcases hq with ⟨w,hw,rfl⟩ | rfl
    · exact hs w hw
    · exact hh

theorem raw10_remainder_disjoint : raw10Remainder.Pairwise Disjoint :=
  remainder_disjoint _ _

/-- No claim is made that the Coq FARv3 held result is already connected
    to this Lean predicate: the precise missing bridge is hHeld. -/
def raw10_cover (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ r ∈ raw10Remainder, ∀ m, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  coverFromRemainder B firstOneB0_1LC (sideTables ++ [held])
    (fun q hq m hm => by
      rcases List.mem_append.mp hq with hs | hh
      · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hs
        have hb := b0_1lcSideWitnesses_safe w hw m hm
        intro k d hk hd
        exact Nat.le_trans (hb k d hk hd) hB
      · have he : q = held := by simpa using hh
        subst q
        exact hHeld m hm)
    hOpen

/-- Consume the exact residual rectangles in the current canonical
    score-B upper bound. Every other quotient entry remains an obligation. -/
theorem exact_from_raw10_remainder (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ r ∈ raw10Remainder, ∀ m, Fits r m → WeightedBound B m)
    (hOther : ∀ e ∈ BB6.Agent47Canonical78.roster,
      e.2 ≠ firstOneB0_1LC → Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B := by
  apply BB6.Agent47Canonical78.exact_at_target B hB _ champ
  intro e he
  by_cases h : e.2 = firstOneB0_1LC
  · rw [h]
    exact raw10_cover B hB hHeld hOpen
  · exact hOther e he h

#print axioms remainder_exact
#print axioms remainder_disjoint
#print axioms raw10_remainder_exact
#print axioms raw10_cover
#print axioms exact_from_raw10_remainder
end BB6.Agent49BoxBridge
