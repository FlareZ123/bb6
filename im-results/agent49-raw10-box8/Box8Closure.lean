import Raw10EncodedSourceBridge
import BlockFARBridge
import Box8Sweep
import SideCycle
import FiniteHalting
import WeightedFirstOneCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent49Box8
open BB6Coverage BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent49BoxEncoded BB6.Agent17Raw10BoxFar
open BB6.Agent13BlankDelay

def fixed : List (Fin 25) := [8,14,11,7,17,4,9,2,23,15]

def encodedBox : Box (Fin 12) (Fin 25) := fun s =>
  if s.val < 10 then [fixed[s.val]!]
  else if s.val = 10 then (List.finRange 25).filter (· != 16)
  else List.finRange 25

def box : Box Slot Transition := fun s =>
  (encodedBox (slotIndex s)).map decodeCode

theorem encoded_exact : ∀ s : Fin 12, boxes[8]! s = encodedBox s := by
  decide +kernel

theorem source_exact : raw10Remainder[8]! = box := by
  funext s
  have h := exact_box_at_index (8 : Fin 34) s
  change raw10Remainder[8]! s = (boxes[8]! (slotIndex s)).map decodeCode at h
  rw [h, encoded_exact]
  rfl

/-- F0=0 is an assigned halt, not a wildcard; F1 is explicitly optional. -/
def partial (c : Fin 25) (f1 : Option Transition) : PartialMachine := fun s =>
  if (slotIndex s).val < 10 then some (decodeCode fixed[(slotIndex s).val]!)
  else if (slotIndex s).val = 10 then some (decodeCode c)
  else f1

private theorem index10 : ∀ s : Slot, (slotIndex s).val = 10 → s = (5,false) := by decide
private theorem index11 : ∀ s : Slot, 10 < (slotIndex s).val → s = (5,true) := by decide
private theorem fixed_ordinary : ∀ s : Slot, (slotIndex s).val < 10 →
    decodeCode fixed[(slotIndex s).val]! ≠ none := by decide
private theorem decode_nonzero : ∀ c : Fin 25, c ≠ 0 → decodeCode c ≠ none := by decide

theorem compatible_of_fits (m : Machine) (hm : Fits box m) (c : Fin 25)
    (hc : m (5,false) = decodeCode c) (f1 : Option Transition)
    (hf : ∀ t, f1 = some t → m (5,true) = t) :
    compatible (partial c f1) m := by
  intro s t hp
  by_cases hi : (slotIndex s).val < 10
  · have hmem := hm s
    change m s ∈ (encodedBox (slotIndex s)).map decodeCode at hmem
    simp only [encodedBox, if_pos hi, List.map_cons, List.map_nil, List.mem_singleton] at hmem
    simp only [partial, if_pos hi, Option.some.injEq] at hp
    exact hmem.trans hp
  · by_cases ht : (slotIndex s).val = 10
    · simp only [partial, if_neg hi, if_pos ht, Option.some.injEq] at hp
      rw [index10 s ht,hc,hp]
    · simp only [partial, if_neg hi, if_neg ht] at hp
      rw [index11 s (by omega)]
      exact hf t hp

theorem code_of_fits (m : Machine) (hm : Fits box m) :
    ∃ c : Fin 25, c ≠ 16 ∧ m (5,false) = decodeCode c := by
  have h := hm (5,false)
  change m (5,false) ∈ ((List.finRange 25).filter (· != 16)).map decodeCode at h
  obtain ⟨c,hc,he⟩ := List.mem_map.mp h
  exact ⟨c,by simpa using (List.mem_filter.mp hc).2,he.symm⟩

structure Witness where
  code : Fin 25
  entry : Nat
  period : Nat
  boundary : Int

def witnesses : List Witness := [
  ⟨2,7,5,-1⟩,⟨3,8,7,-2⟩,⟨4,3,8,2⟩,⟨5,8,4,-2⟩,
  ⟨6,8,5,-2⟩,⟨7,8,4,-2⟩,⟨8,8,6,-2⟩,⟨9,8,3,-2⟩,
  ⟨10,24,14,0⟩,⟨11,8,3,-2⟩,⟨13,7,4,-1⟩,⟨15,7,4,-1⟩,
  ⟨17,9,2,-3⟩,⟨18,6,5,0⟩,⟨19,9,2,-3⟩,⟨20,7,7,-1⟩,
  ⟨21,10,1,-4⟩,⟨23,10,1,-4⟩]

def check (w : Witness) : Bool :=
  decide (0 < w.period) &&
    BB6Coverage.Agent50SideCycle.finiteSideCycleCheck (partial w.code none)
      w.entry w.period false w.boundary

theorem witnesses_checked : witnesses.all check = true := by decide +kernel

theorem cycle_never (c : Fin 25) (hc : c ∈ witnesses.map Witness.code)
    (m : Machine) (hm : compatible (partial c none) m) : NeverHalts m := by
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hc
  have h := List.all_eq_true.mp witnesses_checked w hw
  have hs : 0 < w.period ∧
      BB6Coverage.Agent50SideCycle.finiteSideCycleCheck (partial w.code none)
        w.entry w.period false w.boundary = true := by
    simpa only [check,Bool.and_eq_true,decide_eq_true_eq] using h
  exact BB6Coverage.Agent50SideCycle.finiteSideCycleCheck_sound
    (partial w.code none) w.entry w.period false w.boundary hs.1 hs.2 m hm

theorem sweep_left_table : BB6BlockFAR.partialTable (BB6.Agent49Box8Sweep.machine false) =
    partial 1 none := by
  funext s
  exact (show ∀ s : Slot, BB6BlockFAR.partialTable (BB6.Agent49Box8Sweep.machine false) s =
    partial 1 none s by decide) s

theorem sweep_right_table : BB6BlockFAR.partialTable (BB6.Agent49Box8Sweep.machine true) =
    partial 14 none := by
  funext s
  exact (show ∀ s : Slot, BB6BlockFAR.partialTable (BB6.Agent49Box8Sweep.machine true) s =
    partial 14 none s by decide) s

theorem sweep_left_never (m : Machine) (hm : compatible (partial 1 none) m) : NeverHalts m :=
  BB6BlockFAR.transfer_never (BB6.Agent49Box8Sweep.machine false) m
    (by rwa [sweep_left_table]) (BB6.Agent49Box8Sweep.never false)

theorem sweep_right_never (m : Machine) (hm : compatible (partial 14 none) m) : NeverHalts m :=
  BB6BlockFAR.transfer_never (BB6.Agent49Box8Sweep.machine true) m
    (by rwa [sweep_right_table]) (BB6.Agent49Box8Sweep.never true)

theorem total_never (m : Machine) (h : ∀ s, m s ≠ none) : NeverHalts m := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    cases hr : run m n blank with
    | none => simp [hr] at ih
    | some c =>
      cases hs : m (readSlot c) with
      | none => exact False.elim (h _ hs)
      | some mv => simp [run,hr,rawStep,hs]

theorem ordinary_never (c : Fin 25) (hc0 : c ≠ 0) (m : Machine)
    (hm : Fits box m) (hc : m (5,false) = decodeCode c)
    (hf : m (5,true) ≠ none) : NeverHalts m := by
  apply total_never
  intro s
  by_cases hi : (slotIndex s).val < 10
  · have hmem := hm s
    change m s ∈ (encodedBox (slotIndex s)).map decodeCode at hmem
    simp only [encodedBox, if_pos hi, List.map_cons, List.map_nil, List.mem_singleton] at hmem
    rw [hmem]
    exact fixed_ordinary s hi
  · by_cases ht : (slotIndex s).val = 10
    · rw [index10 s ht,hc]
      exact decode_nonzero c hc0
    · rw [index11 s (by omega)]
      exact hf

theorem halt0_checked : finiteHaltCheck (partial 0 none) 10 = true := by decide +kernel
theorem halt12_checked : finiteHaltCheck (partial 12 (some none)) 32 = true := by decide +kernel
theorem halt22_checked : finiteHaltCheck (partial 22 (some none)) 11 = true := by decide +kernel
theorem halt24_checked : finiteHaltCheck (partial 24 (some none)) 11 = true := by decide +kernel

theorem partition : ∀ c : Fin 25, c ≠ 16 →
    c = 0 ∨ c = 1 ∨ c = 14 ∨ c = 12 ∨ c = 22 ∨ c = 24 ∨
      c ∈ witnesses.map Witness.code := by decide

theorem three_halt_slice (c : Fin 25) (hc : c = 12 ∨ c = 22 ∨ c = 24)
    (m : Machine) (hm : Fits box m) (hcode : m (5,false) = decodeCode c) :
    WeightedBound 38 m := by
  cases hf : m (5,true) with
  | some mv =>
    exact weighted_of_never 38 m (ordinary_never c (by rcases hc with rfl|rfl|rfl <;> decide)
      m hm hcode (by simp [hf]))
  | none =>
    have hp := compatible_of_fits m hm c hcode (some none) (by
      intro t ht
      have h : (none : Transition) = t := Option.some.inj ht
      simpa [← h] using hf)
    apply weighted_of_margin 38 m _ (by decide)
    rcases hc with rfl|rfl|rfl
    · exact (finiteHaltCheck_sound _ 32 33 (by decide) halt12_checked).sound m hp
    · exact (finiteHaltCheck_sound _ 11 33 (by decide) halt22_checked).sound m hp
    · exact (finiteHaltCheck_sound _ 11 33 (by decide) halt24_checked).sound m hp

/-- All 600 original box-8 completions, including the actual F0=0 slice.
    The ordinary live-step ceiling is 32; final halt and blank delay give 38. -/
theorem box8_bound (m : Machine) (hm : Fits box m) : WeightedBound 38 m := by
  obtain ⟨c,hc,hcode⟩ := code_of_fits m hm
  have hp := compatible_of_fits m hm c hcode none (by simp)
  rcases partition c hc with h0|h1|h14|h12|h22|h24|hcycles
  · subst c
    exact weighted_of_margin 38 m ((finiteHaltCheck_sound _ 10 33 (by decide)
      halt0_checked).sound m hp) (by decide)
  · subst c
    exact weighted_of_never 38 m (sweep_left_never m hp)
  · subst c
    exact weighted_of_never 38 m (sweep_right_never m hp)
  · exact three_halt_slice c (Or.inl h12) m hm hcode
  · exact three_halt_slice c (Or.inr (Or.inl h22)) m hm hcode
  · exact three_halt_slice c (Or.inr (Or.inr h24)) m hm hcode
  · exact weighted_of_never 38 m (cycle_never c hcycles m hp)

theorem original_box8_bound (m : Machine) (hm : Fits raw10Remainder[8]! m) :
    WeightedBound 38 m := box8_bound m (by simpa [source_exact] using hm)

#print axioms encoded_exact
#print axioms source_exact
#print axioms witnesses_checked
#print axioms sweep_left_never
#print axioms sweep_right_never
#print axioms box8_bound
#print axioms original_box8_bound

end BB6.Agent49Box8
