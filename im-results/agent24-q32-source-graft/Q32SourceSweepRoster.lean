import SweepPumping
import Q32SideLeafRoster

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent24Q32SourceSweeps

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent24Q32SideLeafRoster
open BB6.Agent31Pump
open BB6.Agent50TNFPilot
open BB6.Agent50TranslatedCycler

/-- Exact source machine used by the two SWsweep entries in
    Agent47SourceChunk2.v. The only parameter is E1: 1RB or 0RC. -/
def q32SweepMachine (v : Bool) : Machine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some ⟨true,true,1⟩
  | 0, true  => some ⟨true,true,3⟩
  | 1, false => some ⟨true,true,2⟩
  | 1, true  => some ⟨true,false,1⟩
  | 2, false => some ⟨false,false,0⟩
  | 2, true  => some ⟨false,false,4⟩
  | 3, false => some ⟨true,false,0⟩
  | 3, true  => some ⟨false,false,1⟩
  | 4, false => none
  | 4, true  => if v then some ⟨true,true,1⟩ else some ⟨false,true,2⟩
  | 5, false => none
  | 5, true  => none
  | _, _ => none

def q32SweepPartial (v : Bool) : PartialMachine :=
  sourcePartial (q32SweepMachine v)

def q32SweepOnes (n : Nat) : List Bool := rep [true] n

@[simp] theorem q32SweepOnes_succ (n : Nat) :
    q32SweepOnes (n+1) = true :: q32SweepOnes n := by
  simp [q32SweepOnes, rep]

theorem q32SweepOnes_two_more (n : Nat) :
    true :: true :: q32SweepOnes n = q32SweepOnes (n+2) := by
  rw [← q32SweepOnes_succ n, ← q32SweepOnes_succ (n+1)]

/-- The two source sweeps grow a block of ones to the left of the
    distinguished blank cell, returning to C0 with the same blank tail. -/
def q32SweepEnd (n : Nat) : Z0 :=
  ⟨2, false :: q32SweepOnes (n+1), []⟩

def q32SweepFamily (n : Nat) : Z0 := q32SweepEnd (n+1)

def q32SweepCost (v : Bool) (n : Nat) : Nat :=
  if v then 4*n+14 else 6*n+18

theorem q32SweepOpen (v : Bool) (n : Nat) :
    run0 (q32SweepPartial v) 5 (q32SweepEnd n) =
      some ⟨1, q32SweepOnes (n+1), [false]⟩ := by
  cases v <;>
    simp [run0, step0, move0, q32SweepPartial, sourcePartial,
      q32SweepMachine, q32SweepEnd, q32SweepOnes, rep]

theorem q32SweepLeft (v : Bool) (n : Nat) :
    run0 (q32SweepPartial v) (n+1)
      ⟨1, q32SweepOnes (n+1), [false]⟩ =
    some ⟨1, [], q32SweepOnes (n+1) ++ [false]⟩ := by
  simpa [q32SweepOnes] using
    (sweepL (q32SweepPartial v) 1 [] [] [true] [true] 1
      (by
        intro L R
        simp [run0, step0, move0, q32SweepPartial, sourcePartial,
          q32SweepMachine])
      (n+1) [] [false])

theorem q32SweepStepToC (v : Bool) (n : Nat) :
    run0 (q32SweepPartial v) 1
      ⟨1, [], q32SweepOnes (n+1) ++ [false]⟩ =
    some ⟨2, [true,true], q32SweepOnes n ++ [false]⟩ := by
  simp [run0, step0, move0, q32SweepPartial, sourcePartial,
    q32SweepMachine, q32SweepOnes_succ]

/-- A rightward sweep consumes one 1 in three steps for E1=1RB and
    five steps for E1=0RC. -/
theorem q32SweepCrossOne (v : Bool) (L R : List Bool) :
    run0 (q32SweepPartial v) (if v then 3 else 5)
      ⟨2, [true,true] ++ L, [true] ++ R⟩ =
    some ⟨2, [true,true,true] ++ L, R⟩ := by
  cases v <;>
    simp [run0, step0, move0, q32SweepPartial, sourcePartial,
      q32SweepMachine]

/-- The final crossing consumes the first blank and restores the C0
    configuration with a zero at the head. -/
theorem q32SweepCrossBlank (v : Bool) (L R : List Bool) :
    run0 (q32SweepPartial v) (if v then 3 else 5)
      ⟨2, [true,true] ++ L, [false] ++ R⟩ =
    some ⟨2, [false,true,true] ++ L, R⟩ := by
  cases v <;>
    simp [run0, step0, move0, q32SweepPartial, sourcePartial,
      q32SweepMachine]

theorem q32SweepRight (v : Bool) (n : Nat) :
    run0 (q32SweepPartial v) ((if v then 3 else 5)*n)
      ⟨2, [true,true], q32SweepOnes n ++ [false]⟩ =
    some ⟨2, [true,true] ++ q32SweepOnes n, [false]⟩ := by
  cases v with
  | true =>
      simpa [q32SweepOnes, List.append_assoc] using
        (sweepR (q32SweepPartial true) 2 [true,true] [] [true] [true] 3
          (by
            intro L R
            simpa [List.append_assoc] using q32SweepCrossOne true L R)
          n [] [false])
  | false =>
      simpa [q32SweepOnes, List.append_assoc] using
        (sweepR (q32SweepPartial false) 2 [true,true] [] [true] [true] 5
          (by
            intro L R
            simpa [List.append_assoc] using q32SweepCrossOne false L R)
          n [] [false])

theorem q32SweepFinish (v : Bool) (n : Nat) :
    run0 (q32SweepPartial v) (if v then 3 else 5)
      ⟨2, [true,true] ++ q32SweepOnes n, [false]⟩ =
    some ⟨2, false :: true :: true :: q32SweepOnes n, []⟩ := by
  cases v <;>
    simpa [List.append_assoc] using q32SweepCrossBlank v (q32SweepOnes n) []

theorem q32SweepGrowth (v : Bool) (n : Nat) :
    run0 (q32SweepPartial v) (q32SweepCost v n) (q32SweepFamily n) =
      some (q32SweepFamily (n+1)) := by
  have h1 := q32SweepOpen v (n+1)
  have h2 := q32SweepLeft v (n+1)
  have h3 := q32SweepStepToC v (n+1)
  have h4 := q32SweepRight v (n+1)
  have h5 := q32SweepFinish v (n+1)
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  have htime :
      5 + (n+2) + 1 + (if v then 3 else 5)*(n+1) +
        (if v then 3 else 5) = q32SweepCost v n := by
    cases v <;> simp [q32SweepCost] <;> omega
  rw [htime] at H
  simpa [q32SweepFamily, q32SweepEnd, q32SweepOnes_two_more] using H

theorem q32SweepEntry (v : Bool) :
    run0 (q32SweepPartial v) 2 ⟨0, [], []⟩ =
      some (q32SweepFamily 0) := by
  cases v <;>
    simp [run0, step0, move0, q32SweepPartial, sourcePartial,
      q32SweepMachine, q32SweepFamily, q32SweepEnd, q32SweepOnes, rep]

theorem q32SweepCostPositive (v : Bool) (n : Nat) :
    0 < q32SweepCost v n := by
  cases v <;> simp [q32SweepCost] <;> omega

theorem q32SweepNever (v : Bool) (m : Machine)
    (hm : compatible (q32SweepPartial v) m) : NeverHalts m :=
  never_of_growth (q32SweepPartial v) q32SweepFamily 2 (q32SweepCost v)
    (q32SweepEntry v) (q32SweepCostPositive v) (q32SweepGrowth v) m hm

theorem q32SweepRoot (v : Bool) :
    q32SweepPartial v initialSlot = some (some ⟨true,true,1⟩) := by
  decide

theorem q32SweepSupport (v : Bool) : TNFSupport (q32SweepPartial v) 6 := by
  intro s t _
  exact ⟨s.1.isLt, fun mv _ => mv.next.isLt⟩

/-- Kernel-checked nonhalting leaves for the two original source sweep
    cylinders. No Coq proof term is trusted by this Lean construction. -/
def q32SweepCertificate (v : Bool) :
    WeightedTNFCertificate 144 (q32SweepPartial v) 6 :=
  .nonhalt (q32SweepRoot v) (q32SweepSupport v)
    (sourcePartial_noAssignedHalt (q32SweepMachine v))
    (by
      intro m hm
      exact q32SweepNever v m hm)

theorem q32SweepTrueEncoding :
    encodeTable (q32SweepPartial true) =
      "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RB_------" := by
  decide

theorem q32SweepFalseEncoding :
    encodeTable (q32SweepPartial false) =
      "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RC_------" := by
  decide

structure Q32SweepData where
  index : Nat
  table : String
  holes : Nat
  sourceCut : Nat
  deriving DecidableEq

def q32SweepData : List Q32SweepData :=
  [⟨5, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RB_------", 3, 5⟩,
   ⟨7, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RC_------", 3, 5⟩]

def q32SweepDataMatches (d : Q32SweepData) : Bool :=
  match q32QueueData[d.index]? with
  | some row =>
      decide (row.table = d.table ∧ row.holes = d.holes ∧ row.cut = d.sourceCut)
  | none => false

theorem q32SweepData_sourceExact :
    q32SweepData.all q32SweepDataMatches = true := by
  decide

structure Q32SweepLeaf where
  data : Q32SweepData
  cylinder : PartialMachine
  certificate : WeightedTNFCertificate 144 cylinder 6
  encoding : encodeTable cylinder = data.table

def q32SweepTrueLeaf : Q32SweepLeaf :=
  { data := ⟨5, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---1RB_------", 3, 5⟩
    cylinder := q32SweepPartial true
    certificate := q32SweepCertificate true
    encoding := q32SweepTrueEncoding }

def q32SweepFalseLeaf : Q32SweepLeaf :=
  { data := ⟨7, "1RB1RD_1RC1LB_0LA0LE_1LA0LB_---0RC_------", 3, 5⟩
    cylinder := q32SweepPartial false
    certificate := q32SweepCertificate false
    encoding := q32SweepFalseEncoding }

def q32SweepLeaves : List Q32SweepLeaf :=
  [q32SweepTrueLeaf, q32SweepFalseLeaf]

theorem q32SweepLeaves_length : q32SweepLeaves.length = 2 := by
  decide

theorem q32SweepLeaves_data_exact :
    q32SweepLeaves.map Q32SweepLeaf.data = q32SweepData := by
  decide

theorem q32SweepLeaves_sourceExact :
    q32SweepLeaves.all (fun leaf => q32SweepDataMatches leaf.data) = true := by
  decide

theorem q32SweepLeaf_sound (leaf : Q32SweepLeaf) (m : Machine)
    (hm : compatible leaf.cylinder m) : WeightedBound 144 m :=
  leaf.certificate.sound m hm

theorem q32SweepLeaves_sound :
    ∀ leaf ∈ q32SweepLeaves, ∀ m, compatible leaf.cylinder m → WeightedBound 144 m := by
  intro leaf hmem m hm
  exact q32SweepLeaf_sound leaf m hm

def q32SweepLeafRefinesParent (leaf : Q32SweepLeaf) : Bool :=
  refinesCheck leaf.cylinder q32Parent

theorem q32SweepLeaves_refine_parent :
    q32SweepLeaves.all q32SweepLeafRefinesParent = true := by
  decide

theorem q32SweepLeaves_refine_parent_sound :
    ∀ leaf, leaf ∈ q32SweepLeaves → Refines leaf.cylinder q32Parent := by
  intro leaf hmem
  exact refinesCheck_sound leaf.cylinder q32Parent
    (List.all_eq_true.mp q32SweepLeaves_refine_parent leaf hmem)

/-- The complete original 34-entry q32 certificate roster: the 32
    translated SWside leaves and both original SWsweep leaves. -/
def q32Original34Leaves : List PartialMachine :=
  q32SideLeaves.map Q32SideLeaf.cylinder ++
    q32SweepLeaves.map Q32SweepLeaf.cylinder

theorem q32Original34Leaves_length : q32Original34Leaves.length = 34 := by
  simp [q32Original34Leaves, q32SideLeaves_length, q32SweepLeaves_length]

theorem q32Original34Leaves_sound :
    ∀ p ∈ q32Original34Leaves, ∀ m, compatible p m → WeightedBound 144 m := by
  intro p hp m hm
  simp only [q32Original34Leaves, List.mem_append] at hp
  rcases hp with hp | hp
  · rcases List.mem_map.mp hp with ⟨leaf, hleaf, rfl⟩
    exact q32SideLeaf_sound leaf m hm
  · rcases List.mem_map.mp hp with ⟨leaf, hleaf, rfl⟩
    exact q32SweepLeaf_sound leaf m hm

theorem q32Original34Leaves_refine_parent :
    ∀ p ∈ q32Original34Leaves, Refines p q32Parent := by
  intro p hp
  simp only [q32Original34Leaves, List.mem_append] at hp
  rcases hp with hp | hp
  · rcases List.mem_map.mp hp with ⟨leaf, hleaf, rfl⟩
    exact q32SideLeaves_refine_parent_sound leaf hleaf
  · rcases List.mem_map.mp hp with ⟨leaf, hleaf, rfl⟩
    exact q32SweepLeaves_refine_parent_sound leaf hleaf

#print axioms q32SweepOpen
#print axioms q32SweepGrowth
#print axioms q32SweepNever
#print axioms q32SweepCertificate
#print axioms q32SweepLeaves_sourceExact
#print axioms q32SweepLeaves_refine_parent
#print axioms q32Original34Leaves_sound
#print axioms q32Original34Leaves_refine_parent

end BB6.Agent24Q32SourceSweeps
