import WeightedFirstOneCover
import TNFPilot
import FastFAR
import SideCycle
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139Core
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent50TNFPilot BB6Coverage.Agent50SideCycle

def p0 := refine (refine root (1,false) (some ⟨true,true,2⟩)) (2,false) (some ⟨true,false,3⟩)
def p1 := refine p0 (3,true) (some ⟨false,false,4⟩)
def p2 := refine p1 (4,true) (some ⟨true,true,2⟩)
def p3 := refine p2 (4,false) (some ⟨false,false,3⟩)
def p4 := refine p3 (3,false) (some ⟨true,true,0⟩)
def p5 := refine p4 (2,true) (some ⟨false,true,5⟩)
def p6 := refine p5 (5,true) (some ⟨false,true,4⟩)
def p7 := refine p6 (5,false) (some ⟨true,true,0⟩)
def parent (i : Fin 7) : PartialMachine := match i.val with
  | 0 => p0
  | 1 => p1
  | 2 => p2
  | 3 => p3
  | 4 => p4
  | 5 => p5
  | _ => p6
def nextParent (i : Fin 7) : PartialMachine := match i.val with
  | 0 => p1
  | 1 => p2
  | 2 => p3
  | 3 => p4
  | 4 => p5
  | 5 => p6
  | _ => p7
def slot (i : Fin 7) : Slot := match i.val with
  | 0 => (3,true)
  | 1 => (4,true)
  | 2 => (4,false)
  | 3 => (3,false)
  | 4 => (2,true)
  | 5 => (5,true)
  | _ => (5,false)
def chosen (i : Fin 7) : Move := match i.val with
  | 0 => ⟨false,false,4⟩
  | 1 => ⟨true,true,2⟩
  | 2 => ⟨false,false,3⟩
  | 3 => ⟨true,true,0⟩
  | 4 => ⟨false,true,5⟩
  | 5 => ⟨false,true,4⟩
  | _ => ⟨true,true,0⟩
def time (i : Fin 7) : Nat := match i.val with
  | 0 => 3
  | 1 => 4
  | 2 => 7
  | 3 => 8
  | 4 => 11
  | 5 => 12
  | _ => 53
def cut (i : Fin 7) : Nat := match i.val with
  | 0 => 4
  | 1 => 5
  | 2 => 5
  | 3 => 5
  | 4 => 5
  | 5 => 6
  | _ => 6
def cfg (i : Fin 7) := (knownRun (parent i) (time i)).getD blank
def child (i : Fin 7) (mv : Move) := refine (parent i) (slot i) (some mv)

theorem fin7 (i : Fin 7) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega

theorem hrun (i : Fin 7) : knownRun (parent i) (time i) = some (cfg i) := by
  have h : (knownRun (parent i) (time i)).isSome = true := by rcases fin7 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  unfold cfg
  cases he : knownRun (parent i) (time i) <;> simp_all

theorem hread (i : Fin 7) : readSlot (cfg i) = slot i := by rcases fin7 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
theorem hhole (i : Fin 7) : parent i (slot i) = none := by rcases fin7 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
theorem hroot (i : Fin 7) : parent i initialSlot = some (some ⟨true,true,1⟩) := by rcases fin7 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
theorem hcut (i : Fin 7) : 0 < cut i := by rcases fin7 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
theorem hslot (i : Fin 7) : (slot i).1.val < cut i := by rcases fin7 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
theorem htime (i : Fin 7) : time i ≤ 53 := by rcases fin7 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
theorem hnext (i : Fin 7) : child i (chosen i) = nextParent i := by rcases fin7 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem support0 : TNFSupport p0 4 := by
  apply refine_support _ _ _ 3 4
  · apply refine_support _ _ _ 2 3
    · exact firstOneCylinder_tnf_support
    all_goals decide
  all_goals decide

theorem support1 : TNFSupport p1 5 := by apply refine_support _ _ _ 4 5 support0 <;> decide
theorem support2 : TNFSupport p2 5 := by apply refine_support _ _ _ 5 5 support1 <;> decide
theorem support3 : TNFSupport p3 5 := by apply refine_support _ _ _ 5 5 support2 <;> decide
theorem support4 : TNFSupport p4 5 := by apply refine_support _ _ _ 5 5 support3 <;> decide
theorem support5 : TNFSupport p5 6 := by apply refine_support _ _ _ 5 6 support4 <;> decide
theorem support6 : TNFSupport p6 6 := by apply refine_support _ _ _ 6 6 support5 <;> decide
theorem hsupport (i : Fin 7) : TNFSupport (parent i) (cut i) := by
  rcases fin7 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact support0 | exact support1 | exact support2 | exact support3 | exact support4 | exact support5 | exact support6

theorem stepCover (B : Nat) (hb : 59 ≤ B) (i : Fin 7)
    (hc : ∀ mv : Move, mv.next.val ≤ cut i → Cover (WeightedBound B) (child i mv)) :
    Cover (WeightedBound B) (parent i) := by
  apply Cover.leaf
  intro m hm
  have hh : parent i (readSlot (cfg i)) = none := by rw [hread]; exact hhole i
  have hw : ∀ d ∈ possibleDelays (refine (parent i) (readSlot (cfg i)) none) 0, d + time i + 1 ≤ B := by
    intro d hd
    have hd6 : d < 6 := by
      unfold possibleDelays at hd
      exact List.mem_range.mp (List.mem_filter.mp hd).1
    have ht := htime i
    omega
  have halt := first_hole_weighted_halt B (parent i) (time i) (cfg i) (hroot i) (hrun i) hh hw
  exact tnf_branch_sound B (cut i) (parent i) (slot i) (hcut i) (hsupport i) (hhole i) (hslot i) (hroot i)
    (by simpa only [hread] using halt)
    (fun mv hv m' hm' => (hc mv (Nat.le_of_lt hv)).sound m' hm')
    (fun q hq w r m' hm' => (hc ⟨w,r,q⟩ (Nat.le_of_eq hq)).sound m' hm') m hm

/-- Local nonhalting witness language used by the Raw139 path.
    The historical module obtained these two constructors through the global
    four-hole roster; Raw139 itself only uses side cycles and exact lassos. -/
inductive ResidualNonhaltWitness where
  | lasso (n : Nat)
  | side (entry period : Nat) (right : Bool) (boundary : Int)

def residualWitnessOK (p : PartialMachine) : ResidualNonhaltWitness → Bool
  | .lasso n => finiteLassoCheck p n
  | .side entry period right boundary =>
      decide (0 < period) && finiteSideCycleCheck p entry period right boundary

theorem residualWitnessOK_sound (p : PartialMachine)
    (w : ResidualNonhaltWitness) (h : residualWitnessOK p w = true) :
    ∀ m, compatible p m → NeverHalts m := by
  cases w with
  | lasso n =>
      exact zeroCover_never (finiteLassoCheck_sound p n 0 h)
  | side entry period right boundary =>
      have hc : 0 < period ∧
          finiteSideCycleCheck p entry period right boundary = true := by
        simpa only [residualWitnessOK, Bool.and_eq_true, decide_eq_true_eq] using h
      exact finiteSideCycleCheck_sound p entry period right boundary hc.1 hc.2

/-- Exact finite table equality, defined locally so Raw139 source transport does
    not depend on the global four-hole roster. -/
def sameTable (p q : PartialMachine) : Bool :=
  (List.finRange 6).all fun state =>
    [false, true].all fun symbol =>
      decide (p (state, symbol) = q (state, symbol))

theorem sameTable_sound {p q : PartialMachine}
    (h : sameTable p q = true) : p = q := by
  funext s
  rcases s with ⟨state, symbol⟩
  have h1 :
      (List.finRange 6).all (fun q' =>
        [false, true].all fun b =>
          decide (p (q', b) = q (q', b))) = true := by
    simpa [sameTable] using h
  have h2 := List.all_eq_true.mp h1 state (List.mem_finRange state)
  have h3 := List.all_eq_true.mp h2 symbol (by cases symbol <;> simp)
  exact of_decide_eq_true h3

structure Witness where
  depth : Fin 7
  mv : Move
  witness : ResidualNonhaltWitness

def witnesses : List Witness := [
  ⟨1,⟨false,false,0⟩,.side 0 5 false 2⟩,
  ⟨2,⟨false,false,0⟩,.side 0 8 false 2⟩,
  ⟨2,⟨false,false,1⟩,.side 5 4 false 1⟩,
  ⟨2,⟨true,true,2⟩,.side 5 3 false 1⟩,
  ⟨3,⟨false,false,0⟩,.side 0 9 false 2⟩,
  ⟨3,⟨false,false,1⟩,.side 5 5 false 1⟩,
  ⟨3,⟨false,true,1⟩,.side 5 5 false 1⟩,
  ⟨3,⟨true,true,1⟩,.side 1 8 false 2⟩,
  ⟨3,⟨true,true,2⟩,.side 5 4 false 1⟩,
  ⟨3,⟨true,true,3⟩,.side 2 14 false 2⟩,
  ⟨3,⟨false,true,4⟩,.lasso 9⟩,
  ⟨3,⟨true,true,4⟩,.side 6 4 false 0⟩,
  ⟨4,⟨false,false,3⟩,.side 2 12 false 2⟩,
  ⟨4,⟨false,true,3⟩,.side 2 14 false 2⟩,
  ⟨4,⟨true,false,3⟩,.side 2 12 false 2⟩,
  ⟨4,⟨true,true,3⟩,.side 2 18 false 2⟩,
  ⟨4,⟨false,false,4⟩,.side 2 14 false 2⟩,
  ⟨4,⟨false,true,4⟩,.side 2 16 false 3⟩,
  ⟨4,⟨true,false,4⟩,.lasso 13⟩,
  ⟨5,⟨false,true,0⟩,.side 0 13 true (-2)⟩,
  ⟨5,⟨false,false,1⟩,.side 2 18 false 2⟩,
  ⟨5,⟨true,true,1⟩,.side 2 20 false 4⟩,
  ⟨5,⟨false,false,2⟩,.side 2 14 false 2⟩,
  ⟨5,⟨true,false,2⟩,.side 2 14 false 2⟩,
  ⟨5,⟨true,true,2⟩,.side 2 16 false 3⟩,
  ⟨5,⟨false,false,4⟩,.side 2 14 false 2⟩,
  ⟨5,⟨true,false,4⟩,.side 2 14 false 2⟩,
  ⟨5,⟨true,true,4⟩,.side 2 16 false 3⟩,
  ⟨6,⟨false,false,0⟩,.side 93 88 true (-2)⟩,
  ⟨6,⟨false,true,1⟩,.side 46 9 true 3⟩,
  ⟨6,⟨true,false,1⟩,.side 51 3 true 5⟩,
  ⟨6,⟨false,false,3⟩,.side 148 23 true 10⟩,
  ⟨6,⟨false,true,3⟩,.side 39 26 true 0⟩,
  ⟨6,⟨false,true,4⟩,.side 265 41 true 11⟩,
  ⟨6,⟨false,false,5⟩,.side 97 96 true (-2)⟩,
  ⟨6,⟨false,true,5⟩,.side 53 1 true 7⟩,
  ⟨6,⟨true,false,5⟩,.side 52 5 true 5⟩,
  ⟨6,⟨true,true,5⟩,.side 53 1 true 7⟩,
  ⟨2,⟨false,false,4⟩,.side 7 1 false (-1)⟩,
  ⟨2,⟨true,false,4⟩,.side 7 1 false (-1)⟩,
  ⟨3,⟨false,false,2⟩,.side 8 2 false (-2)⟩,
  ⟨3,⟨true,false,2⟩,.side 8 2 false (-2)⟩,
  ⟨3,⟨false,false,3⟩,.side 8 1 false (-2)⟩,
  ⟨3,⟨false,true,3⟩,.side 18 1 true 0⟩,
  ⟨3,⟨true,false,3⟩,.side 8 1 false (-2)⟩,
  ⟨3,⟨false,false,4⟩,.side 7 2 false (-1)⟩,
  ⟨3,⟨true,false,4⟩,.side 7 2 false (-1)⟩]

def acceptedRows : List (Fin 7 × Move) := [
  (3,⟨false,false,5⟩),
  (3,⟨false,true,0⟩),
  (3,⟨false,true,2⟩),
  (3,⟨false,true,5⟩),
  (3,⟨true,false,0⟩),
  (3,⟨true,false,1⟩),
  (3,⟨true,false,5⟩),
  (3,⟨true,true,5⟩),
  (4,⟨false,false,1⟩),
  (4,⟨false,false,5⟩),
  (4,⟨false,true,1⟩),
  (4,⟨false,true,2⟩),
  (4,⟨true,false,0⟩),
  (4,⟨true,false,1⟩),
  (4,⟨true,false,5⟩),
  (4,⟨true,true,0⟩),
  (4,⟨true,true,1⟩),
  (4,⟨true,true,2⟩),
  (4,⟨true,true,4⟩),
  (4,⟨true,true,5⟩),
  (5,⟨false,false,0⟩),
  (5,⟨false,false,5⟩),
  (5,⟨false,true,1⟩),
  (5,⟨false,true,2⟩),
  (5,⟨false,true,3⟩),
  (5,⟨false,true,5⟩),
  (5,⟨true,false,0⟩),
  (5,⟨true,false,1⟩),
  (5,⟨true,false,3⟩),
  (5,⟨true,false,5⟩),
  (5,⟨true,true,3⟩),
  (5,⟨true,true,5⟩),
  (6,⟨false,false,1⟩),
  (6,⟨false,false,2⟩),
  (6,⟨false,false,4⟩),
  (6,⟨false,true,0⟩),
  (6,⟨true,false,0⟩),
  (6,⟨true,false,2⟩),
  (6,⟨true,false,3⟩),
  (6,⟨true,false,4⟩),
  (6,⟨true,true,1⟩),
  (6,⟨true,true,2⟩),
  (6,⟨true,true,3⟩)]

def sideClosed (i : Fin 7) (mv : Move) : Bool := witnesses.any (fun w => decide (w.depth = i ∧ w.mv = mv))
theorem witnessesOK : witnesses.all (fun w => residualWitnessOK (child w.depth w.mv) w.witness) = true := by decide

theorem sideCover (B : Nat) (i : Fin 7) (mv : Move) (h : sideClosed i mv = true) : Cover (WeightedBound B) (child i mv) := by
  obtain ⟨w,hw,he⟩ := List.any_eq_true.mp h
  have hw' := List.all_eq_true.mp witnessesOK w hw
  have he' := of_decide_eq_true he
  rcases he' with ⟨rfl,rfl⟩
  exact Cover.leaf _ (fun m hm => weighted_never B m (residualWitnessOK_sound _ _ hw' m hm))

/-- All 24 ordinary instructions, kept local so Raw139 does not import the
    global four-hole roster merely for enumeration. -/
def allMoves : List Move :=
  (List.finRange 6).flatMap fun q =>
    [false, true].flatMap fun w =>
      [false, true].map fun r => ⟨w, r, q⟩

theorem allMoves_complete (mv : Move) : mv ∈ allMoves := by
  rcases mv with ⟨w, r, q⟩
  have hq : q ∈ List.finRange 6 := List.mem_finRange q
  have hw : w ∈ [false, true] := by cases w <;> simp
  have hr : r ∈ [false, true] := by cases r <;> simp
  unfold allMoves
  apply List.mem_flatMap.mpr
  refine ⟨q, hq, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨w, hw, ?_⟩
  apply List.mem_map.mpr
  exact ⟨r, hr, rfl⟩

def allRows : List (Fin 7 × Move) := (List.finRange 7).flatMap (fun i => allMoves.map (fun mv => (i,mv)))
def remainingRows : List (Fin 7 × Move) := allRows.filter (fun r => decide (r.2.next.val ≤ cut r.1 ∧ r.2 ≠ chosen r.1 ∧ r ∉ acceptedRows) && !sideClosed r.1 r.2)
def rowRC : Fin 7 × Move := (6,⟨false,true,2⟩)
def rowRE : Fin 7 × Move := (6,⟨true,true,4⟩)
def leaf (r : Fin 7 × Move) : PartialMachine :=
  if r = rowRC then refine (child r.1 r.2) (0,true) (some ⟨false,true,3⟩)
  else if r = rowRE then refine (child r.1 r.2) (1,true) (some ⟨false,true,3⟩)
  else child r.1 r.2

def remainingTables := remainingRows.map leaf

theorem count : remainingRows.length = 67 := by decide
theorem tableCount : remainingTables.length = 67 := by decide
theorem acceptedCount : acceptedRows.length = 43 := by decide
theorem depthCounts : (List.finRange 7).map (fun i => (remainingRows.filter (fun r => r.1 == i)).length) = [19,22,18,0,4,2,2] := by decide

theorem offPathCover (B : Nat) (i : Fin 7) (mv : Move) (hv : mv.next.val ≤ cut i) (hn : mv ≠ chosen i)
    (ha : ∀ r ∈ acceptedRows, Cover (WeightedBound B) (child r.1 r.2))
    (hl : ∀ p ∈ remainingTables, Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) → Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) → Cover (WeightedBound B) (child rowRE.1 rowRE.2)) :
    Cover (WeightedBound B) (child i mv) := by
  by_cases hs : sideClosed i mv = true
  · exact sideCover B i mv hs
  by_cases hc : (i,mv) ∈ acceptedRows
  · exact ha (i,mv) hc
  have hm : (i,mv) ∈ remainingRows := by
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_flatMap.mpr
      exact ⟨i, by simp, List.mem_map.mpr ⟨mv,allMoves_complete mv,rfl⟩⟩
    · simp [hv,hn,hc,hs]
  have hleaf := hl (leaf (i,mv)) (List.mem_map.mpr ⟨(i,mv),hm,rfl⟩)
  by_cases hrc' : (i,mv) = rowRC
  · have h := hrc (hrc' ▸ hleaf)
    have he := congrArg (fun r : Fin 7 × Move => child r.1 r.2) hrc'
    rw [he]
    exact h
  by_cases hre' : (i,mv) = rowRE
  · have h := hre (hre' ▸ hleaf)
    have he := congrArg (fun r : Fin 7 × Move => child r.1 r.2) hre'
    rw [he]
    exact h
  simpa [leaf,hrc',hre'] using hleaf

theorem spineStep (B : Nat) (hb : 59 ≤ B) (i : Fin 7)
    (ha : ∀ r ∈ acceptedRows, Cover (WeightedBound B) (child r.1 r.2))
    (hl : ∀ p ∈ remainingTables, Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) → Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) → Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hn : Cover (WeightedBound B) (nextParent i)) : Cover (WeightedBound B) (parent i) := by
  apply stepCover B hb i
  intro mv hv
  by_cases he : mv = chosen i
  · subst mv
    rw [hnext]
    exact hn
  · exact offPathCover B i mv hv he ha hl hrc hre

theorem raw139_cover (B : Nat) (hb : 59 ≤ B)
    (ha : ∀ r ∈ acceptedRows, Cover (WeightedBound B) (child r.1 r.2))
    (hl : ∀ p ∈ remainingTables, Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) → Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) → Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) : Cover (WeightedBound B) p0 := by
  exact spineStep B hb 0 ha hl hrc hre (spineStep B hb 1 ha hl hrc hre (spineStep B hb 2 ha hl hrc hre
    (spineStep B hb 3 ha hl hrc hre (spineStep B hb 4 ha hl hrc hre (spineStep B hb 5 ha hl hrc hre
      (spineStep B hb 6 ha hl hrc hre hf))))))

#print axioms raw139_cover
#print axioms count
#print axioms depthCounts
end BB6.Agent14Raw139Core
