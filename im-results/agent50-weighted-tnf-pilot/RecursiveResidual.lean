import RootFrontier

set_option maxRecDepth 24000
set_option maxHeartbeats 0

namespace BB6.Agent50RecursiveResidual
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent50RootFrontier BB6Coverage.Agent50SideCycle

/-- Untrusted, explicit certificates for partial decision trees. An open
    leaf is retained, never treated as a nonhalting verdict. -/
inductive Tree where
  | openLeaf
  | last (n : Nat) (s : Slot)
  | side (n k : Nat) (r : Bool) (b : Int)
  | branch (n : Nat) (s : Slot) (children : Move → Tree)

def queryOK (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  decide (p initialSlot = some (some ⟨true,true,1⟩)) &&
  (decide ((knownRun p n).map readSlot = some s) &&
  (decide (p s = none) && weightOK p s n B))

def lastOK (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  queryOK B p n s && restOK p s

def sideOK (p : PartialMachine) (n k : Nat) (r : Bool) (b : Int) : Bool :=
  decide (0 < k) && finiteSideCycleCheck p n k r b

theorem queryOK_sound (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot)
    (h : queryOK B p n s = true) :
    ∀ m, compatible (refine p s none) m → WeightedBound B m := by
  have hh : p initialSlot = some (some ⟨true,true,1⟩) ∧
      (knownRun p n).map readSlot = some s ∧ p s = none ∧ weightOK p s n B = true := by
    simpa only [queryOK,Bool.and_eq_true,decide_eq_true_eq] using h
  obtain ⟨hf,hread,hu,hw⟩ := hh
  cases hr : knownRun p n with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = s := by simpa [hr] using hread
    simpa only [hs] using first_hole_weighted_halt B p n c hf hr
      (by simpa [hs] using hu) (by simpa [hs] using weightOK_sound p s n B hw)

theorem lastOK_sound (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot)
    (h : lastOK B p n s = true) :
    ∀ m, compatible p m → WeightedBound B m := by
  have hh : p initialSlot = some (some ⟨true,true,1⟩) ∧
      (knownRun p n).map readSlot = some s ∧ p s = none ∧
      weightOK p s n B = true ∧ restOK p s = true := by
    simpa only [lastOK,queryOK,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using h
  obtain ⟨hf,hread,hu,hw,hrest⟩ := hh
  cases hr : knownRun p n with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = s := by simpa [hr] using hread
    exact last_hole_sound B p n c hf hr
      (by simpa [hs] using hu)
      (by simpa [hs] using restOK_sound p s hrest)
      (by simpa [hs] using weightOK_sound p s n B hw)

theorem sideOK_sound (B : Nat) (p : PartialMachine) (n k : Nat) (r : Bool) (b : Int)
    (h : sideOK p n k r b = true) :
    ∀ m, compatible p m → WeightedBound B m := by
  have hh : 0 < k ∧ finiteSideCycleCheck p n k r b = true := by
    simpa only [sideOK,Bool.and_eq_true,decide_eq_true_eq] using h
  intro m hm
  exact weighted_never B m (finiteSideCycleCheck_sound p n k r b hh.1 hh.2 m hm)

def Tree.check (B : Nat) (p : PartialMachine) : Tree → Bool
  | .openLeaf => true
  | .last n s => lastOK B p n s
  | .side n k r b => sideOK p n k r b
  | .branch n s f => queryOK B p n s && allMoves.all (fun mv => (f mv).check B (refine p s (some mv)))

def Tree.residuals (p : PartialMachine) : Tree → List PartialMachine
  | .openLeaf => [p]
  | .last .. => []
  | .side .. => []
  | .branch _ s f => allMoves.flatMap fun mv => (f mv).residuals (refine p s (some mv))

theorem compatible_refine {p : PartialMachine} {m : Machine} (hm : compatible p m)
    (s : Slot) (v : Option Move) (hv : m s = v) : compatible (refine p s v) m := by
  intro t u hu
  by_cases he : t = s
  · subst t
    have h : u = v := by simpa [refine] using hu.symm
    simpa [h] using hv
  · exact hm t u (by simpa [refine,he] using hu)

theorem Tree.sound (B : Nat) (tree : Tree) (p : PartialMachine) (h : tree.check B p = true) :
    ∀ m, compatible p m → WeightedBound B m ∨ ∃ q ∈ tree.residuals p, compatible q m := by
  induction tree generalizing p with
  | openLeaf => intro m hm; exact Or.inr ⟨p,by simp [residuals],hm⟩
  | last n s => intro m hm; exact Or.inl (lastOK_sound B p n s h m hm)
  | side n k r b => intro m hm; exact Or.inl (sideOK_sound B p n k r b h m hm)
  | branch n s f ih =>
    have hh : queryOK B p n s = true ∧ allMoves.all (fun mv => (f mv).check B (refine p s (some mv))) = true := by
      simpa only [check,Bool.and_eq_true] using h
    intro m hm
    cases ha : m s with
    | none => exact Or.inl (queryOK_sound B p n s hh.1 m (compatible_refine hm s none ha))
    | some mv =>
      have hc := List.all_eq_true.mp hh.2 mv (allMoves_complete mv)
      rcases ih mv (refine p s (some mv)) hc m (compatible_refine hm s (some mv) ha) with hb | ⟨q,hq,hcomp⟩
      · exact Or.inl hb
      · exact Or.inr ⟨q,List.mem_flatMap.mpr ⟨mv,allMoves_complete mv,hq⟩,hcomp⟩

def moveIndex (m : Move) : Nat := m.next.val*4+(if m.write then 2 else 0)+(if m.right then 1 else 0)

/-- The default is deliberately open, so missing entries cannot prove closure. -/
def branchList (n : Nat) (s : Slot) (children : List Tree) : Tree :=
  .branch n s (fun mv => (children[moveIndex mv]?).getD .openLeaf)

def Tree.packedResiduals (p : PartialMachine) (t : Tree) : List PackedTable :=
  (t.residuals p).map packTable

theorem Tree.packed_sound (B : Nat) (tree : Tree) (p : PartialMachine) (h : tree.check B p = true) :
    ∀ m, compatible p m → WeightedBound B m ∨
      ∃ q ∈ tree.packedResiduals p, compatible (unpackTable q) m := by
  intro m hm
  rcases tree.sound B p h m hm with hb | ⟨q,hq,hcomp⟩
  · exact Or.inl hb
  · exact Or.inr ⟨packTable q,List.mem_map.mpr ⟨q,hq,rfl⟩,by simpa only [unpack_packTable] using hcomp⟩

#print axioms queryOK_sound
#print axioms lastOK_sound
#print axioms Tree.sound
#print axioms Tree.packed_sound
end BB6.Agent50RecursiveResidual
