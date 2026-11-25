import ZipThreeHoleAudit
import Raw42RDGrowth
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw42
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

abbrev parent : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,false,1⟩)
abbrev child (mv : Move) : PartialMachine := refine parent (1,true) (some mv)

theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt)
theorem query : zipQueryOK 12 parent 6 (1,true) = true := by decide

theorem halt_branch (m : Machine) (hc : compatible (refine parent (1,true) none) m) :
    WeightedBound 12 m := by
  obtain ⟨hread,hhole,hw⟩ := zipQueryOK_sound query
  cases hr : knownRun parent 6 with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = (1,true) := by simpa [hr] using hread
    exact first_hole_weighted_halt 12 parent 6 c parent_root hr
      (by simpa only [hs] using hhole)
      (by simpa only [hs] using weightOK_sound parent (1,true) 6 12 hw)
      m (by simpa only [hs] using hc)

theorem cycle_child (mv : Move) (e k : Nat) (r : Bool) (b : Int)
    (h : zipCheck 12 (child mv) (.cycle e k r b) = true) :
    ∀ m, compatible (child mv) m → WeightedBound 12 m :=
  (certifiedZip 12 (child mv) (.cycle e k r b)
    (refine_preserves_firstOne parent (1,true) (some mv) (by decide) parent_root)
    (weightedTNFNoAssignedHalt_refine _ _ _ parent_nohalt) h).sound

theorem rd_eq : child ⟨true,true,3⟩ = BB6.Agent32Raw42RD.p := by
  apply tableOK_sound
  decide

theorem rd_never (m : Machine) (h : compatible (child ⟨true,true,3⟩) m) : NeverHalts m :=
  BB6.Agent32Raw42RD.never m (rd_eq ▸ h)

def closed (mv : Move) : Bool :=
  [⟨false,false,1⟩,⟨false,false,2⟩,⟨false,false,3⟩,
   ⟨false,true,2⟩,⟨false,true,3⟩,⟨true,false,3⟩,
   ⟨true,true,2⟩,⟨true,true,3⟩].contains mv

theorem closed_sound (mv : Move) (h : closed mv = true) :
    ∀ m, compatible (child mv) m → WeightedBound 12 m := by
  have hh : mv = ⟨false,false,1⟩ ∨ mv = ⟨false,false,2⟩ ∨ mv = ⟨false,false,3⟩ ∨
    mv = ⟨false,true,2⟩ ∨ mv = ⟨false,true,3⟩ ∨ mv = ⟨true,false,3⟩ ∨
    mv = ⟨true,true,2⟩ ∨ mv = ⟨true,true,3⟩ := by
    simpa [closed,List.contains_iff_mem] using h
  rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact cycle_child _ 31 18 false 0 (by decide)
  · exact cycle_child _ 8 1 false 0 (by decide)
  · exact cycle_child _ 7 1 false (-1) (by decide)
  · exact cycle_child _ 1 11 true 0 (by decide)
  · exact cycle_child _ 7 1 false 1 (by decide)
  · exact cycle_child _ 7 1 false (-1) (by decide)
  · exact cycle_child _ 1 11 true 0 (by decide)
  · intro m hm; exact weighted_never 12 m (rd_never m hm)

def moves : List Move :=
  (List.finRange 6).flatMap fun q => [false,true].flatMap fun w =>
    [false,true].map fun r => ⟨w,r,q⟩

theorem moves_complete (mv : Move) : mv ∈ moves := by
  rcases mv with ⟨w,r,q⟩
  unfold moves
  apply List.mem_flatMap.mpr
  refine ⟨q,List.mem_finRange q,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨w,by cases w <;> simp,?_⟩
  exact List.mem_map.mpr ⟨r,by cases r <;> simp,rfl⟩

def retained : List Move := moves.filter fun mv => !(closed mv)
theorem retained_count : retained.length = 16 := by decide
theorem compatible_child {m : Machine} (hm : compatible parent m) (v : Transition)
    (hv : m (1,true) = v) : compatible (refine parent (1,true) v) m := by
  intro s t ht
  by_cases he : s = (1,true)
  · subst s; simp [refine] at ht; subst t; exact hv
  · exact hm s t (by simpa [refine,he] using ht)

theorem partition (m : Machine) (hm : compatible parent m) :
    WeightedBound 12 m ∨ ∃ mv ∈ retained, compatible (child mv) m := by
  cases h : m (1,true) with
  | none => exact Or.inl (halt_branch m (compatible_child hm none h))
  | some mv =>
    have hc := compatible_child hm (some mv) h
    cases hd : closed mv with
    | true => exact Or.inl (closed_sound mv hd m hc)
    | false => exact Or.inr ⟨mv,List.mem_filter.mpr ⟨moves_complete mv,by simp [hd]⟩,hc⟩

theorem cover_parent (B : Nat) (hB : 12 ≤ B)
    (hr : ∀ mv ∈ retained, Cover (WeightedBound B) (child mv)) :
    Cover (WeightedBound B) parent := by
  refine Cover.leaf parent ?_
  intro m hm
  rcases partition m hm with h | ⟨mv,hmem,hc⟩
  · intro k d hk hd; exact Nat.le_trans (h k d hk hd) hB
  · exact (hr mv hmem).sound m hc

#print axioms partition
#print axioms cover_parent
end BB6.Agent32Raw42
