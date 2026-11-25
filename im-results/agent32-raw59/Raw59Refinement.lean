import Raw59A0RBData
import Raw59A0LDData
import Raw59A1RCData
import Raw59A0RCData
import Raw59A0RFData
import Raw59A1LAData
import Raw59A0RDData
import Raw59A1LCData
import Raw59A1RBData
import Raw59A1RDData
import Raw59A0LCData
import Raw59A0REData
import FourHoleResidualRoster
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw59
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent31FourHoleRoster
def closed (mv : Move) : Bool :=
  ([(⟨false,true,0⟩ : Move),⟨false,true,3⟩,⟨true,false,2⟩,⟨true,false,3⟩,⟨true,true,0⟩,⟨true,true,4⟩,⟨true,true,1⟩,⟨true,true,3⟩,⟨false,false,2⟩,⟨false,true,4⟩,⟨false,true,1⟩,⟨false,false,3⟩,⟨true,true,2⟩,⟨false,true,2⟩,⟨false,true,5⟩,⟨true,false,0⟩]).any (fun a => decide (a=mv))
theorem closed_sound (mv : Move) (h : closed mv = true) :
    ∀ m, compatible (child mv) m → WeightedBound 395 m := by
  simp only [closed,List.any_cons,List.any_nil,Bool.or_false,Bool.or_eq_true,decide_eq_true_eq] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · subst mv; exact all_0RA
  · subst mv; intro m hm k d hk hd; exact Nat.le_trans (BB6.Agent32Raw59A0RD.all0RD m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd; exact Nat.le_trans (BB6.Agent32Raw59A1LC.all1LC m hm k d hk hd) (by decide)
  · subst mv; exact all_1LD
  · subst mv; exact all_1RA
  · subst mv; exact all_1RE
  · subst mv; intro m hm k d hk hd; exact Nat.le_trans (BB6.Agent32Raw59A1RB.all1RB m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd; exact Nat.le_trans (BB6.Agent32Raw59A1RD.all1RD m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd; exact Nat.le_trans (BB6.Agent32Raw59A0LC.all0LC m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd; exact Nat.le_trans (BB6.Agent32Raw59A0RE.all0RE m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd; exact Nat.le_trans (BB6.Agent32Raw59A0RB.all0RB m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd; exact Nat.le_trans (BB6.Agent32Raw59A0LD.all0LD m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd; exact Nat.le_trans (BB6.Agent32Raw59A1RC.all1RC m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd; exact Nat.le_trans (BB6.Agent32Raw59A0RC.all0RC m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd; exact Nat.le_trans (BB6.Agent32Raw59A0RF.all0RF m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd; exact Nat.le_trans (BB6.Agent32Raw59A1LA.all1LA m hm k d hk hd) (by decide)
theorem compatible_child {m : Machine} (hm : compatible p59 m) (v : Transition)
    (hv : m (0,true) = v) : compatible (refine p59 (0,true) v) m := by
  intro s t ht
  by_cases he : s = (0,true)
  · subst s; simp [refine] at ht; subst t; exact hv
  · exact hm s t (by simpa [refine,he] using ht)
theorem child_dichotomy (m : Machine) (hm : compatible p59 m) :
    WeightedBound 395 m ∨ ∃ mv, closed mv = false ∧ compatible (child mv) m := by
  cases hs : m (0,true) with
  | none => exact Or.inl (halt_branch m (compatible_child hm none hs))
  | some mv =>
    have hc := compatible_child hm (some mv) hs
    cases h : closed mv with
    | true => exact Or.inl (closed_sound mv h m hc)
    | false => exact Or.inr ⟨mv,h,hc⟩
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
def remainingChildren := moves.filter fun mv => !(closed mv)
theorem remainingChildren_count : remainingChildren.length = 8 := by decide
noncomputable def refinedRoster : List (List Move × PartialMachine) :=
  remainingRootRoster.flatMap fun e =>
    if sameTable e.2 p59 then remainingChildren.map (fun mv => (e.1 ++ [mv], child mv))
    else [e]
theorem refinedRoster_count : refinedRoster.length = 131 := by decide
theorem refinedRoster_sound (m : Machine) (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 395 m ∨ ∃ e ∈ refinedRoster, compatible e.2 m := by
  rcases remainingRootRoster_sound m hm with h | ⟨e,he,hp⟩
  · exact Or.inl h
  · cases h : sameTable e.2 p59 with
    | false =>
      right; refine ⟨e,List.mem_flatMap.mpr ⟨e,he,?_⟩,hp⟩
      simp [h]
    | true =>
      have hEq := sameTable_sound h
      rcases child_dichotomy m (hEq ▸ hp) with hb | ⟨mv,hc,hcomp⟩
      · exact Or.inl hb
      · right
        refine ⟨(e.1 ++ [mv],child mv),List.mem_flatMap.mpr ⟨e,he,?_⟩,hcomp⟩
        simp only [h,if_true]
        apply List.mem_map.mpr
        exact ⟨mv,List.mem_filter.mpr ⟨moves_complete mv,by simp [hc]⟩,rfl⟩
#print axioms child_dichotomy
#print axioms refinedRoster_count
#print axioms refinedRoster_sound
end BB6.Agent32Raw59
