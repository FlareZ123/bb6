import RecursiveResidual
import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw108Root
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent50RootFrontier
open BB6.Agent50RecursiveResidual
open BB6.Agent31ThreeHole BB6.Agent10ZipAudit

abbrev parent : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,false,1⟩)
abbrev child (mv : Move) : PartialMachine := refine parent (1,true) (some mv)
theorem child_root (mv : Move) : child mv initialSlot = some (some ⟨true,true,1⟩) := by rfl
theorem child_nohalt (mv : Move) : weightedTNFNoAssignedHalt (child mv) :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt))

noncomputable def cycle7 : WeightedTNFCertificate 7014 (child ⟨false,true,1⟩) 6 :=
  certifiedZip 7014 _ (.cycle 1 9 true (1)) (child_root _) (child_nohalt _) (by decide)
noncomputable def cycle15 : WeightedTNFCertificate 7014 (child ⟨true,false,3⟩) 6 :=
  certifiedZip 7014 _ (.cycle 11 1 false (-1)) (child_root _) (child_nohalt _) (by decide)
noncomputable def cycle19 : WeightedTNFCertificate 7014 (child ⟨true,true,1⟩) 6 :=
  certifiedZip 7014 _ (.cycle 1 9 true (1)) (child_root _) (child_nohalt _) (by decide)
noncomputable def cycle22 : WeightedTNFCertificate 7014 (child ⟨true,true,4⟩) 6 :=
  certifiedZip 7014 _ (.cycle 6 2 true (1)) (child_root _) (child_nohalt _) (by decide)

def remaining : List Move := [⟨false,false,0⟩, ⟨false,false,1⟩, ⟨false,false,2⟩, ⟨false,false,3⟩, ⟨false,false,4⟩, ⟨false,false,5⟩, ⟨false,true,0⟩, ⟨false,true,2⟩, ⟨false,true,3⟩, ⟨false,true,4⟩, ⟨false,true,5⟩, ⟨true,false,0⟩, ⟨true,false,1⟩, ⟨true,false,2⟩, ⟨true,false,4⟩, ⟨true,false,5⟩, ⟨true,true,0⟩, ⟨true,true,2⟩, ⟨true,true,3⟩, ⟨true,true,5⟩]
theorem remaining_count : remaining.length = 20 := by decide
theorem first_query : BB6.Agent50RecursiveResidual.queryOK 7014 parent 7 (1,true) = true := by decide

theorem child_dichotomy (mv : Move) (m : Machine) (hm : compatible (child mv) m) :
    WeightedBound 7014 m ∨ mv ∈ remaining := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · right; decide
  · right; decide
  · right; decide
  · right; decide
  · right; decide
  · exact Or.inl (cycle7.sound m hm)
  · right; decide
  · exact Or.inl (cycle19.sound m hm)
  · right; decide
  · right; decide
  · right; decide
  · right; decide
  · right; decide
  · right; decide
  · exact Or.inl (cycle15.sound m hm)
  · right; decide
  · right; decide
  · right; decide
  · right; decide
  · exact Or.inl (cycle22.sound m hm)
  · right; decide
  · right; decide
  · right; decide
  · right; decide

theorem parent_dichotomy (m : Machine) (hm : compatible parent m) :
    WeightedBound 7014 m ∨ ∃ mv ∈ remaining, compatible (child mv) m := by
  cases hs : m (1,true) with
  | none =>
    exact Or.inl (BB6.Agent50RecursiveResidual.queryOK_sound 7014 parent 7 (1,true)
      first_query m (compatible_refine hm (1,true) none hs))
  | some mv =>
    have hc := compatible_refine hm (1,true) (some mv) hs
    rcases child_dichotomy mv m hc with hb | hr
    · exact Or.inl hb
    · exact Or.inr ⟨mv,hr,hc⟩

theorem all_completions
    (h : ∀ mv ∈ remaining, ∀ m, compatible (child mv) m → WeightedBound 7014 m) :
    ∀ m, compatible parent m → WeightedBound 7014 m := by
  intro m hm
  rcases parent_dichotomy m hm with hb | ⟨mv,hr,hc⟩
  · exact hb
  · exact h mv hr m hc

#print axioms parent_dichotomy
#print axioms all_completions
end BB6.Agent10Raw108Root
