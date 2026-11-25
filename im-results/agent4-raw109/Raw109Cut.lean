import RecursiveResidual
import Raw109B0LDData
import Raw109B0REData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent4Raw109Cut
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent50RootFrontier BB6.Agent50RecursiveResidual
open BB6.Agent31ThreeHole BB6.Agent10ZipAudit
abbrev parent : PartialMachine := BB6.Agent4Raw109B0RE.p109
abbrev child (mv : Move) : PartialMachine := refine parent (1,true) (some mv)
theorem child_root (mv : Move) : child mv initialSlot = some (some ⟨true,true,1⟩) := by rfl
theorem child_nohalt (mv : Move) : weightedTNFNoAssignedHalt (child mv) :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt))
noncomputable def cycle1 : WeightedTNFCertificate 353 (child ⟨false,false,1⟩) 6 :=
  certifiedZip 353 _ (.cycle 8 9 false (2)) (child_root _) (child_nohalt _) (by decide)
noncomputable def cycle4 : WeightedTNFCertificate 353 (child ⟨false,false,4⟩) 6 :=
  certifiedZip 353 _ (.cycle 1 8 true (1)) (child_root _) (child_nohalt _) (by decide)
noncomputable def cycle6 : WeightedTNFCertificate 353 (child ⟨false,true,0⟩) 6 :=
  certifiedZip 353 _ (.cycle 0 8 true (0)) (child_root _) (child_nohalt _) (by decide)
noncomputable def cycle7 : WeightedTNFCertificate 353 (child ⟨false,true,1⟩) 6 :=
  certifiedZip 353 _ (.cycle 1 7 true (1)) (child_root _) (child_nohalt _) (by decide)
noncomputable def cycle9 : WeightedTNFCertificate 353 (child ⟨false,true,3⟩) 6 :=
  certifiedZip 353 _ (.cycle 3 5 true (1)) (child_root _) (child_nohalt _) (by decide)
noncomputable def cycle15 : WeightedTNFCertificate 353 (child ⟨true,false,3⟩) 6 :=
  certifiedZip 353 _ (.cycle 1 9 true (1)) (child_root _) (child_nohalt _) (by decide)
noncomputable def cycle16 : WeightedTNFCertificate 353 (child ⟨true,false,4⟩) 6 :=
  certifiedZip 353 _ (.cycle 6 2 true (2)) (child_root _) (child_nohalt _) (by decide)
noncomputable def cycle18 : WeightedTNFCertificate 353 (child ⟨true,true,0⟩) 6 :=
  certifiedZip 353 _ (.cycle 0 8 true (0)) (child_root _) (child_nohalt _) (by decide)
noncomputable def cycle19 : WeightedTNFCertificate 353 (child ⟨true,true,1⟩) 6 :=
  certifiedZip 353 _ (.cycle 1 7 true (1)) (child_root _) (child_nohalt _) (by decide)
noncomputable def cycle20 : WeightedTNFCertificate 353 (child ⟨true,true,2⟩) 6 :=
  certifiedZip 353 _ (.cycle 2 6 true (1)) (child_root _) (child_nohalt _) (by decide)
noncomputable def cycle21 : WeightedTNFCertificate 353 (child ⟨true,true,3⟩) 6 :=
  certifiedZip 353 _ (.cycle 1 10 true (1)) (child_root _) (child_nohalt _) (by decide)
def remaining : List Move := [⟨false,false,0⟩, ⟨false,false,2⟩, ⟨false,false,5⟩, ⟨false,true,2⟩, ⟨false,true,5⟩, ⟨true,false,0⟩, ⟨true,false,1⟩, ⟨true,false,2⟩, ⟨true,false,5⟩, ⟨true,true,4⟩, ⟨true,true,5⟩]
theorem remaining_count : remaining.length = 11 := by decide
theorem first_query : BB6.Agent50RecursiveResidual.queryOK 353 parent 7 (1,true) = true := by decide
theorem child_dichotomy (mv : Move) (m : Machine) (hm : compatible (child mv) m) :
    WeightedBound 353 m ∨ mv ∈ remaining := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · right; decide
  · exact Or.inl (cycle6.sound m hm)
  · right; decide
  · exact Or.inl (cycle18.sound m hm)
  · exact Or.inl (cycle1.sound m hm)
  · exact Or.inl (cycle7.sound m hm)
  · right; decide
  · exact Or.inl (cycle19.sound m hm)
  · right; decide
  · right; decide
  · right; decide
  · exact Or.inl (cycle20.sound m hm)
  · left; intro k d hk hd
    exact Nat.le_trans (BB6.Agent4Raw109B0LD.all_closed m hm k d hk hd) (by decide)
  · exact Or.inl (cycle9.sound m hm)
  · exact Or.inl (cycle15.sound m hm)
  · exact Or.inl (cycle21.sound m hm)
  · exact Or.inl (cycle4.sound m hm)
  · exact Or.inl (BB6.Agent4Raw109B0RE.all_closed m hm)
  · exact Or.inl (cycle16.sound m hm)
  · right; decide
  · right; decide
  · right; decide
  · right; decide
  · right; decide
theorem parent_dichotomy (m : Machine) (hm : compatible parent m) :
    WeightedBound 353 m ∨ ∃ mv ∈ remaining, compatible (child mv) m := by
  cases hs : m (1,true) with
  | none =>
    exact Or.inl (BB6.Agent50RecursiveResidual.queryOK_sound 353 parent 7 (1,true)
      first_query m (compatible_refine hm (1,true) none hs))
  | some mv =>
    have hc := compatible_refine hm (1,true) (some mv) hs
    rcases child_dichotomy mv m hc with hb | hr
    · exact Or.inl hb
    · exact Or.inr ⟨mv,hr,hc⟩
#print axioms parent_dichotomy
end BB6.Agent4Raw109Cut
