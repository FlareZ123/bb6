import Raw39B0REBase
import Raw39B0REKid00
import Raw39B0REKid01
import Raw39B0REKid02
import Raw39B0REKid03
import Raw39B0REKid04
import Raw39B0REKid05
import Raw39B0REKid06
import Raw39B0REKid07
import Raw39B0REKid08
import Raw39B0REKid09
import Raw39B0REKid10
import Raw39B0REKid11
import Raw39B0REKid12
import Raw39B0REKid13
import Raw39B0REKid14
import Raw39B0REKid15
import Raw39B0REKid16
import Raw39B0REKid17
import Raw39B0REKid18
import Raw39B0REKid19
import Raw39B0REKid20
import Raw39B0REKid21
import Raw39B0REKid22
import Raw39B0REKid23
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B0RE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

def kidsChild : Move → Audit := byMove [kid00,kid01,kid02,kid03,kid04,kid05,kid06,kid07,kid08,kid09,kid10,kid11,kid12,kid13,kid14,kid15,kid16,kid17,kid18,kid19,kid20,kid21,kid22,kid23]
theorem kidsChild_checked (mv : Move) : zipCheck 944 (child mv) (kidsChild mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · exact check00
  · exact check06
  · exact check12
  · exact check18
  · exact check01
  · exact check07
  · exact check13
  · exact check19
  · exact check02
  · exact check08
  · exact check14
  · exact check20
  · exact check03
  · exact check09
  · exact check15
  · exact check21
  · exact check04
  · exact check10
  · exact check16
  · exact check22
  · exact check05
  · exact check11
  · exact check17
  · exact check23
def treeChild : Audit := .split 7 (4,true) kidsChild
theorem treeChild_checked : zipCheck 944 pChild treeChild = true := by
  change (zipQueryOK 944 pChild 7 (4,true) && allMoves (fun mv => zipCheck 944 (child mv) (kidsChild mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨queryChild,allMoves_of _ kidsChild_checked⟩
noncomputable def certificateChild : WeightedTNFCertificate 944 pChild 6 :=
  certifiedZip 944 pChild treeChild pChild_root pChild_nohalt treeChild_checked
theorem allChild : ∀ m, compatible pChild m → WeightedBound 944 m := certificateChild.sound
#print axioms treeChild_checked
#print axioms allChild

end BB6.Agent11Raw39B0RE
