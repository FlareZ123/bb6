import Raw39B0RBBase
import Raw39B0RBKid00
import Raw39B0RBKid01
import Raw39B0RBKid02
import Raw39B0RBKid03
import Raw39B0RBKid04
import Raw39B0RBKid05
import Raw39B0RBKid06
import Raw39B0RBKid07
import Raw39B0RBKid08
import Raw39B0RBKid09
import Raw39B0RBKid10
import Raw39B0RBKid11
import Raw39B0RBKid12
import Raw39B0RBKid13
import Raw39B0RBKid14
import Raw39B0RBKid15
import Raw39B0RBKid16
import Raw39B0RBKid17
import Raw39B0RBKid18
import Raw39B0RBKid19
import Raw39B0RBKid20
import Raw39B0RBKid21
import Raw39B0RBKid22
import Raw39B0RBKid23
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B0RB
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

def kidsChild : Move → Audit := byMove [kid00,kid01,kid02,kid03,kid04,kid05,kid06,kid07,kid08,kid09,kid10,kid11,kid12,kid13,kid14,kid15,kid16,kid17,kid18,kid19,kid20,kid21,kid22,kid23]
theorem kidsChild_checked (mv : Move) : zipCheck 1271 (child mv) (kidsChild mv) = true := by
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
def treeChild : Audit := .split 7 (1,true) kidsChild
theorem treeChild_checked : zipCheck 1271 pChild treeChild = true := by
  change (zipQueryOK 1271 pChild 7 (1,true) && allMoves (fun mv => zipCheck 1271 (child mv) (kidsChild mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨queryChild,allMoves_of _ kidsChild_checked⟩
noncomputable def certificateChild : WeightedTNFCertificate 1271 pChild 6 :=
  certifiedZip 1271 pChild treeChild pChild_root pChild_nohalt treeChild_checked
theorem allChild : ∀ m, compatible pChild m → WeightedBound 1271 m := certificateChild.sound
#print axioms treeChild_checked
#print axioms allChild

end BB6.Agent11Raw39B0RB
