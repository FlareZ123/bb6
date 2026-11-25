import Raw39Base
import Raw39Kid00
import Raw39Kid01
import Raw39Kid02
import Raw39Kid03
import Raw39Kid04
import Raw39Kid05
import Raw39Kid06
import Raw39Kid07
import Raw39Kid08
import Raw39Kid09
import Raw39Kid10
import Raw39Kid11
import Raw39Kid12
import Raw39Kid13
import Raw39Kid14
import Raw39Kid15
import Raw39Kid16
import Raw39Kid17
import Raw39Kid18
import Raw39Kid19
import Raw39Kid20
import Raw39Kid21
import Raw39Kid22
import Raw39Kid23
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

def kids39 : Move → Audit := byMove [kid00,kid01,kid02,kid03,kid04,kid05,kid06,kid07,kid08,kid09,kid10,kid11,kid12,kid13,kid14,kid15,kid16,kid17,kid18,kid19,kid20,kid21,kid22,kid23]
theorem kids39_checked (mv : Move) : zipCheck 175 (child39 mv) (kids39 mv) = true := by
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
def tree1RB : Audit := .split 7 (1,true) kids39
theorem tree1RB_checked : zipCheck 175 p1RB tree1RB = true := by
  change (zipQueryOK 175 p1RB 7 (1,true) && allMoves (fun mv => zipCheck 175 (child39 mv) (kids39 mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query1RB,allMoves_of _ kids39_checked⟩
noncomputable def certificate1RB : WeightedTNFCertificate 175 p1RB 6 :=
  certifiedZip 175 p1RB tree1RB p1RB_root p1RB_nohalt tree1RB_checked
theorem all1RB : ∀ m, compatible p1RB m → WeightedBound 175 m := certificate1RB.sound
#print axioms tree1RB_checked
#print axioms all1RB

end BB6.Agent11Raw39
