import Raw39RCBase
import Raw39RCKid00
import Raw39RCKid01
import Raw39RCKid02
import Raw39RCKid03
import Raw39RCKid04
import Raw39RCKid05
import Raw39RCKid06
import Raw39RCKid07
import Raw39RCKid08
import Raw39RCKid09
import Raw39RCKid10
import Raw39RCKid11
import Raw39RCKid12
import Raw39RCKid13
import Raw39RCKid14
import Raw39RCKid15
import Raw39RCKid16
import Raw39RCKid17
import Raw39RCKid18
import Raw39RCKid19
import Raw39RCKid20
import Raw39RCKid21
import Raw39RCKid22
import Raw39RCKid23
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39RC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

def kidsRC : Move → Audit := byMove [kid00,kid01,kid02,kid03,kid04,kid05,kid06,kid07,kid08,kid09,kid10,kid11,kid12,kid13,kid14,kid15,kid16,kid17,kid18,kid19,kid20,kid21,kid22,kid23]
theorem kidsRC_checked (mv : Move) : zipCheck 2354 (childRC mv) (kidsRC mv) = true := by
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
def tree0RC : Audit := .split 7 (2,true) kidsRC
theorem tree0RC_checked : zipCheck 2354 p0RC tree0RC = true := by
  change (zipQueryOK 2354 p0RC 7 (2,true) && allMoves (fun mv => zipCheck 2354 (childRC mv) (kidsRC mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨queryRC,allMoves_of _ kidsRC_checked⟩
noncomputable def certificate0RC : WeightedTNFCertificate 2354 p0RC 6 :=
  certifiedZip 2354 p0RC tree0RC p0RC_root p0RC_nohalt tree0RC_checked
theorem all0RC : ∀ m, compatible p0RC m → WeightedBound 2354 m := certificate0RC.sound
#print axioms tree0RC_checked
#print axioms all0RC

end BB6.Agent11Raw39RC
