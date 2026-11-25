import Raw121Base
import Raw121Kid00
import Raw121Kid01
import Raw121Kid02
import Raw121Kid03
import Raw121Kid04
import Raw121Kid05
import Raw121Kid06
import Raw121Kid07
import Raw121Kid08
import Raw121Kid09
import Raw121Kid10
import Raw121Kid11
import Raw121Kid12
import Raw121Kid13
import Raw121Kid14
import Raw121Kid15
import Raw121Kid16
import Raw121Kid17
import Raw121Kid18
import Raw121Kid19
import Raw121Kid20
import Raw121Kid21
import Raw121Kid22
import Raw121Kid23
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw121
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

def kids121 : Move → Audit := byMove [kid00,kid01,kid02,kid03,kid04,kid05,kid06,kid07,kid08,kid09,kid10,kid11,kid12,kid13,kid14,kid15,kid16,kid17,kid18,kid19,kid20,kid21,kid22,kid23]

theorem kids121_checked (mv : Move) :
    zipCheck 4063 (child121 mv) (kids121 mv) = true := by
  rcases mv with ⟨w, r, q⟩
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

def tree121 : Audit := .split 8 (4, false) kids121

theorem tree121_checked : zipCheck 4063 p121 tree121 = true := by
  change (zipQueryOK 4063 p121 8 (4, false) &&
    allMoves (fun mv => zipCheck 4063 (child121 mv) (kids121 mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query121, allMoves_of _ kids121_checked⟩

noncomputable def certificate121 : WeightedTNFCertificate 4063 p121 6 :=
  certifiedZip 4063 p121 tree121 p121_root p121_nohalt tree121_checked

theorem all121 : ∀ m, compatible p121 m → WeightedBound 4063 m :=
  certificate121.sound

#print axioms tree121_checked
#print axioms all121

end BB6.Agent11Raw121
