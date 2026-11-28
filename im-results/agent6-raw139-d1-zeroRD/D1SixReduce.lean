import D1ZeroRD
import ZipPrefixAudit
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6D1SixReduce
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot
open BB6.Agent10ZipAudit
open BB6.Agent6D1ZeroRD

def p : PartialMachine := BB6.Agent6D1ZeroRD.sub (BB6.Agent6D1ZeroRD.move 6)
theorem support : TNFSupport p 4 := by
  unfold p BB6.Agent6D1ZeroRD.sub
  apply refine_support _ _ _ 4 4 BB6.Agent6D1ZeroRD.support <;> decide

def cfg : Config := (knownRun p 7).getD blank
theorem rootRun : knownRun p 7 = some cfg := by rfl
theorem rootSlot : readSlot cfg = (2,true) := by decide

def sub (mv : Move) : PartialMachine := refine p (2,true) (some mv)
def code (mv : Move) : Nat := 4*mv.next.val+2*mv.write.toNat+mv.right.toNat
def move (n : Nat) : Move := ⟨(n/2)%2=1,n%2=1,⟨n/4%6,by omega⟩⟩
def hard : List Nat := [0,2,4,6,9,15,16,17,18,19]
def aud (n : Nat) : Audit := match n with
  | 1 | 3 => .cycle 0 8 true 0
  | 5 | 7 => .cycle 1 7 true 1
  | 8 => .cycle 12 5 false 2
  | 10 => .cycle 14 5 false 4
  | 11 => .cycle 2 6 true 1
  | 12 => .cycle 4 4 true 2
  | 13 => .cycle 5 3 true 2
  | 14 => .cycle 3 5 true 1
  | _ => .last 0 (0,false)

theorem pNo : weightedTNFNoAssignedHalt p :=
  BB6.Agent6D1ZeroRD.subNo (BB6.Agent6D1ZeroRD.move 6)
theorem subNo (mv : Move) : weightedTNFNoAssignedHalt (sub mv) := by
  apply weightedTNFNoAssignedHalt_refine
  exact pNo

theorem allCycles :
    allMoves (fun mv => if mv.next.val ≤ 4 ∧ code mv ∉ hard
      then zipCheck 13 (sub mv) (aud (code mv)) else true) = true := by decide

theorem cover (B : Nat) (hB : 13 ≤ B)
    (h : ∀ n ∈ hard, Cover (WeightedBound B) (sub (move n))) :
    Cover (WeightedBound B) p := by
  have hf : p initialSlot = some (some ⟨true,true,1⟩) := by decide
  have hu : p (readSlot cfg) = none := by decide
  have hd : ∀ d∈possibleDelays (refine p (readSlot cfg) none) 0, d+7+1≤B := by
    intro d hd
    have hh : weightOK p (readSlot cfg) 7 13 = true := by decide
    have := weightOK_sound _ _ _ _ hh d hd
    omega
  have hs : ∀ mv : Move, mv.next.val ≤ 4 → Cover (WeightedBound B) (sub mv) := by
    intro mv hv
    by_cases hm : code mv ∈ hard
    · have he : move (code mv) = mv := by
        rcases mv with ⟨w,r,q⟩
        have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
        rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases w <;> cases r <;> decide
      rw [← he]
      exact h _ hm
    · have hc := allMoves_sound _ allCycles mv
      simp only [hv,hm,not_false_eq_true,and_self,ite_true] at hc
      have hroot' : (sub mv) initialSlot = some (some ⟨true,true,1⟩) := by
        exact refine_preserves_firstOne p (2,true) (some mv) (by decide) hf
      have hn := (certifiedZip 13 (sub mv) (aud (code mv)) hroot' (subNo mv) hc).sound
      exact .leaf _ (fun m hc => fun n d ht hd => Nat.le_trans (hn m hc n d ht hd) hB)
  apply first_hole_tnf_cover B 4 p 7 cfg (by decide) support hf rootRun hu hd
  · intro mv hv m hm
    rw [rootSlot] at hm
    exact (hs mv (by omega)).sound m hm
  · intro q hq w r m hm
    rw [rootSlot] at hm
    exact (hs ⟨w,r,q⟩ (by simpa using Nat.le_of_eq hq)).sound m hm

#print axioms cover
end BB6.Agent6D1SixReduce
