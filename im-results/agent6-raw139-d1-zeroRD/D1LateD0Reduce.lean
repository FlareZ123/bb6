import D1ZeroRD
import ZipPrefixAudit
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent6D1SixteenReduce
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot
open BB6.Agent10ZipAudit BB6.Agent6D1ZeroRD

def p : PartialMachine := BB6.Agent6D1ZeroRD.sub (BB6.Agent6D1ZeroRD.move 16)
theorem support : TNFSupport p 5 := by
  unfold p BB6.Agent6D1ZeroRD.sub
  apply refine_support _ _ _ 4 5 BB6.Agent6D1ZeroRD.support <;> decide

def cfg : Config := (knownRun p 6).getD blank
theorem rootRun : knownRun p 6 = some cfg := by rfl
theorem rootSlot : readSlot cfg = (4,false) := by decide

def sub (mv : Move) : PartialMachine := refine p (4,false) (some mv)
def code (mv : Move) : Nat := 4*mv.next.val+2*mv.write.toNat+mv.right.toNat
def move (n : Nat) : Move := ⟨(n/2)%2=1,n%2=1,⟨n/4%6,by omega⟩⟩
def hard : List Nat := [2,6,9,12,14,15,16,18,20,21,22,23]
def aud (n : Nat) : Audit := match n with
  | 0 | 1 | 3 => .cycle 0 7 true 0
  | 4 | 5 | 7 => .cycle 1 6 true 1
  | 8 => .cycle 10 3 false 2
  | 10 => .cycle 11 3 false 3
  | 11 => .cycle 2 5 true 1
  | 13 => .cycle 5 2 true 2
  | 17 | 19 => .cycle 6 1 true 2
  | _ => .last 0 (0,false)

theorem pNo : weightedTNFNoAssignedHalt p :=
  BB6.Agent6D1ZeroRD.subNo (BB6.Agent6D1ZeroRD.move 16)
theorem subNo (mv : Move) : weightedTNFNoAssignedHalt (sub mv) := by
  apply weightedTNFNoAssignedHalt_refine
  exact pNo

theorem allCycles :
    allMoves (fun mv => if mv.next.val ≤ 5 ∧ code mv ∉ hard
      then zipCheck 12 (sub mv) (aud (code mv)) else true) = true := by decide

theorem cover (B : Nat) (hB : 12 ≤ B)
    (h : ∀ n ∈ hard, Cover (WeightedBound B) (sub (move n))) :
    Cover (WeightedBound B) p := by
  have hf : p initialSlot = some (some ⟨true,true,1⟩) := by decide
  have hu : p (readSlot cfg) = none := by decide
  have hd : ∀ d∈possibleDelays (refine p (readSlot cfg) none) 0, d+6+1≤B := by
    intro d hd
    have hh : weightOK p (readSlot cfg) 6 12 = true := by decide
    have := weightOK_sound _ _ _ _ hh d hd
    omega
  have hs : ∀ mv : Move, mv.next.val ≤ 5 → Cover (WeightedBound B) (sub mv) := by
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
        exact refine_preserves_firstOne p (4,false) (some mv) (by decide) hf
      have hn := (certifiedZip 12 (sub mv) (aud (code mv)) hroot' (subNo mv) hc).sound
      exact .leaf _ (fun m hc => fun n d ht hd => Nat.le_trans (hn m hc n d ht hd) hB)
  apply first_hole_tnf_cover B 5 p 6 cfg (by decide) support hf rootRun hu hd
  · intro mv hv m hm
    rw [rootSlot] at hm
    exact (hs mv (by omega)).sound m hm
  · intro q hq w r m hm
    rw [rootSlot] at hm
    exact (hs ⟨w,r,q⟩ (by simpa using Nat.le_of_eq hq)).sound m hm

#print axioms cover
end BB6.Agent6D1SixteenReduce

namespace BB6.Agent6D1SeventeenReduce
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot
open BB6.Agent10ZipAudit BB6.Agent6D1ZeroRD

def p : PartialMachine := BB6.Agent6D1ZeroRD.sub (BB6.Agent6D1ZeroRD.move 17)
theorem support : TNFSupport p 5 := by
  unfold p BB6.Agent6D1ZeroRD.sub
  apply refine_support _ _ _ 4 5 BB6.Agent6D1ZeroRD.support <;> decide

def cfg : Config := (knownRun p 6).getD blank
theorem rootRun : knownRun p 6 = some cfg := by rfl
theorem rootSlot : readSlot cfg = (4,false) := by decide

def sub (mv : Move) : PartialMachine := refine p (4,false) (some mv)
def code (mv : Move) : Nat := 4*mv.next.val+2*mv.write.toNat+mv.right.toNat
def move (n : Nat) : Move := ⟨(n/2)%2=1,n%2=1,⟨n/4%6,by omega⟩⟩
def hard : List Nat := [2,6,8,9,10,14,16,18,20,21,22,23]
def aud (n : Nat) : Audit := match n with
  | 0 | 1 | 3 => .cycle 0 7 true 0
  | 4 | 5 | 7 => .cycle 1 6 true 1
  | 11 => .cycle 2 5 true 1
  | 12 | 13 | 15 => .cycle 5 2 true 3
  | 17 | 19 => .cycle 6 1 true 4
  | _ => .last 0 (0,false)

theorem pNo : weightedTNFNoAssignedHalt p :=
  BB6.Agent6D1ZeroRD.subNo (BB6.Agent6D1ZeroRD.move 17)
theorem subNo (mv : Move) : weightedTNFNoAssignedHalt (sub mv) := by
  apply weightedTNFNoAssignedHalt_refine
  exact pNo

theorem allCycles :
    allMoves (fun mv => if mv.next.val ≤ 5 ∧ code mv ∉ hard
      then zipCheck 12 (sub mv) (aud (code mv)) else true) = true := by decide

theorem cover (B : Nat) (hB : 12 ≤ B)
    (h : ∀ n ∈ hard, Cover (WeightedBound B) (sub (move n))) :
    Cover (WeightedBound B) p := by
  have hf : p initialSlot = some (some ⟨true,true,1⟩) := by decide
  have hu : p (readSlot cfg) = none := by decide
  have hd : ∀ d∈possibleDelays (refine p (readSlot cfg) none) 0, d+6+1≤B := by
    intro d hd
    have hh : weightOK p (readSlot cfg) 6 12 = true := by decide
    have := weightOK_sound _ _ _ _ hh d hd
    omega
  have hs : ∀ mv : Move, mv.next.val ≤ 5 → Cover (WeightedBound B) (sub mv) := by
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
        exact refine_preserves_firstOne p (4,false) (some mv) (by decide) hf
      have hn := (certifiedZip 12 (sub mv) (aud (code mv)) hroot' (subNo mv) hc).sound
      exact .leaf _ (fun m hc => fun n d ht hd => Nat.le_trans (hn m hc n d ht hd) hB)
  apply first_hole_tnf_cover B 5 p 6 cfg (by decide) support hf rootRun hu hd
  · intro mv hv m hm
    rw [rootSlot] at hm
    exact (hs mv (by omega)).sound m hm
  · intro q hq w r m hm
    rw [rootSlot] at hm
    exact (hs ⟨w,r,q⟩ (by simpa using Nat.le_of_eq hq)).sound m hm

#print axioms cover
end BB6.Agent6D1SeventeenReduce
