import Raw139Normalized
import ZipPrefixAudit
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6D1ZeroRD
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot
open BB6.Agent6Raw139Normalized BB6.Agent10ZipAudit

def p : PartialMachine := child 0 ⟨false,true,3⟩
def pCodes : PartialMachine := FAR.fromCodes [7,24,11,24,14,24,24,13,24,24,24,24]
theorem exactTable : p = pCodes := tableOK_sound _ _ (by decide)
theorem rowMember : (0,⟨false,true,3⟩) ∈ remainingRows := by decide
theorem support : TNFSupport p 4 := by
  unfold p BB6.Agent6Raw139Normalized.child
  apply refine_support _ _ _ 4 4 support0 <;> decide

def cfg : Config := (knownRun p 5).getD blank
 theorem rootRun : knownRun p 5 = some cfg := by rfl
 theorem rootSlot : readSlot cfg = (3,false) := by decide

def sub (mv : Move) : PartialMachine := refine p (3,false) (some mv)
def code (mv : Move) : Nat := 4*mv.next.val+2*mv.write.toNat+mv.right.toNat
 def move (n : Nat) : Move := ⟨(n/2)%2=1,n%2=1,⟨n/4%6,by omega⟩⟩
def hard : List Nat := [2,6,8,9,10,16,17,18,19]
def aud (n : Nat) : Audit := match n with
  | 0 | 1 | 3 => .cycle 0 6 true 0
  | 4 | 5 | 7 => .cycle 1 5 true 1
  | 11 => .cycle 2 4 true 1
  | 12 => .cycle 9 1 false 1
  | 13 | 15 => .cycle 5 1 true 3
  | 14 => .cycle 12 1 false 4
  | _ => .last 0 (0,false)
 theorem nohalt (xs : List Nat) : weightedTNFNoAssignedHalt (FAR.fromCodes xs) := by
  intro s
  rcases s with ⟨q,b⟩
  unfold FAR.fromCodes
  cases h : xs[2*q.val+b.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h,hn]
 theorem subNo (mv : Move) : weightedTNFNoAssignedHalt (sub mv) := by
  apply weightedTNFNoAssignedHalt_refine
  rw [exactTable]
  exact nohalt _
 theorem allCycles : allMoves (fun mv => if mv.next.val ≤ 4 ∧ code mv ∉ hard then zipCheck 11 (sub mv) (aud (code mv)) else true) = true := by decide
 theorem cover (B : Nat) (hB : 11 ≤ B)
    (h : ∀ n ∈ hard, Cover (WeightedBound B) (sub (move n))) : Cover (WeightedBound B) p := by
  have hf : p initialSlot = some (some ⟨true,true,1⟩) := by decide
  have hu : p (readSlot cfg) = none := by decide
  have hd : ∀ d∈possibleDelays (refine p (readSlot cfg) none) 0, d+5+1≤B := by
    intro d hd
    have hh : weightOK p (readSlot cfg) 5 11 = true := by decide
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
        exact refine_preserves_firstOne p (3,false) (some mv) (by decide) hf
      have hn := (certifiedZip 11 (sub mv) (aud (code mv)) hroot' (subNo mv) hc).sound
      exact .leaf _ (fun m hc => fun n d ht hd => Nat.le_trans (hn m hc n d ht hd) hB)
  apply first_hole_tnf_cover B 4 p 5 cfg (by decide) support hf rootRun hu hd
  · intro mv hv m hm
    rw [rootSlot] at hm
    exact (hs mv (by omega)).sound m hm
  · intro q hq w r m hm
    rw [rootSlot] at hm
    exact (hs ⟨w,r,q⟩ (by simpa using Nat.le_of_eq hq)).sound m hm
#print axioms exactTable
#print axioms rowMember
#print axioms cover
end BB6.Agent6D1ZeroRD
