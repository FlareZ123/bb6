import BlockPump
import DepthEightFAR

set_option maxHeartbeats 0
set_option maxRecDepth 24000

namespace BB6Coverage.Agent6Final126
open BB6Coverage Agent50Zipper Agent50Pump BB6Coverage.FAR
open BB6.Agent13BlankDelay BB6.Agent7FAR.DepthEight

/-- tree126, path [(10,17),(1,23)]. E0 is unassigned. -/
abbrev M := fromCodes [7,23,11,22,13,21,14,19,24,4,17,0]
abbrev O := bits "1"
abbrev P := bits "11"
abbrev V := bits "010"
abbrev W := bits "0101"
abbrev Z0 := bits "0"
def A (n : Nat) : HZ := ⟨0,[],W++rep P n⟩
def B (n : Nat) : HZ := ⟨0,O++rep P n,V++P⟩

theorem base : hrun M 9 ⟨0,[],[]⟩ = some (A 0) := by rfl

theorem rep_pair (n : Nat) : rep P n = rep O (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega]
    simp only [rep,ih,List.append_assoc]
    rfl

/-- Forward two-cell sweep, followed by the right-boundary turn. -/
theorem forward (n : Nat) : hrun M (20*n+22) (A n) = some (B n) := by
  cases n with
  | zero => rfl
  | succ n =>
    have h1 := openRun_sound M true false 20 ⟨0,[],W++P⟩ ⟨0,Z0++P,W⟩ [] (rep P n) (by simp) (by simp) (by rfl)
    have h2 := sweepR M 0 W P Z0 P 20 (by rfl) n P []
    have h3 := openRun_sound M false true 22 ⟨0,Z0,W⟩ ⟨0,O,V++P⟩ (rep P n++P) [] (by simp) (by simp) (by rfl)
    simp only [tail,List.nil_append,List.append_nil,List.append_assoc] at h1 h2 h3
    have H := hjoin (hjoin h1 h2) h3
    rw [show 20*(n+1)+22=20+20*n+22 by omega]
    simp only [A,B,rep,List.append_assoc]
    simpa only [List.append_assoc, rep_snoc] using H

/-- Leftward eleven-step sweep over each of the 2*n+1 marked cells. -/
theorem backward (n : Nat) : hrun M (11*(2*n+1)) (B n) = some (A (n+1)) := by
  have H := sweepL M 0 [] O V O 11 (by rfl) (2*n+1) [] P
  simp only [List.nil_append,List.append_nil] at H
  simp only [rep] at H
  rw [← rep_pair] at H
  rw [← List.append_assoc V O, show V++O=W by rfl] at H
  simpa only [A,B,rep,List.append_assoc,rep_snoc] using H

theorem grow (n : Nat) : hrun M (42*n+33) (A n) = some (A (n+1)) := by
  rw [show 42*n+33=(20*n+22)+11*(2*n+1) by omega]
  exact hjoin (forward n) (backward n)

theorem arbitrary (n : Nat) :
    ∃ t, n≤t ∧ hrun M t ⟨0,[],[]⟩ = some (A n) := by
  induction n with
  | zero => exact ⟨9,by omega,base⟩
  | succ n ih =>
    obtain ⟨t,ht,H⟩ := ih
    exact ⟨t+(42*n+33),by omega,hjoin H (grow n)⟩

/-- The blank orbit avoids E0 forever, independently of its completion. -/
theorem never (m : Machine) (hm : compatible M m) : NeverHalts m := by
  intro n
  obtain ⟨k,hk,Hk⟩ := arbitrary n
  obtain ⟨h',H'⟩ := hrun_sound M k _ _ 0 Hk
  have H := zrun_sound M m hm k _ _ H'
  rw [blank_embed] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl

theorem rootRow : M initialSlot = some (some ⟨true,true,1⟩) := by decide

def leaf (B : Nat) : WeightedTNFCertificate B M 6 :=
  WeightedTNFCertificate.nonhalt rootRow (support6 _) (fromCodes_noAssignedHalt _) never

theorem weighted (B : Nat) (m : Machine) (hm : compatible M m) :
    WeightedBound B m := (leaf B).sound m hm

#print axioms grow
#print axioms never
#print axioms leaf
#print axioms weighted

end BB6Coverage.Agent6Final126
