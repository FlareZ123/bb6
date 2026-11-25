import Raw59ParentPartition
import Raw59A0RBData
import Raw59A0LDData
import Raw59A1RCData
import Raw59A0RCData
import Raw59A0RFData
import Raw59A1LAData
import Raw59A1RFData
import Raw59A0RDData
import Raw59A1LCData
import Raw59A1RBData
import Raw59A1RDData
import Raw59A0LCData
import Raw59A0REData

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw59CanonicalAll
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent32Raw59 BB6.Agent32Raw59Partition

def closed (mv : Move) : Bool :=
  ([(⟨false,true,0⟩ : Move),(⟨true,false,3⟩ : Move),(⟨true,true,0⟩ : Move),(⟨true,true,4⟩ : Move),(⟨false,true,1⟩ : Move),(⟨false,false,3⟩ : Move),(⟨true,true,2⟩ : Move),(⟨false,true,2⟩ : Move),(⟨false,true,5⟩ : Move),(⟨true,false,0⟩ : Move),(⟨true,true,5⟩ : Move),(⟨false,true,3⟩ : Move),(⟨true,false,2⟩ : Move),(⟨true,true,1⟩ : Move),(⟨true,true,3⟩ : Move),(⟨false,false,2⟩ : Move),(⟨false,true,4⟩ : Move)]).any (fun a => decide (a=mv))

theorem closed_sound (mv : Move) (h : closed mv = true) :
    ∀ m, compatible (child mv) m → WeightedBound 395 m := by
  simp only [closed,List.any_cons,List.any_nil,Bool.or_false,Bool.or_eq_true,decide_eq_true_eq] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · subst mv; exact all_0RA
  · subst mv; exact all_1LD
  · subst mv; exact all_1RA
  · subst mv; exact all_1RE
  · subst mv; intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent32Raw59A0RB.all0RB m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent32Raw59A0LD.all0LD m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent32Raw59A1RC.all1RC m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent32Raw59A0RC.all0RC m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent32Raw59A0RF.all0RF m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent32Raw59A1LA.all1LA m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent32Raw59A1RF.all1RF m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent32Raw59A0RD.all0RD m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent32Raw59A1LC.all1LC m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent32Raw59A1RB.all1RB m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent32Raw59A1RD.all1RD m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent32Raw59A0LC.all0LC m hm k d hk hd) (by decide)
  · subst mv; intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent32Raw59A0RE.all0RE m hm k d hk hd) (by decide)

theorem retained_count : (retained closed).length = 7 := by decide

#print axioms closed_sound
#print axioms retained_count
end BB6.Agent32Raw59CanonicalAll
