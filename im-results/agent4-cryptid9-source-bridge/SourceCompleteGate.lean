import SourceTComplete

namespace Agent4CompleteGate
open Agent9SourceSRun Agent9SProjection
open Agent4TComplete
open BusyBeaver.M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB

def fatalSResidue (q : Nat) : Prop :=
   q%729=0 ∨ q%729=81 ∨ q%729=243 ∨ q%729=324 ∨
   q%729=405 ∨ q%729=486 ∨ q%729=567

theorem residue_equiv (b : Nat) (h : (b+16)%3=0) :
    ((4*(b/3)+7)%243=10 ∨ (4*(b/3)+7)%243=37 ∨
     (4*(b/3)+7)%243=64 ∨ (4*(b/3)+7)%243=91 ∨
     (4*(b/3)+7)%243=145 ∨ (4*(b/3)+7)%243=172 ∨
     (4*(b/3)+7)%243=226) ↔ fatalSResidue (b+16) := by
  unfold fatalSResidue
  omega

theorem source_two_stage_halt_iff (b c : Nat)
   (ht : Sstep (b+16) c = none) :
   (highLevelNext (.S b c)).bind highLevelNext = none ↔
       fatalSResidue (b+16) := by
  have hq : (b+16)%3=0 := by
    unfold Sstep at ht
    by_cases hx : (b+16)%3=0
    · exact hx
    · by_cases hy : (b+16)%3=1
      · simp [hx,hy] at ht
      · simp [hx,hy] at ht
  have hc : c=0 := by simpa [Sstep,hq] using ht
  have hb0 : b%3≠0 := by omega
  have hb1 : b%3≠1 := by omega
  have hs : highLevelNext (.S b c) =
       some (.T (4*(b/3)+7)) := by
    simp [highLevelNext,hb0,hb1,hc]
    omega
  rw [hs]
  simpa using (t_none_seven_residues (4*(b/3)+7)).trans
     (residue_equiv b hq)

#print axioms residue_equiv
#print axioms source_two_stage_halt_iff
end Agent4CompleteGate
