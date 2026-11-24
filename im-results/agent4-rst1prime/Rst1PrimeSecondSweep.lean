import Rst1PrimeBridge8Source
import CountedRst1Prime
import CountedSuffixOutput
import Lean.Elab.Tactic.Omega

/-!
# Second counted sweep in the Rst1' itinerary

After bridge8, its output window contributes two leading ones.  The
unmodified source suffix contributes one final d0 bit, the complete
d1^L block, and the first two lh bits.  These concatenate to exactly
3L+5 ones, with a zero immediately right of the new head.  Thus the
second counted left sweep is an exact original-machine run.
-/

namespace BB6Coverage.Agent4Rst1Prime

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent8Rst1Prime
open BB6Coverage.Agent8CountedReset

/-- The source tail after markerWord 1 ++ d0 is one through the end of
d1^L and the first two cells of lh. -/
theorem rst1Prime_source_tail_ones
    (L j : Nat) (hj : j ≤ 3*L+2) :
    sideBit (markerWord 1 ++ d0 ++ binDec L 0 ++ lh) (5+j) = true := by
  have hmark : (markerWord 1).length = 3 := by decide
  have hd0 : d0.length = 3 := by decide
  simp only [List.append_assoc]
  rw [sideBit_append]
  rw [hmark]
  have hnot1 : ¬ 5+j < 3 := by omega
  simp only [if_neg hnot1]
  have hindex1 : 5+j-3 = 2+j := by omega
  rw [hindex1,sideBit_append]
  rw [hd0]
  by_cases hj0 : j=0
  · subst j
    simp [d0,sideBit]
  · have hnot2 : ¬ 2+j < 3 := by omega
    simp only [if_neg hnot2]
    have hindex2 : 2+j-3 = j-1 := by omega
    rw [hindex2,binDec_zero,sideBit_append,d1pow_length]
    by_cases hjL : j ≤ 3*L
    · have hlt : j-1 < 3*L := by omega
      simp only [if_pos hlt]
      exact sideBit_d1pow_true L (j-1) hlt
    · have hnotL : ¬ j-1 < 3*L := by omega
      simp only [if_neg hnotL]
      have hcases : j=3*L+1 ∨ j=3*L+2 := by omega
      rcases hcases with hj1 | hj2
      · subst j
        simp [sideBit,lh]
      · subst j
        simp [sideBit,lh]

/-- Full original-source configuration after the first counted sweep and
the eight-step bridge8. -/
def rst1PrimeAfterBridge8
    (L a b : Nat) (h : Int) : Config :=
  BB6Coverage.Agent8Rst1Prime.frameAt
    (sweptLeft (3*a+1) (s1Config L 0 1 a 0 b h).tape h)
    (h-((3*a+1:Int))) BB6Coverage.Agent8Rst1Prime.inside8 BB6Coverage.Agent8Rst1Prime.bridge8End

/-- The second sweep has exactly 3L+5 left-facing ones and a zero
immediately right of the head. -/
theorem rst1Prime_secondSweep_preconditions
    (L a b : Nat) (h : Int) :
    leftOnes (rst1PrimeAfterBridge8 L a b h).tape
      (h-((3*a+1:Int))-2) (3*L+5) ∧
    (rst1PrimeAfterBridge8 L a b h).tape
      (h-((3*a+1:Int))-1) = false := by
  let H : Int := h-((3*a+1:Int))
  let T : Int → Bool := sweptLeft (3*a+1)
    (s1Config L 0 1 a 0 b h).tape h
  change leftOnes (BB6Coverage.Agent8Rst1Prime.frameAt T H BB6Coverage.Agent8Rst1Prime.inside8 BB6Coverage.Agent8Rst1Prime.bridge8End).tape (H-2) (3*L+5) ∧
    (BB6Coverage.Agent8Rst1Prime.frameAt T H BB6Coverage.Agent8Rst1Prime.inside8 BB6Coverage.Agent8Rst1Prime.bridge8End).tape (H-1) = false
  constructor
  · intro i hi
    by_cases hi2 : i < 2
    · have hcases : i=0 ∨ i=1 := by omega
      rcases hcases with h0 | h1
      · subst i
        have hr : H - 2 - H = -2 := by omega
        simp [BB6Coverage.Agent8Rst1Prime.frameAt_tape, hr,BB6Coverage.Agent8Rst1Prime.inside8,BB6Coverage.Agent8Rst1Prime.inWindow,BB6Coverage.Agent8Rst1Prime.bridge8End]
      · subst i
        have hr : H - 2 - (1 : Int) - H = -3 := by omega
        simp [BB6Coverage.Agent8Rst1Prime.frameAt_tape, hr,BB6Coverage.Agent8Rst1Prime.inside8,BB6Coverage.Agent8Rst1Prime.inWindow,BB6Coverage.Agent8Rst1Prime.bridge8End]
    · let j := i-2
      have hj : j ≤ 3*L+2 := by omega
      have hpos : H-2-(i:Int) = H-4-(j:Int) := by omega
      have hrel : (H-2-(i:Int))-H = -2-(i:Int) := by omega
      have hout : BB6Coverage.Agent8Rst1Prime.inside8 ((H-2-(i:Int))-H) = false := by
        simp [BB6Coverage.Agent8Rst1Prime.inside8,BB6Coverage.Agent8Rst1Prime.inWindow,hrel]
        omega
      rw [BB6Coverage.Agent8Rst1Prime.frameAt_tape]
      simp only [hout, Bool.false_eq_true, if_false]
      rw [hpos]
      dsimp [T]
      have hunchanged :
          sweptLeft (3*a+1) (s1Config L 0 1 a 0 b h).tape h
            (H-4-(j:Int)) =
          (s1Config L 0 1 a 0 b h).tape (H-4-(j:Int)) := by
        apply sweptLeft_eq_of_le
        dsimp [H]
        omega
      rw [hunchanged]
      have hcoord :
          H-4-(j:Int) = h-((3*a+1+(4+j):Int)) := by
        dsimp [H]
        omega
      have hcoord' : H-4-(j:Int) = h-((3*a+1:Int)+(↑(4+j):Int)) := by omega
      rw [hcoord',s1Config_left_after_d1pow]
      rw [show 4+j+1 = 5+j by omega]
      exact rst1Prime_source_tail_ones L j hj
  · rw [BB6Coverage.Agent8Rst1Prime.frameAt_tape]
    have hrel : (H-1)-H = -1 := by omega
    rw [hrel]
    simp [BB6Coverage.Agent8Rst1Prime.inside8,BB6Coverage.Agent8Rst1Prime.inWindow,BB6Coverage.Agent8Rst1Prime.bridge8End]

/-- Exact original-machine run through the second counted left sweep,
following the first sweep and bridge8. -/
theorem rst1Prime_secondSweep_run
    (L a b : Nat) (h : Int) :
    run tm2 (9*a+3+8 + 3*(3*L+5))
      (s1Config L 0 1 a 0 b h) =
      some ⟨3,
        (h-((3*a+1:Int))-2)-((3*L+5:Int)),
        sweptLeft (3*L+5) (rst1PrimeAfterBridge8 L a b h).tape
          (h-((3*a+1:Int))-2)⟩ := by
  have hprefix := rst1Prime_bridge8_after_firstSweep L a b h
  have hpre := rst1Prime_secondSweep_preconditions L a b h
  have hrun := counted_left_sweep (3*L+5)
    (rst1PrimeAfterBridge8 L a b h).tape
    (h-((3*a+1:Int))-2) hpre.1 (by
      rw [show h-((3*a+1:Int))-2+1 = h-((3*a+1:Int))-1 by omega]
      exact hpre.2)
  rw [run_add,hprefix]
  simp only [Option.bind_some]
  have hcfg : BB6Coverage.Agent8Rst1Prime.frameAt
      (sweptLeft (3*a+1) (s1Config L 0 1 a 0 b h).tape h)
      (h-((3*a+1:Int))) inside8 bridge8End =
      (⟨3, h-((3*a+1:Int))-2, (rst1PrimeAfterBridge8 L a b h).tape⟩ : Config) := by
    apply BB6Coverage.Agent8Rst1Prime.config_ext
    · simp [bridge8End]
    · simp [bridge8End]
      omega
    · rfl
  rw [hcfg]
  exact hrun

#print axioms rst1Prime_source_tail_ones
#print axioms rst1PrimeAfterBridge8
#print axioms rst1Prime_secondSweep_preconditions
#print axioms rst1Prime_secondSweep_run

end BB6Coverage.Agent4Rst1Prime
