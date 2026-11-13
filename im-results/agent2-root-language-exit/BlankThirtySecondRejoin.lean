import Lean.Elab.Tactic.Omega
import BlankThirtyFirstRejoin
import EAllDouble
import EZeroZTwoA
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2ThirtySecondRejoin

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent31PacketSource
open BB6.Agent2ThirtyFirstRejoin

def seed32 : DRegular.L := BB6.Agent2ThirtyFirstRejoin.seed32

def terminal6106 : DRegular.L :=
  (BB6.DRegularFast.fastRun 6106 seed32).getD ⟨9,0,0⟩

def t32 : Nat := (terminal6106.a-4)/9

theorem terminal6106_certificate :
    DRegular.run 6106 seed32 = some ⟨9*t32+4,1,1⟩ ∧
      t32 % 27 = 5 ∧
      terminal6106.a % 59049 = 58126 := by
  have hcanon : DRegular.Canon seed32 :=
    BB6.Agent2ThirtyFirstRejoin.seed32_canon
  rw [BB6.DRegularFast.fastRun_correct 6106 seed32 hcanon]
  decide

theorem terminal6106_exact :
    DRegular.run 6106 seed32 = some ⟨9*t32+4,1,1⟩ :=
  terminal6106_certificate.1

theorem t32_mod27 : t32 % 27 = 5 :=
  terminal6106_certificate.2.1

def exception32Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  BB6.Agent2ThirtyFirstRejoin.reentry31Time T22 Tnorm24 Tnorm27 +
    DRegular.accumulated 6106 seed32

/-- Extend the blank root through the exact 6,106-step regular segment. -/
theorem blank_thirty_second_exception_from
    (T22 Tnorm24 Tnorm27 : Nat)
    (h31 : ObsEq
      (run (BB6.Agent2ThirtyFirstRejoin.reentry31Time
        T22 Tnorm24 Tnorm27) blank)
      (DRegularSource.sourceSection seed32)) :
    ObsEq (run (exception32Time T22 Tnorm24 Tnorm27) blank)
      (DRegularSource.sourceSection ⟨9*t32+4,1,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    (BB6.Agent2ThirtyFirstRejoin.reentry31Time T22 Tnorm24 Tnorm27)
    6106 seed32 ⟨9*t32+4,1,1⟩
  · exact BB6.Agent2ThirtyFirstRejoin.seed32_canon
  · exact terminal6106_exact
  · exact h31

theorem blank_thirty_second_exception :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq (run (exception32Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection ⟨9*t32+4,1,1⟩) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h31⟩ :=
    BB6.Agent2ThirtyFirstRejoin.blank_thirty_first_reentry
  exact ⟨T22,Tnorm24,Tnorm27,
    blank_thirty_second_exception_from T22 Tnorm24 Tnorm27 h31⟩

private theorem input_shape32 :
    DRegularSource.sourceSection ⟨9*t32+4,1,1⟩ =
      init (List.replicate (3*(3*t32)+2) true ++
        false :: (CryptidBoundary.pairs 0 ++ [true,true])) := by
  have hlen : (9*t32+4)-2 = 3*(3*t32)+2 := by omega
  simp only [DRegularSource.sourceSection,init,hlen,List.replicate_one]
  have ho : CryptidBoundary.oppairs (0+1) ++ [true] =
      false :: (CryptidBoundary.pairs 0 ++ [true,true]) := by
    simpa using (BB6.Agent25BGeneral.oppairs_last 0)
  rw [List.append_assoc,ho]

def postZ32 : Cfg :=
  BB6.Agent36EZeroZTwoFollow.postZ (3*t32) 0

def eTime32 : Nat := BB6.Agent32EAll.duration (3*t32) 0
def aTime32 : Nat := BB6.Agent36EZeroZTwoA.aTime t32 0

def seed33 : DRegular.L :=
  ⟨BB6.Agent36EZeroZTwoA.aUnary t32 0,0,0⟩

theorem seed33_a_formula : seed33.a = 64*t32+27 := by
  dsimp [seed33,BB6.Agent36EZeroZTwoA.aUnary,
    BB6.Agent36EZeroZTwoA.aWords]
  simp [CryptidA.wordInc]
  omega

theorem seed33_canon : DRegular.Canon seed33 := by
  constructor
  · rw [seed33_a_formula]
    omega
  · right
    rfl

def reentry32Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  exception32Time T22 Tnorm24 Tnorm27 + (eTime32+aTime32)

/-- The q=1 E-double return is followed by the k=3t, marker-depth-zero
    EZeroZTwoA return, producing a pure-unary regular section. -/
theorem blank_thirty_second_reentry :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq (run (reentry32Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection seed33) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h32⟩ :=
    blank_thirty_second_exception
  have hE0 :=
    BB6.Agent32EAll.all_e_double_implicit_blank (3*t32) 0
  have hE : ObsEq
      (run eTime32 (DRegularSource.sourceSection ⟨9*t32+4,1,1⟩))
      postZ32 := by
    rw [← input_shape32] at hE0
    simpa [eTime32,postZ32,BB6.Agent32EAll.output,
      BB6.Agent36EZeroZTwoFollow.postZ,
      BB6.Agent32EZero.packetZero] using hE0
  have hA0 :=
    BB6.Agent36EZeroZTwoA.a_follow_multiple_three t32 0
  have htarget :
      (⟨[],false,List.replicate seed33.a true,5⟩ : Cfg) =
        DRegularSource.sourceSection seed33 := by
    have hreg :=
      BB6.Agent2TwentyThirdRoot.regularSection_sourceSection
        seed33.a 0 0 (by rw [seed33_a_formula]; omega)
    simpa [seed33,BB6.Agent2BoundaryBZero.regularSection,
      CryptidBoundary.oppairs] using hreg
  have hA : ObsEq (run aTime32 postZ32)
      (DRegularSource.sourceSection seed33) := by
    have hrun :
        run aTime32 postZ32 =
          (⟨[],false,List.replicate seed33.a true,5⟩ : Cfg) := by
      simpa [aTime32,postZ32,seed33] using hA0
    rw [hrun,htarget]
    rfl
  have hroot : ObsEq
      (run (eTime32+aTime32)
        (DRegularSource.sourceSection ⟨9*t32+4,1,1⟩))
      (DRegularSource.sourceSection seed33) := by
    exact source_chain eTime32 aTime32
      (DRegularSource.sourceSection ⟨9*t32+4,1,1⟩)
      postZ32 (DRegularSource.sourceSection seed33) hE hA
  exact ⟨T22,Tnorm24,Tnorm27,
    source_chain (exception32Time T22 Tnorm24 Tnorm27)
      (eTime32+aTime32) blank
      (DRegularSource.sourceSection ⟨9*t32+4,1,1⟩)
      (DRegularSource.sourceSection seed33) h32 hroot⟩

#print axioms terminal6106_exact
#print axioms blank_thirty_second_exception
#print axioms blank_thirty_second_reentry

end BB6.Agent2ThirtySecondRejoin
