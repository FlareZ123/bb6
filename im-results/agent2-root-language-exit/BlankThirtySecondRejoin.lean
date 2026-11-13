import Lean.Elab.Tactic.Omega
import BlankThirtyFirstRejoin
import E3SourceRejoin
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

def seed33 : DRegular.L := ⟨64*t32+27,0,0⟩

theorem seed33_canon : DRegular.Canon seed33 := by
  constructor
  · dsimp [seed33]
    omega
  · right
    rfl

def duration32 : Nat := BB6.Agent25E3SourceBridge.duration t32

def reentry32Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  exception32Time T22 Tnorm24 Tnorm27 + duration32

/-- Agent 25's physical two-blank bridge closes the q=1,b=1 exception
    and returns to the pure-unary regular section. -/
theorem blank_thirty_second_reentry :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq (run (reentry32Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection seed33) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h32⟩ :=
    blank_thirty_second_exception
  have hbridge :=
    BB6.Agent25E3SourceBridge.q1b1_regular_rejoin t32
  have hroot : ObsEq
      (run duration32
        (DRegularSource.sourceSection ⟨9*t32+4,1,1⟩))
      (DRegularSource.sourceSection seed33) := by
    simpa [duration32,BB6.Agent25E3SourceBridge.sourceStart,
      BB6.Agent25E3SourceBridge.sourceEnd,seed33] using hbridge
  exact ⟨T22,Tnorm24,Tnorm27,
    source_chain (exception32Time T22 Tnorm24 Tnorm27)
      duration32 blank
      (DRegularSource.sourceSection ⟨9*t32+4,1,1⟩)
      (DRegularSource.sourceSection seed33) h32 hroot⟩

#print axioms terminal6106_exact
#print axioms blank_thirty_second_exception
#print axioms blank_thirty_second_reentry

end BB6.Agent2ThirtySecondRejoin
