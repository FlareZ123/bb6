import Lean.Elab.Tactic.Omega
import BlankThirtyFourthToThirtySixthRejoin
import ExceptionalBGeneral
import E3SourceRejoin
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent37ThirtySeventhToThirtyEighthRejoin

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def seed37 : DRegular.L :=
  BB6.Agent37ThirtyFourthToThirtySixthRejoin.seed37

def terminal2348 : DRegular.L :=
  (BB6.Agent2Fast64.fastRun 2348 seed37).getD ⟨9,0,0⟩
def t37 : Nat := (terminal2348.a-4)/9
def seed38 : DRegular.L := ⟨64*t37+29,1,5⟩

def terminal1341 : DRegular.L :=
  (BB6.Agent2Fast64.fastRun 1341 seed38).getD ⟨9,0,0⟩
def t38 : Nat := (terminal1341.a-10)/9
def seed39 : DRegular.L := ⟨64*t38+49,6,0⟩

private theorem canon_nonzero_q (a q b : Nat)
    (ha : 2 ≤ a) (hq : q ≠ 0) : DRegular.Canon ⟨a,q,b⟩ := by
  constructor
  · exact ha
  · exact Or.inl hq

theorem seed37_canon : DRegular.Canon seed37 :=
  BB6.Agent37ThirtyFourthToThirtySixthRejoin.seed37_canon

theorem seed38_canon : DRegular.Canon seed38 := by
  apply canon_nonzero_q
  · dsimp [seed38]
    omega
  · decide

theorem seed39_canon : DRegular.Canon seed39 := by
  apply canon_nonzero_q
  · dsimp [seed39]
    omega
  · decide

/-- Exact q=6 first stop after the q=7 E/A return. -/
theorem terminal2348_certificate :
    DRegular.run 2348 seed37 = some ⟨9*t37+4,6,1⟩ ∧
    terminal2348.a % 59049 = 50584 ∧
    t37 % 27 = 4 := by
  rw [BB6.Agent2Fast64.fastRun_correct 2348 seed37 seed37_canon]
  decide

theorem terminal2348_eq :
    terminal2348 = ⟨9*t37+4,6,1⟩ := by
  have hfast : BB6.Agent2Fast64.fastRun 2348 seed37 =
      some ⟨9*t37+4,6,1⟩ := by
    rw [← BB6.Agent2Fast64.fastRun_correct 2348 seed37 seed37_canon]
    exact terminal2348_certificate.1
  simp [terminal2348,hfast]

theorem terminal2348_first_stop :
    DRegular.run 2348 seed37 = some terminal2348 ∧
      DRegular.next terminal2348 = none := by
  refine ⟨by simpa [terminal2348_eq] using terminal2348_certificate.1, ?_⟩
  rw [terminal2348_eq]
  have hm : (9*t37+4) % 3 = 1 := by omega
  simp [DRegular.next,hm]

/-- Exact q=1 first stop after the q=6 E/B return. -/
theorem terminal1341_certificate :
    DRegular.run 1341 seed38 = some ⟨9*t38+10,1,1⟩ ∧
    terminal1341.a % 59049 = 24670 ∧
    t38 % 27 = 13 := by
  rw [BB6.Agent2Fast64.fastRun_correct 1341 seed38 seed38_canon]
  decide

theorem terminal1341_eq :
    terminal1341 = ⟨9*t38+10,1,1⟩ := by
  have hfast : BB6.Agent2Fast64.fastRun 1341 seed38 =
      some ⟨9*t38+10,1,1⟩ := by
    rw [← BB6.Agent2Fast64.fastRun_correct 1341 seed38 seed38_canon]
    exact terminal1341_certificate.1
  simp [terminal1341,hfast]

theorem terminal1341_first_stop :
    DRegular.run 1341 seed38 = some terminal1341 ∧
      DRegular.next terminal1341 = none := by
  refine ⟨by simpa [terminal1341_eq] using terminal1341_certificate.1, ?_⟩
  rw [terminal1341_eq]
  have hm : (9*t38+10) % 3 = 1 := by omega
  simp [DRegular.next,hm]

def exception37Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  BB6.Agent37ThirtyFourthToThirtySixthRejoin.reentry36Time
    T22 Tnorm24 Tnorm27 +
    DRegular.accumulated 2348 seed37

def return37Time : Nat :=
  BB6.Agent32EAll.duration (3*t37) 5 +
    BB6.Agent25BGeneral.bCost t37

def reentry37Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  exception37Time T22 Tnorm24 Tnorm27 + return37Time

theorem blank_thirty_seventh_exception_from
    (T22 Tnorm24 Tnorm27 : Nat)
    (h36 : ObsEq
      (run (BB6.Agent37ThirtyFourthToThirtySixthRejoin.reentry36Time
        T22 Tnorm24 Tnorm27) blank)
      (DRegularSource.sourceSection seed37)) :
    ObsEq
      (run (exception37Time T22 Tnorm24 Tnorm27) blank)
      (DRegularSource.sourceSection terminal2348) := by
  apply BB6.Agent25RootChain.extend_regular blank
    (BB6.Agent37ThirtyFourthToThirtySixthRejoin.reentry36Time
      T22 Tnorm24 Tnorm27)
    2348 seed37 terminal2348
  · exact seed37_canon
  · exact terminal2348_first_stop.1
  · exact h36

theorem blank_thirty_seventh_exception :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq
        (run (exception37Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection terminal2348) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h36⟩ :=
    BB6.Agent37ThirtyFourthToThirtySixthRejoin.blank_thirty_sixth_reentry
  exact ⟨T22,Tnorm24,Tnorm27,
    blank_thirty_seventh_exception_from T22 Tnorm24 Tnorm27 h36⟩

theorem source_return37 :
    ObsEq
      (run return37Time (DRegularSource.sourceSection terminal2348))
      (DRegularSource.sourceSection seed38) := by
  rw [terminal2348_eq]
  simpa [return37Time,seed38] using
    (BB6.Agent25BGeneral.exceptional_EB_general t37 4)

theorem blank_thirty_seventh_reentry :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq
        (run (reentry37Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection seed38) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h37⟩ :=
    blank_thirty_seventh_exception
  exact ⟨T22,Tnorm24,Tnorm27,
    BB6.BoundaryPadding.source_chain
      (exception37Time T22 Tnorm24 Tnorm27) return37Time blank
      (DRegularSource.sourceSection terminal2348)
      (DRegularSource.sourceSection seed38)
      h37 source_return37⟩

def exception38Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  reentry37Time T22 Tnorm24 Tnorm27 +
    DRegular.accumulated 1341 seed38

def return38Time : Nat := BB6.Agent25E3SourceBridge.eDuration t38

def reentry38Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  exception38Time T22 Tnorm24 Tnorm27 + return38Time

theorem blank_thirty_eighth_exception_from
    (T22 Tnorm24 Tnorm27 : Nat)
    (h37 : ObsEq
      (run (reentry37Time T22 Tnorm24 Tnorm27) blank)
      (DRegularSource.sourceSection seed38)) :
    ObsEq
      (run (exception38Time T22 Tnorm24 Tnorm27) blank)
      (DRegularSource.sourceSection terminal1341) := by
  apply BB6.Agent25RootChain.extend_regular blank
    (reentry37Time T22 Tnorm24 Tnorm27)
    1341 seed38 terminal1341
  · exact seed38_canon
  · exact terminal1341_first_stop.1
  · exact h37

theorem blank_thirty_eighth_exception :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq
        (run (exception38Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection terminal1341) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h37⟩ := blank_thirty_seventh_reentry
  exact ⟨T22,Tnorm24,Tnorm27,
    blank_thirty_eighth_exception_from T22 Tnorm24 Tnorm27 h37⟩

theorem source_return38 :
    ObsEq
      (run return38Time (DRegularSource.sourceSection terminal1341))
      (DRegularSource.sourceSection seed39) := by
  rw [terminal1341_eq]
  simpa [return38Time,seed39,
    BB6.Agent25E3SourceBridge.sourceStartK,
    BB6.Agent25E3SourceBridge.eDuration] using
    (BB6.Agent25E3SourceBridge.q1b1_regular_rejoin_E t38)

theorem blank_thirty_eighth_reentry :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq
        (run (reentry38Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection seed39) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h38⟩ :=
    blank_thirty_eighth_exception
  exact ⟨T22,Tnorm24,Tnorm27,
    BB6.BoundaryPadding.source_chain
      (exception38Time T22 Tnorm24 Tnorm27) return38Time blank
      (DRegularSource.sourceSection terminal1341)
      (DRegularSource.sourceSection seed39)
      h38 source_return38⟩

#print axioms terminal2348_certificate
#print axioms terminal1341_certificate
#print axioms blank_thirty_eighth_reentry

end BB6.Agent37ThirtySeventhToThirtyEighthRejoin
