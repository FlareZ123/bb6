import Lean.Elab.Tactic.Omega
import BlankThirtyThirdRejoin
import ExceptionalBGeneral
import TwelfthPacket
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent37ThirtyFourthToThirtySixthRejoin

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def seed34 : DRegular.L := BB6.Agent2ThirtyThirdRejoin.seed34
def terminal12638 : DRegular.L :=
  (BB6.DRegularFast.fastRun 12638 seed34).getD ⟨9,0,0⟩
def t34 : Nat := (terminal12638.a-4)/9
def seed35 : DRegular.L := ⟨64*t34+29,1,5⟩

def terminal335 : DRegular.L :=
  (BB6.DRegularFast.fastRun 335 seed35).getD ⟨9,0,0⟩
def t35 : Nat := (terminal335.a-4)/9
def seed36 : DRegular.L := ⟨64*t35+35,1,5⟩

def terminal615 : DRegular.L :=
  (BB6.DRegularFast.fastRun 615 seed36).getD ⟨9,0,0⟩
def t36 : Nat := (terminal615.a-10)/9
def seed37 : DRegular.L := ⟨64*t36+91,3,2⟩

private theorem canon_nonzero_q (a q b : Nat)
    (ha : 2 ≤ a) (hq : q ≠ 0) : DRegular.Canon ⟨a,q,b⟩ := by
  constructor
  · exact ha
  · exact Or.inl hq

theorem seed34_canon : DRegular.Canon seed34 :=
  BB6.Agent2ThirtyThirdRejoin.seed34_canon

theorem seed35_canon : DRegular.Canon seed35 := by
  apply canon_nonzero_q
  · dsimp [seed35]
    omega
  · decide

theorem seed36_canon : DRegular.Canon seed36 := by
  apply canon_nonzero_q
  · dsimp [seed36]
    omega
  · decide

theorem seed37_canon : DRegular.Canon seed37 := by
  apply canon_nonzero_q
  · dsimp [seed37]
    omega
  · decide

theorem terminal12638_certificate :
    DRegular.run 12638 seed34 = some ⟨9*t34+4,6,1⟩ ∧
    terminal12638.a % 59049 = 55039 ∧ t34 % 27 = 13 := by
  rw [BB6.DRegularFast.fastRun_correct 12638 seed34 seed34_canon]
  decide

theorem terminal12638_eq :
    terminal12638 = ⟨9*t34+4,6,1⟩ := by
  have hfast : BB6.DRegularFast.fastRun 12638 seed34 =
      some ⟨9*t34+4,6,1⟩ := by
    rw [← BB6.DRegularFast.fastRun_correct 12638 seed34 seed34_canon]
    exact terminal12638_certificate.1
  simp [terminal12638,hfast]

theorem terminal12638_first_stop :
    DRegular.run 12638 seed34 = some terminal12638 ∧
      DRegular.next terminal12638 = none := by
  refine ⟨by simpa [terminal12638_eq] using terminal12638_certificate.1, ?_⟩
  rw [terminal12638_eq]
  have hm : (9*t34+4) % 3 = 1 := by omega
  simp [DRegular.next,hm]

theorem terminal335_certificate :
    DRegular.run 335 seed35 = some ⟨9*t35+4,9,1⟩ ∧
    terminal335.a % 59049 = 54265 ∧ t35 % 27 = 8 := by
  rw [BB6.DRegularFast.fastRun_correct 335 seed35 seed35_canon]
  decide

theorem terminal335_eq :
    terminal335 = ⟨9*t35+4,9,1⟩ := by
  have hfast : BB6.DRegularFast.fastRun 335 seed35 =
      some ⟨9*t35+4,9,1⟩ := by
    rw [← BB6.DRegularFast.fastRun_correct 335 seed35 seed35_canon]
    exact terminal335_certificate.1
  simp [terminal335,hfast]

theorem terminal335_first_stop :
    DRegular.run 335 seed35 = some terminal335 ∧
      DRegular.next terminal335 = none := by
  refine ⟨by simpa [terminal335_eq] using terminal335_certificate.1, ?_⟩
  rw [terminal335_eq]
  have hm : (9*t35+4) % 3 = 1 := by omega
  simp [DRegular.next,hm]

theorem terminal615_certificate :
    DRegular.run 615 seed36 = some ⟨9*t36+10,7,1⟩ ∧
    terminal615.a % 59049 = 27469 ∧ t36 % 27 = 0 := by
  rw [BB6.DRegularFast.fastRun_correct 615 seed36 seed36_canon]
  decide

theorem terminal615_eq :
    terminal615 = ⟨9*t36+10,7,1⟩ := by
  have hfast : BB6.DRegularFast.fastRun 615 seed36 =
      some ⟨9*t36+10,7,1⟩ := by
    rw [← BB6.DRegularFast.fastRun_correct 615 seed36 seed36_canon]
    exact terminal615_certificate.1
  simp [terminal615,hfast]

theorem terminal615_first_stop :
    DRegular.run 615 seed36 = some terminal615 ∧
      DRegular.next terminal615 = none := by
  refine ⟨by simpa [terminal615_eq] using terminal615_certificate.1, ?_⟩
  rw [terminal615_eq]
  have hm : (9*t36+10) % 3 = 1 := by omega
  simp [DRegular.next,hm]

def exception34Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  BB6.Agent2ThirtyThirdRejoin.reentry33Time T22 Tnorm24 Tnorm27 +
    DRegular.accumulated 12638 seed34
def return34Time : Nat :=
  BB6.Agent32EAll.duration (3*t34) 5 + BB6.Agent25BGeneral.bCost t34
def reentry34Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  exception34Time T22 Tnorm24 Tnorm27 + return34Time

theorem blank_thirty_fourth_exception_from
    (T22 Tnorm24 Tnorm27 : Nat)
    (h33 : ObsEq
      (run (BB6.Agent2ThirtyThirdRejoin.reentry33Time T22 Tnorm24 Tnorm27) blank)
      (DRegularSource.sourceSection seed34)) :
    ObsEq
      (run (exception34Time T22 Tnorm24 Tnorm27) blank)
      (DRegularSource.sourceSection terminal12638) := by
  apply BB6.Agent25RootChain.extend_regular blank
    (BB6.Agent2ThirtyThirdRejoin.reentry33Time T22 Tnorm24 Tnorm27)
    12638 seed34 terminal12638
  · exact seed34_canon
  · exact terminal12638_first_stop.1
  · exact h33

theorem blank_thirty_fourth_exception :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq (run (exception34Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection terminal12638) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h33⟩ :=
    BB6.Agent2ThirtyThirdRejoin.blank_thirty_third_reentry
  exact ⟨T22,Tnorm24,Tnorm27,
    blank_thirty_fourth_exception_from T22 Tnorm24 Tnorm27 h33⟩

theorem source_return34 :
    ObsEq (run return34Time (DRegularSource.sourceSection terminal12638))
      (DRegularSource.sourceSection seed35) := by
  rw [terminal12638_eq]
  simpa [return34Time,seed35] using
    (BB6.Agent25BGeneral.exceptional_EB_general t34 4)

theorem blank_thirty_fourth_reentry :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq (run (reentry34Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection seed35) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h34⟩ := blank_thirty_fourth_exception
  exact ⟨T22,Tnorm24,Tnorm27,
    BB6.BoundaryPadding.source_chain
      (exception34Time T22 Tnorm24 Tnorm27) return34Time blank
      (DRegularSource.sourceSection terminal12638)
      (DRegularSource.sourceSection seed35) h34 source_return34⟩

def exception35Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  reentry34Time T22 Tnorm24 Tnorm27 + DRegular.accumulated 335 seed35
def return35Time : Nat :=
  BB6.Agent32EAll.duration (3*t35) 8 + BB6.Agent25BGeneral.bCost t35
def reentry35Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  exception35Time T22 Tnorm24 Tnorm27 + return35Time

theorem blank_thirty_fifth_exception_from
    (T22 Tnorm24 Tnorm27 : Nat)
    (h34 : ObsEq
      (run (reentry34Time T22 Tnorm24 Tnorm27) blank)
      (DRegularSource.sourceSection seed35)) :
    ObsEq
      (run (exception35Time T22 Tnorm24 Tnorm27) blank)
      (DRegularSource.sourceSection terminal335) := by
  apply BB6.Agent25RootChain.extend_regular blank
    (reentry34Time T22 Tnorm24 Tnorm27) 335 seed35 terminal335
  · exact seed35_canon
  · exact terminal335_first_stop.1
  · exact h34

theorem blank_thirty_fifth_exception :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq (run (exception35Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection terminal335) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h34⟩ := blank_thirty_fourth_reentry
  exact ⟨T22,Tnorm24,Tnorm27,
    blank_thirty_fifth_exception_from T22 Tnorm24 Tnorm27 h34⟩

theorem source_return35 :
    ObsEq (run return35Time (DRegularSource.sourceSection terminal335))
      (DRegularSource.sourceSection seed36) := by
  rw [terminal335_eq]
  simpa [return35Time,seed36] using
    (BB6.Agent25BGeneral.exceptional_EB_general t35 7)

theorem blank_thirty_fifth_reentry :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq (run (reentry35Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection seed36) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h35⟩ := blank_thirty_fifth_exception
  exact ⟨T22,Tnorm24,Tnorm27,
    BB6.BoundaryPadding.source_chain
      (exception35Time T22 Tnorm24 Tnorm27) return35Time blank
      (DRegularSource.sourceSection terminal335)
      (DRegularSource.sourceSection seed36) h35 source_return35⟩

def exception36Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  reentry35Time T22 Tnorm24 Tnorm27 + DRegular.accumulated 615 seed36
def return36Time : Nat := BB6.Agent37TwelfthPacket.totalTime t36
def reentry36Time (T22 Tnorm24 Tnorm27 : Nat) : Nat :=
  exception36Time T22 Tnorm24 Tnorm27 + return36Time

theorem blank_thirty_sixth_exception_from
    (T22 Tnorm24 Tnorm27 : Nat)
    (h35 : ObsEq
      (run (reentry35Time T22 Tnorm24 Tnorm27) blank)
      (DRegularSource.sourceSection seed36)) :
    ObsEq
      (run (exception36Time T22 Tnorm24 Tnorm27) blank)
      (DRegularSource.sourceSection terminal615) := by
  apply BB6.Agent25RootChain.extend_regular blank
    (reentry35Time T22 Tnorm24 Tnorm27) 615 seed36 terminal615
  · exact seed36_canon
  · exact terminal615_first_stop.1
  · exact h35

theorem blank_thirty_sixth_exception :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq (run (exception36Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection terminal615) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h35⟩ := blank_thirty_fifth_reentry
  exact ⟨T22,Tnorm24,Tnorm27,
    blank_thirty_sixth_exception_from T22 Tnorm24 Tnorm27 h35⟩

theorem source_return36 :
    ObsEq (run return36Time (DRegularSource.sourceSection terminal615))
      (DRegularSource.sourceSection seed37) := by
  rw [terminal615_eq]
  simpa [return36Time,BB6.Agent37TwelfthPacket.sourceStart,
    BB6.Agent37TwelfthPacket.sourceEnd] using
    (BB6.Agent37TwelfthPacket.two_returns t36)

theorem blank_thirty_sixth_reentry :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq (run (reentry36Time T22 Tnorm24 Tnorm27) blank)
        (DRegularSource.sourceSection seed37) := by
  obtain ⟨T22,Tnorm24,Tnorm27,h36⟩ := blank_thirty_sixth_exception
  exact ⟨T22,Tnorm24,Tnorm27,
    BB6.BoundaryPadding.source_chain
      (exception36Time T22 Tnorm24 Tnorm27) return36Time blank
      (DRegularSource.sourceSection terminal615)
      (DRegularSource.sourceSection seed37) h36 source_return36⟩

#print axioms terminal12638_certificate
#print axioms terminal335_certificate
#print axioms terminal615_certificate
#print axioms blank_thirty_sixth_reentry

end BB6.Agent37ThirtyFourthToThirtySixthRejoin
