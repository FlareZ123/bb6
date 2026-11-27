import Agent46CompleteCut
import Raw13Coupled6LateCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled6LateCore
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper
open BB6Coverage.Agent10ZipAudit BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent10ZipAudit

def Dtab (d : Bool) : PartialMachine := p d 14
def Rtab : PartialMachine := p true 15
def nD (d : Bool) : Nat := 2649120+1104*e d

theorem shared_read (p : PartialMachine) (n : Nat)
    (h0 : run0 p n (R0 []) = some ⟨5,[false,false,true,true,true]++rep U 1665,[]⟩) :
    zipRead p n = some (5,false) := by
  have h : (zrun p n BB6Coverage.Agent31Pump.start).map project =
      some ⟨5,[false,false,true,true,true]++rep U 1665,[]⟩ :=
    (run_project _ _ _).trans h0
  change (zrun p n BB6Coverage.Agent31Pump.start).map
    (fun z => (z.q,z.l.headD false)) = some (5,false)
  cases hz : zrun p n BB6Coverage.Agent31Pump.start with
  | none => simp [hz] at h
  | some z =>
    have hh : project z = ⟨5,[false,false,true,true,true]++rep U 1665,[]⟩ := by
      exact Option.some.inj (by simpa only [hz,Option.map_some] using h)
    have hq := congrArg Z0.q hh
    have hl := congrArg Z0.l hh
    change z.q = 5 at hq
    change z.l = [false,false,true,true,true]++rep U 1665 at hl
    simp [hq,hl]

theorem readD (d : Bool) : zipRead (Dtab d) (nD d) = some (5,false) :=
  shared_read _ _ (traceBD d true)

theorem readR : zipRead Rtab 2651340 = some (5,false) :=
  shared_read _ _ traceR

theorem nohaltD (d : Bool) : weightedTNFNoAssignedHalt (Dtab d) := by
  intro s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> cases d <;> decide

theorem nohaltR : weightedTNFNoAssignedHalt Rtab := by
  intro s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

theorem checkedD (d : Bool) : zipCheck 2651346 (Dtab d) (.last (nD d) (5,false)) = true := by
  simp only [zipCheck,zipQueryOK,readD] <;> cases d <;> rfl

theorem checkedR : zipCheck 2651346 Rtab (.last 2651340 (5,false)) = true := by
  simp only [zipCheck,zipQueryOK,readR] <;> rfl

theorem boundD (d : Bool) (m : Machine) (hm : compatible (Dtab d) m) : WeightedBound 2651346 m :=
  (certifiedZip 2651346 (Dtab d) (.last (nD d) (5,false)) (by cases d <;> decide) (nohaltD d) (checkedD d)).sound m hm

theorem boundR (m : Machine) (hm : compatible Rtab m) : WeightedBound 2651346 m :=
  (certifiedZip 2651346 Rtab (.last 2651340 (5,false)) (by decide) nohaltR checkedR).sound m hm

#print axioms readD
#print axioms readR
#print axioms boundD
#print axioms boundR
end BB6.Agent46Raw13Coupled6LateCore
