import Agent46CompleteCut
import Raw13Coupled6Late1LB

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled6Late1LB
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper
open BB6Coverage.Agent10ZipAudit BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent10ZipAudit

def n (d : Bool) : Nat := 2649126+1104*e d

theorem read_ok (d : Bool) : zipRead (p d) (n d) = some (5,false) := by
  have h : (zrun (p d) (n d) BB6Coverage.Agent31Pump.start).map project =
      some ⟨5,[false,false,true,true,true]++rep U 1665,[]⟩ :=
    (run_project _ _ _).trans (trace d)
  change (zrun (p d) (n d) BB6Coverage.Agent31Pump.start).map
    (fun z => (z.q,z.l.headD false)) = some (5,false)
  cases hz : zrun (p d) (n d) BB6Coverage.Agent31Pump.start with
  | none => simp [hz] at h
  | some z =>
    have hh : project z = ⟨5,[false,false,true,true,true]++rep U 1665,[]⟩ := by
      exact Option.some.inj (by simpa only [hz,Option.map_some] using h)
    have hq := congrArg Z0.q hh
    have hl := congrArg Z0.l hh
    change z.q = 5 at hq
    change z.l = [false,false,true,true,true]++rep U 1665 at hl
    simp [hq,hl]

theorem nohalt (d : Bool) : weightedTNFNoAssignedHalt (p d) := by
  intro s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> cases d <;> decide

theorem checked (d : Bool) : zipCheck 2651340 (p d) (.last (n d) (5,false)) = true := by
  simp only [zipCheck,zipQueryOK,read_ok] <;> cases d <;> rfl

theorem bound (d : Bool) (m : Machine) (hm : compatible (p d) m) : WeightedBound 2651340 m :=
  (certifiedZip 2651340 (p d) (.last (n d) (5,false)) (by cases d <;> decide) (nohalt d) (checked d)).sound m hm

def witness (d : Bool) : Machine := weightedTNFDefaultCompletion (p d)

theorem witness_halts (d : Bool) : HaltsAfter (witness d) (n d) := by
  apply (weightedTNF_halt_iff_firstHole (p d) (nohalt d) (n d)).2
  have hr := read_ok d
  rw [zipRead_eq] at hr
  cases hc : knownRun (p d) (n d) with
  | none => simp [hc] at hr
  | some c =>
    have hs : readSlot c = (5,false) := by simpa [hc] using hr
    exact ⟨c,rfl,by rw [hs]; cases d <;> decide⟩

#print axioms read_ok
#print axioms bound
#print axioms witness_halts
end BB6.Agent46Raw13Coupled6Late1LB
