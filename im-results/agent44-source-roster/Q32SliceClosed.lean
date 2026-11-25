import Q32SliceData
import Q32CubicSweep
import Q32SweepData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent44Q32Slice
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent47PartialAudit BB6Coverage.Agent31Pump

def sweepTables : List PartialMachine := [Q32Cubic.table,MQ32_1.table,MQ32_2.table,MQ32_3.table,MQ32_4.table,MQ32_5.table,MQ32_6.table,MQ32_7.table,MQ32_8.table,MQ32_9.table,MQ32_10.table,MQ32_11.table,MQ32_12.table,MQ32_13.table]
theorem sweepTables_never : ∀ p ∈ sweepTables, ∀ m, compatible p m → NeverHalts m := by
  intro p hp m hm
  simp only [sweepTables,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact Q32Cubic.never m hm
  · exact MQ32_1.never m hm
  · exact MQ32_2.never m hm
  · exact MQ32_3.never m hm
  · exact MQ32_4.never m hm
  · exact MQ32_5.never m hm
  · exact MQ32_6.never m hm
  · exact MQ32_7.never m hm
  · exact MQ32_8.never m hm
  · exact MQ32_9.never m hm
  · exact MQ32_10.never m hm
  · exact MQ32_11.never m hm
  · exact MQ32_12.never m hm
  · exact MQ32_13.never m hm

theorem residualTables9_covered :
    (partialResiduals p9 audit9).all
      (fun e => sweepTables.any (fun t => tableOK e.2 t)) = true := by decide

theorem residualTables11_covered :
    (partialResiduals p11 audit11).all
      (fun e => sweepTables.any (fun t => tableOK e.2 t)) = true := by decide

theorem residual_never (p : PartialMachine)
    (h : sweepTables.any (fun t => tableOK p t) = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  obtain ⟨t,ht,heq⟩ := List.any_eq_true.mp h
  have htable := tableOK_sound p t heq
  rw [htable] at hm
  exact sweepTables_never t ht m hm

theorem safe9 (m : Machine) (hm : compatible p9 m) : WeightedBound 144 m := by
  rcases coverage9 m hm with hb | ⟨e,he,hc⟩
  · exact hb
  · exact weighted_never 144 m
      (residual_never e.2 (List.all_eq_true.mp residualTables9_covered e he) m hc)

theorem safe11 (m : Machine) (hm : compatible p11 m) : WeightedBound 144 m := by
  rcases coverage11 m hm with hb | ⟨e,he,hc⟩
  · exact hb
  · exact weighted_never 144 m
      (residual_never e.2 (List.all_eq_true.mp residualTables11_covered e he) m hc)

def allTwelve : List PartialMachine := [p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11]
theorem allTwelve_sound : ∀ p ∈ allTwelve, ∀ m, compatible p m → WeightedBound 144 m := by
  intro p hp m hc
  simp only [allTwelve,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact safe0 m hc
  · exact safe1 m hc
  · exact safe2 m hc
  · exact safe3 m hc
  · exact safe4 m hc
  · exact safe5 m hc
  · exact safe6 m hc
  · exact safe7 m hc
  · exact safe8 m hc
  · exact safe9 m hc
  · exact safe10 m hc
  · exact safe11 m hc

#print axioms sweepTables_never
#print axioms safe9
#print axioms safe11
#print axioms allTwelve_sound
end BB6.Agent44Q32Slice
