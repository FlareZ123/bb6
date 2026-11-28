import Raw45ReParent
namespace BB6.Agent24Raw45.ReWitness
open BB6Coverage BB6Coverage.Agent50Zipper BB6.Agent24Raw45.ReAudit BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨false,true,3⟩)
  | _,_ => none

def witness : Machine := fun s => (table s).getD none

theorem witness_compatible : compatible table witness := by
  intro s t h; simp [witness,h]

theorem parent_compatible : compatible Raw45ReParent.parent witness := by
  intro s t h
  have H : allSlots (fun s => if (Raw45ReParent.parent s).isSome then decide (table s = Raw45ReParent.parent s) else true) = true := by decide +kernel
  have hs := allSlots_sound _ H s
  simp only [h,Option.isSome_some,ite_true,decide_eq_true_eq] at hs
  exact witness_compatible s t hs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem exact_halt : HaltsAfter witness 472 := by
  have h : (zrun table 472 start).map (fun z => (z.q,z.l.headD false)) = some (5,false) := by decide +kernel
  cases hz : zrun table 472 start with
  | none => simp [hz] at h
  | some z =>
    have he : (z.q,z.l.headD false) = (5,false) := by simpa only [hz,Option.map_some,Option.some.injEq] using h
    have hr := zrun_sound table witness witness_compatible 472 start z hz
    rw [start_embed] at hr
    have hread : readSlot (embed z) = (5,false) := (read_embed z).trans he
    refine ⟨by simp [hr],?_⟩
    change (run witness 472 blank).bind (rawStep witness) = none
    rw [hr]
    simp only [Option.bind_some,rawStep,hread]
    rfl

theorem exact_parent_max :
    (∀ m, compatible Raw45ReParent.parent m → DecidedBelow 473 m) ∧
    (∃ m, compatible Raw45ReParent.parent m ∧ HaltsAfter m 472) :=
  ⟨Raw45ReParent.cover.sound, witness, parent_compatible, exact_halt⟩

#print axioms exact_parent_max
end BB6.Agent24Raw45.ReWitness
