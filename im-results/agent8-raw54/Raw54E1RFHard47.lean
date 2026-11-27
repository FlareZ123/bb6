import Raw54E1RF47Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RF47
open BB6Coverage BB6Coverage.Agent31Pump

def goodB (m : M (ML × MR)) : Bool := m.all (fun o => match o with | none => false | some c => states.contains c)
def check : Bool := states.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r))

theorem check0 : chunk0.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check1 : chunk1.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check2 : chunk2.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check3 : chunk3.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check4 : chunk4.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check5 : chunk5.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check6 : chunk6.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check7 : chunk7.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check8 : chunk8.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check9 : chunk9.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check10 : chunk10.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check11 : chunk11.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check12 : chunk12.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check13 : chunk13.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check14 : chunk14.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check15 : chunk15.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check16 : chunk16.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check17 : chunk17.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check18 : chunk18.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check19 : chunk19.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check20 : chunk20.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check21 : chunk21.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check22 : chunk22.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check23 : chunk23.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check24 : chunk24.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check25 : chunk25.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check26 : chunk26.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check27 : chunk27.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check28 : chunk28.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check29 : chunk29.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check30 : chunk30.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check31 : chunk31.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check32 : chunk32.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check33 : chunk33.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check34 : chunk34.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check35 : chunk35.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check36 : chunk36.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check37 : chunk37.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check38 : chunk38.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check39 : chunk39.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check40 : chunk40.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check41 : chunk41.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check42 : chunk42.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check43 : chunk43.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check44 : chunk44.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check45 : chunk45.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check46 : chunk46.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check47 : chunk47.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check48 : chunk48.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check49 : chunk49.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check50 : chunk50.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check51 : chunk51.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check52 : chunk52.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide
theorem check53 : chunk53.all (fun (l,r) => goodB (advanceA leftEdges rightEdges l r)) = true := by decide

theorem checked : check = true := by
  simp only [check,states,List.all_append,check0, check1, check2, check3, check4, check5, check6, check7, check8, check9, check10, check11, check12, check13, check14, check15, check16, check17, check18, check19, check20, check21, check22, check23, check24, check25, check26, check27, check28, check29, check30, check31, check32, check33, check34, check35, check36, check37, check38, check39, check40, check41, check42, check43, check44, check45, check46, check47, check48, check49, check50, check51, check52, check53,Bool.true_and]

theorem closure (l : ML) (r : MR) (h : (l,r) ∈ states) : Good (advanceA leftEdges rightEdges l r) (fun c => c ∈ states) := by
  have hc := List.all_eq_true.mp checked (l,r) h
  intro o ho
  have hh := List.all_eq_true.mp hc o ho
  cases o with
  | none => contradiction
  | some c => exact List.contains_iff_mem.mp hh

def invariant (z : Z0) : Prop :=
  ∃ l r ls rs, zrel z (cfg l r) ∧ LRep leftEdges l ls ∧ RRep rightEdges r rs ∧ (ls,rs) ∈ states

theorem entry : run0 table 20 ⟨0,[],[]⟩ = some (cfg [] [(0,3),(1,1)]) := by rfl

theorem initial : invariant (cfg [] [(0,3),(1,1)]) := by
  refine ⟨[],[(0,3),(1,1)],[],[(0,3),(1,1)],zrel_refl _,Rep.nil,?_,by decide⟩
  change Rep rightEdges [(0,3),(1,1)] [(0,3),(1,1)]
  exact Rep.cons (Rep.cons Rep.nil (by decide)) (by decide)

theorem progress (z : Z0) (h : invariant z) : ∃ t d, 0<t ∧ run0 table t z = some d ∧ invariant d := by
  obtain ⟨l,r,ls,rs,hrel,hl,hr,hc⟩ := h
  obtain ⟨l',r',ls',rs',hg,hl',hr',hc'⟩ := advanceA_sound hl hr (closure ls rs hc)
  obtain ⟨t,d,ht,hd,hrel'⟩ := goes_congr (zrel_symm hrel) (zrel_refl (cfg l' r')) hg
  exact ⟨t,d,ht,hd,l',r',ls',rs',hrel',hl',hr',hc'⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  have arbitrary : ∀ k, ∃ t z, k ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some z ∧ invariant z := by
    intro k
    induction k with
    | zero => exact ⟨20,_,by decide,entry,initial⟩
    | succ k ih =>
      obtain ⟨t,z,ht,hr,hi⟩ := ih
      obtain ⟨u,d,hu,hd,hi'⟩ := progress z hi
      exact ⟨t+u,d,by omega,join0 hr hd,hi'⟩
  intro n
  obtain ⟨t,z,ht,hr,_⟩ := arbitrary n
  have hz : (BB6Coverage.Agent50Zipper.zrun table t start).map project = some z := (run_project table t start).trans hr
  cases h : BB6Coverage.Agent50Zipper.zrun table t start with
  | none => simp [h] at hz
  | some zz =>
    have H := BB6Coverage.Agent50Zipper.zrun_sound table m hm t start zz h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms checked
#print axioms never
end BB6.Agent8Raw54.RF47
