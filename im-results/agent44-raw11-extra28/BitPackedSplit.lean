import BitPackedStack
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent44BitPackedSplit
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent13BitPacked

/-- A proof-oriented form of the bit-packed checker. It avoids forcing all
    independently kernel-checked row chunks back through one giant Boolean
    reduction. The hypotheses are exactly the components used by the
    invariant soundness proof. -/
structure SplitCheck (p : PartialMachine) (c : Cert) : Prop where
  left_pos : 0 < c.left.size
  right_pos : 0 < c.right.size
  left_zero : (false,0) ∈ c.left.pop 0
  right_zero : (false,0) ∈ c.right.pop 0
  start : stateOK c 0 false 0 0 = true
  valid : ∀ (q : Fin 6) (a : Bool), (row c q a).valid = true
  chunks : ∀ (q : Fin 6) (a : Bool) (xs : List Nat),
    xs ∈ (row c q a).chunks → indicesCheck p c q a xs = true

theorem state_checked {p c q a l r} (h : SplitCheck p c)
    (hr : r < c.right.size) (hs : stateOK c q a l r = true) :
    stateStepOK p c q a l r = true := by
  have hi := Row.mem (h.valid q a) hs
  obtain ⟨chunk, hchunk, hmem⟩ := List.mem_flatten.mp hi
  have H := List.all_eq_true.mp (h.chunks q a chunk hchunk) _ hmem
  change stateStepOK p c q a ((r+c.right.size*l)/c.right.size) ((r+c.right.size*l)%c.right.size) = true at H
  rw [Nat.add_mul_div_left _ _ h.right_pos, Nat.div_eq_of_lt hr, Nat.zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr] at H
  exact H

theorem inv_start {p c} (h : SplitCheck p c) : Inv c ⟨0,[],[]⟩ := by
  exact ⟨0,0,⟨h.left_pos,rfl⟩,⟨h.right_pos,rfl⟩,h.start⟩

theorem inv_step {p c z} (hc : SplitCheck p c) (hz : Inv c z) :
    ∃ t, step0 p z = some t ∧ Inv c t := by
  obtain ⟨q,l,r⟩ := z
  obtain ⟨i,j,hl,hr,hs⟩ := hz
  change c.left.Tape l.tail i at hl
  change c.right.Tape r j at hr
  change stateOK c q (l.headD false) i j = true at hs
  have h := state_checked hc (Stack.bound hr) hs
  cases hm : p (q,l.headD false) with
  | none => simp only [stateStepOK,hm,Bool.false_eq_true] at h
  | some op =>
    cases op with
    | none => simp only [stateStepOK,hm,Bool.false_eq_true] at h
    | some mv =>
      refine ⟨move0 mv ⟨q,l,r⟩, by simp only [step0,hm,Option.bind_some,id_eq,Option.map_some], ?_⟩
      cases hd : mv.right with
      | false =>
        simp only [stateStepOK,hm,hd,Bool.false_eq_true,ite_false,Bool.and_eq_true,
          List.all_eq_true,decide_eq_true_eq,List.contains_iff_mem] at h
        obtain ⟨k,hk,he⟩ := Stack.pop_sound hc.left_zero hl
        have hp : c.right.Tape (mv.write::r) (c.right.push j mv.write) := ⟨h.1.1,j,hr,h.1.2⟩
        have hs' := h.2 (l.tail.headD false,k) he
        simpa only [BB6.Agent13BitPacked.Inv,move0,hd,Bool.false_eq_true,ite_false] using
          (show ∃ a b, c.left.Tape l.tail.tail a ∧ c.right.Tape (mv.write::r) b ∧
            stateOK c mv.next (l.tail.headD false) a b = true from ⟨k,_,hk,hp,hs'⟩)
      | true =>
        simp only [stateStepOK,hm,hd,ite_true,Bool.and_eq_true,List.all_eq_true,
          decide_eq_true_eq,List.contains_iff_mem] at h
        obtain ⟨k,hk,he⟩ := Stack.pop_sound hc.right_zero hr
        have hp : c.left.Tape (mv.write::l.tail) (c.left.push i mv.write) := ⟨h.1.1,i,hl,h.1.2⟩
        have hs' := h.2 (r.headD false,k) he
        simpa only [BB6.Agent13BitPacked.Inv,move0,hd,ite_true,List.tail_cons,List.headD_cons] using
          (show ∃ a b, c.left.Tape (mv.write::l.tail) a ∧ c.right.Tape r.tail b ∧
            stateOK c mv.next (r.headD false) a b = true from ⟨_,k,hp,hk,hs'⟩)

theorem live {p c z} (hc : SplitCheck p c) (hz : Inv c z) (n : Nat) :
    ∃ t, run0 p n z = some t ∧ Inv c t := by
  induction n generalizing z with
  | zero => exact ⟨z,rfl,hz⟩
  | succ n ih =>
    obtain ⟨t,ht,hi⟩ := inv_step hc hz
    obtain ⟨u,hu,hj⟩ := ih hi
    exact ⟨u,by rw [run0,ht]; exact hu,hj⟩

theorem never (p : PartialMachine) (c : Cert) (hc : SplitCheck p c)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  obtain ⟨t,ht,_⟩ := live hc (inv_start hc) n
  have hz : (BB6Coverage.Agent50Zipper.zrun p n start).map project = some t :=
    (run_project p n start).trans ht
  cases h : BB6Coverage.Agent50Zipper.zrun p n start with
  | none => simp [h] at hz
  | some z =>
    have H := BB6Coverage.Agent50Zipper.zrun_sound p m hm n start z h
    rw [start_embed] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some _ => rfl

#print axioms state_checked
#print axioms never
end BB6.Agent44BitPackedSplit
