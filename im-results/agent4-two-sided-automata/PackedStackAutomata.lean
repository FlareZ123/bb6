import TwoSidedAutomata
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent4PackedAutomata
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent4Automata (Stack)
open BB6.Agent1NGram (bits mem_bits mem_states)

/-- Sparse enumeration, independent of the efficient lookup bitmap. -/
def bitmap : List Nat → Nat
  | [] => 0
  | i::xs => (1 <<< i) ||| bitmap xs

theorem bit_one (i j : Nat) : ((1 : Nat) <<< i).testBit j = true ↔ j = i := by
  simp only [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_one_eq_true_iff_self_eq_zero]
  omega

theorem bitmap_mem (xs : List Nat) (i : Nat) : (bitmap xs).testBit i = true ↔ i ∈ xs := by
  induction xs with
  | nil => simp [bitmap]
  | cons x xs ih => simp only [bitmap,Nat.testBit_or,Bool.or_eq_true,bit_one,ih,List.mem_cons]

structure Row where
  chunks : List (List Nat)
  mask : Nat

def Row.valid (r : Row) : Bool := r.mask == bitmap r.chunks.flatten

theorem Row.mem {r : Row} (h : r.valid = true) {i : Nat} (hi : r.mask.testBit i = true) : i ∈ r.chunks.flatten := by
  simp only [Row.valid,beq_iff_eq] at h
  rw [h] at hi
  exact (bitmap_mem _ _).mp hi

structure Cert where
  left : Stack
  right : Stack
  rows : Array Row

def row (c : Cert) (q : Fin 6) (a : Bool) : Row := c.rows.getD (2*q.val+a.toNat) ⟨[],0⟩

def stateOK (c : Cert) (q : Fin 6) (a : Bool) (l r : Nat) : Bool :=
  (row c q a).mask.testBit (r+c.right.edges.size*l)

def stateStepOK (p : PartialMachine) (c : Cert) (q : Fin 6) (a : Bool) (l r : Nat) : Bool :=
  match p (q,a) with
  | some (some mv) =>
    if mv.right then
      let j := c.left.push l mv.write
      decide (j < c.left.edges.size) && (c.left.pop j).contains (mv.write,l) &&
        (c.right.pop r).all (fun e => stateOK c mv.next e.1 j e.2)
    else
      let j := c.right.push r mv.write
      decide (j < c.right.edges.size) && (c.right.pop j).contains (mv.write,r) &&
        (c.left.pop l).all (fun e => stateOK c mv.next e.1 e.2 j)
  | _ => false

def indicesCheck (p : PartialMachine) (c : Cert) (q : Fin 6) (a : Bool) (xs : List Nat) : Bool :=
  xs.all (fun i => stateStepOK p c q a (i/c.right.edges.size) (i%c.right.edges.size))

def rowCheck (p : PartialMachine) (c : Cert) (q : Fin 6) (a : Bool) : Bool :=
  (row c q a).valid && (row c q a).chunks.all (indicesCheck p c q a)

def check (p : PartialMachine) (c : Cert) : Bool :=
  decide (0 < c.left.edges.size) && decide (0 < c.right.edges.size) &&
  (c.left.pop 0).contains (false,0) && (c.right.pop 0).contains (false,0) &&
  stateOK c 0 false 0 0 && (List.finRange 6).all (fun q => bits.all (fun a => rowCheck p c q a))

def Inv (c : Cert) (z : Z0) : Prop :=
  ∃ l r, c.left.Tape z.l.tail l ∧ c.right.Tape z.r r ∧ stateOK c z.q (z.l.headD false) l r = true

theorem inv_start {p c} (h : check p c = true) : Inv c ⟨0,[],[]⟩ := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
  exact ⟨0,0,⟨h.1.1.1.1.1,rfl⟩,⟨h.1.1.1.1.2,rfl⟩,h.1.2⟩

theorem state_checked {p c q a l r} (h : check p c = true)
    (hr : r < c.right.edges.size) (hs : stateOK c q a l r = true) :
    stateStepOK p c q a l r = true := by
  simp only [check,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at h
  have ha := h.2 q (mem_states q) a (mem_bits a)
  simp only [rowCheck,indicesCheck,Bool.and_eq_true,List.all_eq_true] at ha
  have hi := Row.mem ha.1 hs
  obtain ⟨chunk, hchunk, hmem⟩ := List.mem_flatten.mp hi
  have H := ha.2 chunk hchunk _ hmem
  change stateStepOK p c q a ((r+c.right.edges.size*l)/c.right.edges.size) ((r+c.right.edges.size*l)%c.right.edges.size) = true at H
  rw [Nat.add_mul_div_left _ _ (by omega : 0 < c.right.edges.size),Nat.div_eq_of_lt hr,Nat.zero_add,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr] at H
  exact H
theorem inv_step {p c z} (hc : check p c = true) (hz : Inv c z) :
    ∃ t, step0 p z = some t ∧ Inv c t := by
  obtain ⟨q,l,r⟩ := z
  obtain ⟨i,j,hl,hr,hs⟩ := hz
  change c.left.Tape l.tail i at hl
  change c.right.Tape r j at hr
  change stateOK c q (l.headD false) i j = true at hs
  have h := state_checked hc (Stack.bound hr) hs
  have hb := hc
  simp only [check,Bool.and_eq_true,List.contains_iff_mem] at hb
  cases hm : p (q,l.headD false) with
  | none => simp only [stateStepOK,hm,Bool.false_eq_true] at h
  | some op =>
    cases op with
    | none => simp only [stateStepOK,hm,Bool.false_eq_true] at h
    | some mv =>
      refine ⟨move0 mv ⟨q,l,r⟩, by simp only [step0,hm,Option.bind_some,id_eq,Option.map_some], ?_⟩
      cases hd : mv.right with
      | false =>
        simp only [stateStepOK,hm,hd,Bool.false_eq_true,ite_false,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,List.contains_iff_mem] at h
        obtain ⟨k,hk,he⟩ := Stack.pop_sound hb.1.1.1.2 hl
        have hp : c.right.Tape (mv.write::r) (c.right.push j mv.write) := ⟨h.1.1,j,hr,h.1.2⟩
        have hs' := h.2 (l.tail.headD false,k) he
        simpa only [Inv,move0,hd,Bool.false_eq_true,ite_false] using (show ∃ a b, c.left.Tape l.tail.tail a ∧ c.right.Tape (mv.write::r) b ∧ stateOK c mv.next (l.tail.headD false) a b = true from ⟨k,_,hk,hp,hs'⟩)
      | true =>
        simp only [stateStepOK,hm,hd,ite_true,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,List.contains_iff_mem] at h
        obtain ⟨k,hk,he⟩ := Stack.pop_sound hb.1.1.2 hr
        have hp : c.left.Tape (mv.write::l.tail) (c.left.push i mv.write) := ⟨h.1.1,i,hl,h.1.2⟩
        have hs' := h.2 (r.headD false,k) he
        simpa only [Inv,move0,hd,ite_true,List.tail_cons,List.headD_cons] using (show ∃ a b, c.left.Tape (mv.write::l.tail) a ∧ c.right.Tape r.tail b ∧ stateOK c mv.next (r.headD false) a b = true from ⟨_,k,hp,hk,hs'⟩)

theorem live {p c z} (hc : check p c = true) (hz : Inv c z) (n : Nat) :
    ∃ t, run0 p n z = some t ∧ Inv c t := by
  induction n generalizing z with
  | zero => exact ⟨z,rfl,hz⟩
  | succ n ih =>
    obtain ⟨t,ht,hi⟩ := inv_step hc hz
    obtain ⟨u,hu,hj⟩ := ih hi
    exact ⟨u,by rw [run0,ht]; exact hu,hj⟩

theorem never (p : PartialMachine) (c : Cert) (hc : check p c = true)
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

#print axioms live
#print axioms never
end BB6.Agent4PackedAutomata
