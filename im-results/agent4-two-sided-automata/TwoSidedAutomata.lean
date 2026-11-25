import NGramCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent4Automata
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent1NGram (Trie mem_bits mem_states bits)

/-- A finite stack relation, represented by inverse push edges. -/
structure Stack where
  edges : Array (List (Bool × Nat))
  pushes : Array (Nat × Nat)

def Stack.pop (s : Stack) (i : Nat) : List (Bool × Nat) := s.edges.getD i []
def Stack.push (s : Stack) (i : Nat) (b : Bool) : Nat :=
  if b then (s.pushes.getD i (0,0)).2 else (s.pushes.getD i (0,0)).1

def Stack.Tape (s : Stack) : List Bool → Nat → Prop
  | [],i => i < s.edges.size ∧ i = 0
  | b::t,j => j < s.edges.size ∧ ∃ i, s.Tape t i ∧ (b,i) ∈ s.pop j

theorem Stack.bound {s : Stack} {t : List Bool} {i : Nat} (h : s.Tape t i) : i < s.edges.size := by
  cases t <;> exact h.1

theorem Stack.pop_sound {s : Stack} {t : List Bool} {j : Nat}
    (hb : (false,0) ∈ s.pop 0) (h : s.Tape t j) :
    ∃ i, s.Tape t.tail i ∧ (t.headD false,i) ∈ s.pop j := by
  cases t with
  | nil =>
    obtain ⟨h, rfl⟩ := h
    exact ⟨0,⟨h,rfl⟩,hb⟩
  | cons b t => exact h.2

structure Cert where
  left : Stack
  right : Stack
  states : Array Trie

def row (c : Cert) (q : Fin 6) (a : Bool) : Trie := c.states.getD (2*q.val+a.toNat) .empty

def stateOK (c : Cert) (q : Fin 6) (a : Bool) (l r : Nat) : Bool :=
  (row c q a).has (r+c.right.edges.size*l)

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

def check (p : PartialMachine) (c : Cert) : Bool :=
  decide (0 < c.left.edges.size) && decide (0 < c.right.edges.size) &&
  (c.left.pop 0).contains (false,0) && (c.right.pop 0).contains (false,0) &&
  stateOK c 0 false 0 0 && (List.finRange 6).all (fun q => bits.all (fun a =>
    (row c q a).all (fun i => stateStepOK p c q a (i/c.right.edges.size) (i%c.right.edges.size))))

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
  have H := Trie.all_sound ha hs
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
end BB6.Agent4Automata
