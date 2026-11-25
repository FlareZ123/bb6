import NGramCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47SparseNGram
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram

/-- Sparse variant of Agent1's kernel checker: edge membership uses the same
    certified finite low-bit trie as state membership, avoiding a 2^k bitset. -/
structure Cert where
  n : Nat
  left : Trie
  right : Trie
  states : Array Trie

def edgeOK (E : Trie) (x : Nat) (b : Bool) : Bool :=
  E.has (2*x+b.toNat)

def row (c : Cert) (q : Fin 6) (a : Bool) : Trie :=
  c.states.getD (2*q.val+a.toNat) .empty

def stateOK (c : Cert) (q : Fin 6) (a : Bool) (l r : Nat) : Bool :=
  (row c q a).has (r+2^(c.n+1)*l)

def bits : List Bool := [false,true]

theorem mem_bits (b : Bool) : b ∈ bits := by cases b <;> decide

theorem mem_states (q : Fin 6) : q ∈ List.finRange 6 := by simp

def stateStepOK (p : PartialMachine) (c : Cert) (q : Fin 6) (a : Bool) (l r : Nat) : Bool :=
  match p (q,a) with
  | some (some mv) =>
    if mv.right then
      edgeOK c.left (push c.n mv.write l) (far c.n l) &&
        bits.all (fun e => !edgeOK c.right r e ||
          stateOK c mv.next (head r) (push c.n mv.write l) (pop c.n r e))
    else
      edgeOK c.right (push c.n mv.write r) (far c.n r) &&
        bits.all (fun e => !edgeOK c.left l e ||
          stateOK c mv.next (head l) (pop c.n l e) (push c.n mv.write r))
  | _ => false

def check (p : PartialMachine) (c : Cert) : Bool :=
  edgeOK c.left 0 false && edgeOK c.right 0 false && stateOK c 0 false 0 0 &&
    (List.finRange 6).all (fun q => bits.all (fun a =>
      (row c q a).all (fun i => stateStepOK p c q a (i/2^(c.n+1)) (i%2^(c.n+1)))))

/-- Independently checked state rows assemble without re-running the checker. -/
theorem check_of_rows {p : PartialMachine} {c : Cert}
    (hL : edgeOK c.left 0 false = true)
    (hR : edgeOK c.right 0 false = true)
    (hS : stateOK c 0 false 0 0 = true)
    (hrows : ∀ q a, (row c q a).all (fun i =>
      stateStepOK p c q a (i/2^(c.n+1)) (i%2^(c.n+1))) = true) :
    check p c = true := by
  simp only [check,Bool.and_eq_true,List.all_eq_true]
  exact ⟨⟨⟨hL,hR⟩,hS⟩,fun q _ a _ => hrows q a⟩

def TapeOK (n : Nat) (E : Trie) : List Bool → Prop
  | [] => edgeOK E 0 false = true
  | b::t => edgeOK E (pref (n+1) (b::t)) (atBit (n+1) (b::t)) = true ∧ TapeOK n E t

theorem tape_top {n E t} (h : TapeOK n E t) :
    edgeOK E (pref (n+1) t) (atBit (n+1) t) = true := by
  cases t with
  | nil =>
    change edgeOK E 0 false = true at h
    simpa only [pref_nil,atBit_nil] using h
  | cons b t => exact h.1

theorem tape_tail {n E t} (h : TapeOK n E t) : TapeOK n E t.tail := by
  cases t with
  | nil => exact h
  | cons b t => exact h.2

theorem tape_push {n E t} (b : Bool) (h : TapeOK n E t)
    (he : edgeOK E (push n b (pref (n+1) t)) (far n (pref (n+1) t)) = true) :
    TapeOK n E (b::t) := by
  rw [pref_push,pref_far] at he
  exact ⟨he,h⟩

def Inv (c : Cert) (z : Z0) : Prop :=
  TapeOK c.n c.left z.l.tail ∧ TapeOK c.n c.right z.r ∧
    stateOK c z.q (z.l.headD false) (pref (c.n+1) z.l.tail) (pref (c.n+1) z.r) = true

theorem inv_start {p c} (h : check p c = true) : Inv c ⟨0,[],[]⟩ := by
  simp only [check,Bool.and_eq_true] at h
  refine ⟨h.1.1.1,h.1.1.2,?_⟩
  change stateOK c 0 false (pref (c.n+1) []) (pref (c.n+1) []) = true
  simpa only [pref_nil] using h.1.2

theorem state_checked {p c q a l r} (h : check p c = true)
    (hr : r < 2^(c.n+1)) (hs : stateOK c q a l r = true) :
    stateStepOK p c q a l r = true := by
  simp only [check,Bool.and_eq_true,List.all_eq_true] at h
  have ha := h.2 q (mem_states q) a (mem_bits a)
  have H := Trie.all_sound ha hs
  change stateStepOK p c q a ((r+2^(c.n+1)*l)/2^(c.n+1)) ((r+2^(c.n+1)*l)%2^(c.n+1)) = true at H
  rw [Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)),Nat.div_eq_of_lt hr,Nat.zero_add,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr] at H
  exact H

theorem inv_step {p c z} (hc : check p c = true) (hz : Inv c z) :
    ∃ t, step0 p z = some t ∧ Inv c t := by
  obtain ⟨q,l,r⟩ := z
  obtain ⟨hl,hr,hs⟩ := hz
  change TapeOK c.n c.left l.tail at hl
  change TapeOK c.n c.right r at hr
  change stateOK c q (l.headD false) (pref (c.n+1) l.tail) (pref (c.n+1) r) = true at hs
  have h := state_checked hc (pref_lt (c.n+1) r) hs
  cases hm : p (q,l.headD false) with
  | none => simp only [stateStepOK,hm,Bool.false_eq_true] at h
  | some op =>
    cases op with
    | none => simp only [stateStepOK,hm,Bool.false_eq_true] at h
    | some mv =>
      refine ⟨move0 mv ⟨q,l,r⟩, by simp only [step0,hm,Option.bind_some,id_eq,Option.map_some], ?_⟩
      cases hd : mv.right with
      | false =>
        simp only [stateStepOK,hm,hd,Bool.false_eq_true,ite_false,Bool.and_eq_true,List.all_eq_true] at h
        have hp := tape_push mv.write hr h.1
        have ht := tape_tail hl
        have he := h.2 (atBit (c.n+1) l.tail) (mem_bits _)
        rw [tape_top hl] at he
        simp only [Bool.not_true,Bool.false_or,pref_head,pref_pop,pref_push] at he
        simpa only [Inv,move0,hd,Bool.false_eq_true,ite_false] using And.intro ht (And.intro hp he)
      | true =>
        simp only [stateStepOK,hm,hd,ite_true,Bool.and_eq_true,List.all_eq_true] at h
        have hp := tape_push mv.write hl h.1
        have ht := tape_tail hr
        have he := h.2 (atBit (c.n+1) r) (mem_bits _)
        rw [tape_top hr] at he
        simp only [Bool.not_true,Bool.false_or,pref_head,pref_pop,pref_push] at he
        simpa only [Inv,move0,hd,ite_true,List.tail_cons,List.headD_cons] using And.intro hp (And.intro ht he)

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

#print axioms inv_step
#print axioms live
#print axioms never
end BB6.Agent47SparseNGram
