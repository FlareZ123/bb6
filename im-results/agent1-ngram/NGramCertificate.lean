import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1NGram
open BB6Coverage BB6Coverage.Agent31Pump

/-- Little-endian prefix of the zero-padded stack. -/
def pref : Nat → List Bool → Nat
  | 0,_ => 0
  | n+1,t => (t.headD false).toNat + 2 * pref n t.tail

def atBit : Nat → List Bool → Bool
  | 0,t => t.headD false
  | n+1,t => atBit n t.tail

theorem pref_nil (n : Nat) : pref n [] = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pref,ih]

theorem atBit_nil (n : Nat) : atBit n [] = false := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem pref_lt (n : Nat) (t : List Bool) : pref n t < 2^n := by
  induction n generalizing t with
  | zero => change 0 < 1; decide
  | succ n ih =>
    have h := ih t.tail
    have hb := Bool.toNat_lt (t.headD false)
    rw [pref,Nat.pow_succ]
    omega

theorem pref_extend (n : Nat) (t : List Bool) :
    pref (n+1) t = pref n t + 2^n * (atBit n t).toNat := by
  induction n generalizing t with
  | zero => simp [pref,atBit]
  | succ n ih =>
    change (t.headD false).toNat + 2 * pref (n+1) t.tail = (t.headD false).toNat + 2*pref n t.tail + 2^(n+1)*(atBit n t.tail).toNat
    rw [ih t.tail,Nat.pow_succ]
    cases atBit n t.tail <;> simp <;> omega

theorem pref_mod (n : Nat) (t : List Bool) :
    pref (n+1) t % 2^n = pref n t := by
  rw [pref_extend,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (pref_lt n t)]

def far (n x : Nat) : Bool := x / 2^n == 1

def head (x : Nat) : Bool := x % 2 == 1

def push (n : Nat) (w : Bool) (x : Nat) : Nat := w.toNat + 2 * (x % 2^n)

def pop (n x : Nat) (e : Bool) : Nat := x / 2 + 2^n * e.toNat

theorem pref_far (n : Nat) (t : List Bool) : far n (pref (n+1) t) = atBit n t := by
  unfold far
  rw [pref_extend,Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)),Nat.div_eq_of_lt (pref_lt n t)]
  cases atBit n t <;> rfl

theorem pref_head (n : Nat) (t : List Bool) : head (pref (n+1) t) = t.headD false := by
  unfold head
  rw [pref,Nat.add_mul_mod_self_left]
  cases t.headD false <;> rfl

theorem pref_push (n : Nat) (w : Bool) (t : List Bool) :
    push n w (pref (n+1) t) = pref (n+1) (w::t) := by
  rw [push,pref_mod]
  rfl

theorem pref_pop (n : Nat) (t : List Bool) :
    pop n (pref (n+1) t) (atBit (n+1) t) = pref (n+1) t.tail := by
  unfold pop
  change ((t.headD false).toNat + 2*pref n t.tail)/2 + 2^n*(atBit n t.tail).toNat = pref (n+1) t.tail
  rw [Nat.add_mul_div_left _ _ (by decide : 0<2),Nat.div_eq_of_lt (Bool.toNat_lt (t.headD false))]
  simp only [Nat.zero_add]
  exact (pref_extend n t.tail).symm

/-- A finite set of nonnegative integers, represented by a low-bit trie. -/
inductive Trie where
  | empty
  | leaf
  | branch (even odd : Trie)

def Trie.has : Trie → Nat → Bool
  | .empty, _ => false
  | .leaf, i => i == 0
  | .branch e o, i => if i % 2 == 0 then e.has (i/2) else o.has (i/2)

def Trie.all : Trie → (Nat → Bool) → Bool
  | .empty, _ => true
  | .leaf, f => f 0
  | .branch e o, f => e.all (fun i => f (2*i)) && o.all (fun i => f (2*i+1))

theorem Trie.all_sound {t : Trie} {f : Nat → Bool} {i : Nat}
    (ha : t.all f = true) (hi : t.has i = true) : f i = true := by
  induction t generalizing f i with
  | empty => simp [Trie.has] at hi
  | leaf =>
    simp only [Trie.has,beq_iff_eq] at hi
    subst i
    exact ha
  | branch e o he ho =>
    simp only [Trie.all,Bool.and_eq_true] at ha
    by_cases h : i % 2 = 0
    · have hh : e.has (i/2) = true := by simpa only [Trie.has,h,beq_self_eq_true,ite_true] using hi
      have H := he ha.1 hh
      have eq : 2*(i/2)=i := by omega
      simpa only [eq] using H
    · have hh : o.has (i/2) = true := by simpa only [Trie.has,beq_iff_eq,h,ite_false] using hi
      have H := ho ha.2 hh
      have eq : 2*(i/2)+1=i := by omega
      simpa only [eq] using H

/-- Window width is n+1. The two edge bitsets record allowed (window,
    extension-bit) pairs. Each state trie records pairs of left/right windows. -/
structure Cert where
  n : Nat
  left : Nat
  right : Nat
  states : Array Trie

def edgeOK (E : Nat) (x : Nat) (b : Bool) : Bool :=
  E.testBit (2*x+b.toNat)

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

def TapeOK (n : Nat) (E : Nat) : List Bool → Prop
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
end BB6.Agent1NGram
