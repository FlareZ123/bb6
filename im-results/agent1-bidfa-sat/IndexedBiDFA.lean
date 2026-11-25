import TreeBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent1IndexedBiDFA
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent16BiDFA
open BB6Coverage.Agent16BiDFA.TreeCheck

/-- Lookup soundness needs no ordering or injectivity assumption.
    The wider radix allows compressed sparse-window states above 64. -/
def key (s : AState) : Nat := ((s.q.val*2+s.a.toNat)*65536+s.l)*65536+s.r

def contains (t : Tree) (s : AState) : Bool :=
  match t with
  | .empty => false
  | .node l a r =>
    if key s < key a then contains l s
    else if key a < key s then contains r s
    else decide (s = a)

theorem contains_sound {t : Tree} {s : AState} (h : contains t s = true) : s ∈ t.flatten := by
  induction t with
  | empty => simp [contains] at h
  | node l a r il ir =>
    simp only [contains] at h
    split at h
    · exact List.mem_append_left _ (il h)
    · split at h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (ir h))
      · have he := of_decide_eq_true h
        subst s
        exact List.mem_append_right _ (List.mem_cons_self)

/-- Incoming stack edges grouped by their destination summary. -/
abbrev ERows := Array (List (Bool × Nat))

structure Cert where
  dl : Array Nat
  dr : Array Nat
  el : ERows
  er : ERows
  states : Tree

def delta (d : Array Nat) (i : Nat) (b : Bool) : Nat := d.getD (2*i+b.toNat) 0
def summary (d : Array Nat) : List Bool → Nat
  | [] => 0
  | b::t => delta d (summary d t) b

def TapeOK (d : Array Nat) (e : ERows) : List Bool → Prop
  | [] => (false,0) ∈ e.getD 0 []
  | b::t => (b,summary d t) ∈ e.getD (delta d (summary d t) b) [] ∧ TapeOK d e t

theorem tape_top {d e t} (h : TapeOK d e t) :
    (t.headD false,summary d t.tail) ∈ e.getD (summary d t) [] := by
  cases t with
  | nil => exact h
  | cons b t => exact h.1

theorem tape_tail {d e t} (h : TapeOK d e t) : TapeOK d e t.tail := by
  cases t with
  | nil => exact h
  | cons b t => exact h.2

theorem tape_push {d e t} (b : Bool) (h : TapeOK d e t)
    (he : (b,summary d t) ∈ e.getD (delta d (summary d t) b) []) :
    TapeOK d e (b::t) := ⟨he,h⟩

def stepOK (p : PartialMachine) (c : Cert) (s : AState) : Bool :=
  match p (s.q,s.a) with
  | some (some mv) =>
    if mv.right then
      decide ((mv.write,s.l) ∈ c.el.getD (delta c.dl s.l mv.write) []) &&
      (c.er.getD s.r []).all (fun e => contains c.states ⟨mv.next,e.1,delta c.dl s.l mv.write,e.2⟩)
    else
      decide ((mv.write,s.r) ∈ c.er.getD (delta c.dr s.r mv.write) []) &&
      (c.el.getD s.l []).all (fun e => contains c.states ⟨mv.next,e.1,e.2,delta c.dr s.r mv.write⟩)
  | _ => false

def Inv (c : Cert) (z : Z0) : Prop :=
  TapeOK c.dl c.el z.l.tail ∧ TapeOK c.dr c.er z.r ∧
    contains c.states ⟨z.q,z.l.headD false,summary c.dl z.l.tail,summary c.dr z.r⟩ = true

theorem inv_start {c : Cert}
    (hl : (false,0) ∈ c.el.getD 0 [])
    (hr : (false,0) ∈ c.er.getD 0 [])
    (hs : contains c.states ⟨0,false,0,0⟩ = true) :
    Inv c ⟨0,[],[]⟩ := ⟨hl,hr,hs⟩

theorem inv_step {p c z} (hc : c.states.all (stepOK p c) = true) (hz : Inv c z) :
    ∃ t, step0 p z = some t ∧ Inv c t := by
  obtain ⟨q,l,r⟩ := z
  obtain ⟨hl,hr,hs⟩ := hz
  change TapeOK c.dl c.el l.tail at hl
  change TapeOK c.dr c.er r at hr
  change contains c.states ⟨q,l.headD false,summary c.dl l.tail,summary c.dr r⟩ = true at hs
  have h := Tree.all_sound hc _ (contains_sound hs)
  cases hm : p (q,l.headD false) with
  | none => simp only [stepOK,hm,Bool.false_eq_true] at h
  | some op =>
    cases op with
    | none => simp only [stepOK,hm,Bool.false_eq_true] at h
    | some mv =>
      refine ⟨move0 mv ⟨q,l,r⟩, by simp only [step0,hm,Option.bind_some,id_eq,Option.map_some],?_⟩
      cases hd : mv.right with
      | false =>
        simp only [stepOK,hm,hd,Bool.false_eq_true,ite_false,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
        have hp := tape_push mv.write hr h.1
        have ht := tape_tail hl
        have he := h.2 _ (tape_top hl)
        simpa only [Inv,move0,hd,Bool.false_eq_true,ite_false,summary] using And.intro ht (And.intro hp he)
      | true =>
        simp only [stepOK,hm,hd,ite_true,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
        have hp := tape_push mv.write hl h.1
        have ht := tape_tail hr
        have he := h.2 _ (tape_top hr)
        simpa only [Inv,move0,hd,ite_true,List.tail_cons,List.headD_cons,summary] using And.intro hp (And.intro ht he)

theorem live {p c z} (hc : c.states.all (stepOK p c) = true) (hz : Inv c z) (n : Nat) :
    ∃ t, run0 p n z = some t ∧ Inv c t := by
  induction n generalizing z with
  | zero => exact ⟨z,rfl,hz⟩
  | succ n ih =>
    obtain ⟨t,ht,hi⟩ := inv_step hc hz
    obtain ⟨u,hu,hj⟩ := ih hi
    exact ⟨u,by rw [run0,ht]; exact hu,hj⟩

theorem never (p : PartialMachine) (c : Cert)
    (hl : (false,0) ∈ c.el.getD 0 [])
    (hr : (false,0) ∈ c.er.getD 0 [])
    (hs : contains c.states ⟨0,false,0,0⟩ = true)
    (hc : c.states.all (stepOK p c) = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  obtain ⟨t,ht,_⟩ := live hc (inv_start hl hr hs) n
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
end BB6Coverage.Agent1IndexedBiDFA
