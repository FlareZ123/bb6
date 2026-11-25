import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent1RelationalBiNFA
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent16BiDFA
open BB6Coverage.Agent16BiDFA.TreeCheck
open BB6Coverage.Agent1IndexedBiDFA (ERows contains contains_sound)

/-- A finite stack path reads from the distant blank end toward the head.
    Its terminal abstract state is existential, not a deterministic summary. -/
def StackOK (e : ERows) : List Bool → Nat → Prop
  | [], s => s = 0 ∧ (false,0) ∈ e.getD 0 []
  | b::t, s => ∃ k, StackOK e t k ∧ (b,k) ∈ e.getD s []

theorem stack_top {e t s} (h : StackOK e t s) :
    ∃ k, StackOK e t.tail k ∧ (t.headD false,k) ∈ e.getD s [] := by
  cases t with
  | nil =>
    obtain ⟨rfl,hb⟩ := h
    exact ⟨0,⟨rfl,hb⟩,hb⟩
  | cons b t => exact h

theorem stack_push {e t s d} {b : Bool} (h : StackOK e t s)
    (he : (b,s) ∈ e.getD d []) : StackOK e (b::t) d := ⟨s,h,he⟩

/-- Incoming edges describe possible pop transitions. The indexed outgoing
    rows only propose push successors; the checker verifies every used edge
    against the incoming graph. No consistency assumption is necessary. -/
structure Cert where
  el : ERows
  er : ERows
  pl : Array (List Nat)
  pr : Array (List Nat)
  states : Tree

def pushRow (p : Array (List Nat)) (s : Nat) (b : Bool) : List Nat :=
  p.getD (2*s+b.toNat) []

def stepOK (p : PartialMachine) (c : Cert) (s : AState) : Bool :=
  match p (s.q,s.a) with
  | some (some mv) =>
    if mv.right then
      (c.er.getD s.r []).all (fun e => (pushRow c.pl s.l mv.write).any (fun d =>
        decide ((mv.write,s.l) ∈ c.el.getD d []) &&
        contains c.states ⟨mv.next,e.1,d,e.2⟩))
    else
      (c.el.getD s.l []).all (fun e => (pushRow c.pr s.r mv.write).any (fun d =>
        decide ((mv.write,s.r) ∈ c.er.getD d []) &&
        contains c.states ⟨mv.next,e.1,e.2,d⟩))
  | _ => false

def Inv (c : Cert) (z : Z0) : Prop :=
  ∃ l r, StackOK c.el z.l.tail l ∧ StackOK c.er z.r r ∧
    contains c.states ⟨z.q,z.l.headD false,l,r⟩ = true

theorem inv_start {c : Cert}
    (hl : (false,0) ∈ c.el.getD 0 [])
    (hr : (false,0) ∈ c.er.getD 0 [])
    (hs : contains c.states ⟨0,false,0,0⟩ = true) :
    Inv c ⟨0,[],[]⟩ := ⟨0,0,⟨rfl,hl⟩,⟨rfl,hr⟩,hs⟩

theorem inv_step {p c z} (hc : c.states.all (stepOK p c) = true) (hz : Inv c z) :
    ∃ t, step0 p z = some t ∧ Inv c t := by
  obtain ⟨q,l,r⟩ := z
  obtain ⟨li,ri,hl,hr,hs⟩ := hz
  change StackOK c.el l.tail li at hl
  change StackOK c.er r ri at hr
  change contains c.states ⟨q,l.headD false,li,ri⟩ = true at hs
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
        simp only [stepOK,hm,hd,Bool.false_eq_true,ite_false,List.all_eq_true,List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
        obtain ⟨k,hk,he⟩ := stack_top hl
        obtain ⟨d,_,hp,hn⟩ := h _ he
        have hs' := stack_push hr hp
        simpa only [Inv,move0,hd,Bool.false_eq_true,ite_false] using
          (show ∃ x y, StackOK c.el l.tail.tail x ∧ StackOK c.er (mv.write::r) y ∧
              contains c.states ⟨mv.next,l.tail.headD false,x,y⟩ = true from ⟨k,d,hk,hs',hn⟩)
      | true =>
        simp only [stepOK,hm,hd,ite_true,List.all_eq_true,List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
        obtain ⟨k,hk,he⟩ := stack_top hr
        obtain ⟨d,_,hp,hn⟩ := h _ he
        have hs' := stack_push hl hp
        simpa only [Inv,move0,hd,ite_true,List.tail_cons,List.headD_cons] using
          (show ∃ x y, StackOK c.el (mv.write::l.tail) x ∧ StackOK c.er r.tail y ∧
              contains c.states ⟨mv.next,r.headD false,x,y⟩ = true from ⟨d,k,hs',hk,hn⟩)

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
end BB6Coverage.Agent1RelationalBiNFA
