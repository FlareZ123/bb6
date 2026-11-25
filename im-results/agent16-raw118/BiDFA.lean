import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent16BiDFA
open BB6Coverage BB6Coverage.Agent31Pump

/-- Two stack summaries and discovered stack-edge constraints. A summary reads
    from the distant end of each finite stack towards its head. -/
structure Edge where
  dst : Nat
  sym : Bool
  src : Nat
  deriving DecidableEq, Repr
structure AState where
  q : Fin 6
  a : Bool
  l : Nat
  r : Nat
  deriving DecidableEq, Repr
structure Cert where
  dl : List Nat
  dr : List Nat
  el : List Edge
  er : List Edge
  states : List AState

def delta (d : List Nat) (i : Nat) (b : Bool) : Nat := d.getD (2*i+b.toNat) 0
def summary (d : List Nat) : List Bool → Nat
  | [] => 0
  | b::t => delta d (summary d t) b

def TapeOK (d : List Nat) (e : List Edge) : List Bool → Prop
  | [] => (⟨0,false,0⟩ : Edge) ∈ e
  | b::t => (⟨delta d (summary d t) b,b,summary d t⟩ : Edge) ∈ e ∧ TapeOK d e t

theorem tape_top {d e t} (h : TapeOK d e t) :
    (⟨summary d t,t.headD false,summary d t.tail⟩ : Edge) ∈ e := by
  cases t with
  | nil => exact h
  | cons b t => exact h.1

theorem tape_tail {d e t} (h : TapeOK d e t) : TapeOK d e t.tail := by
  cases t with
  | nil => exact h
  | cons b t => exact h.2

theorem tape_push {d e t} (b : Bool) (h : TapeOK d e t)
    (he : (⟨delta d (summary d t) b,b,summary d t⟩ : Edge) ∈ e) :
    TapeOK d e (b::t) := ⟨he,h⟩

def stateStepOK (p : PartialMachine) (c : Cert) (s : AState) : Bool :=
  match p (s.q,s.a) with
  | some (some mv) =>
    if mv.right then
      decide ((⟨delta c.dl s.l mv.write,mv.write,s.l⟩ : Edge) ∈ c.el) &&
      c.er.all (fun e => if e.dst = s.r then decide ((⟨mv.next,e.sym,delta c.dl s.l mv.write,e.src⟩ : AState) ∈ c.states) else true)
    else
      decide ((⟨delta c.dr s.r mv.write,mv.write,s.r⟩ : Edge) ∈ c.er) &&
      c.el.all (fun e => if e.dst = s.l then decide ((⟨mv.next,e.sym,e.src,delta c.dr s.r mv.write⟩ : AState) ∈ c.states) else true)
  | _ => false

def check (p : PartialMachine) (c : Cert) : Bool :=
  decide ((⟨0,false,0⟩ : Edge) ∈ c.el) && decide ((⟨0,false,0⟩ : Edge) ∈ c.er) &&
  decide ((⟨0,false,0,0⟩ : AState) ∈ c.states) && c.states.all (stateStepOK p c)

def Inv (c : Cert) (z : Z0) : Prop :=
  TapeOK c.dl c.el z.l.tail ∧ TapeOK c.dr c.er z.r ∧
    (⟨z.q,z.l.headD false,summary c.dl z.l.tail,summary c.dr z.r⟩ : AState) ∈ c.states

theorem inv_start {p c} (h : check p c = true) : Inv c ⟨0,[],[]⟩ := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
  exact ⟨h.1.1.1,h.1.1.2,h.1.2⟩

theorem inv_step {p c z} (hc : check p c = true) (hz : Inv c z) :
    ∃ t, step0 p z = some t ∧ Inv c t := by
  obtain ⟨q,l,r⟩ := z
  obtain ⟨hl,hr,hs⟩ := hz
  change TapeOK c.dl c.el l.tail at hl
  change TapeOK c.dr c.er r at hr
  change (⟨q,l.headD false,summary c.dl l.tail,summary c.dr r⟩ : AState) ∈ c.states at hs
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hc
  have h := hc.2 _ hs
  cases hm : p (q,l.headD false) with
  | none => simp only [stateStepOK,hm,Bool.false_eq_true] at h
  | some op =>
    cases op with
    | none => simp only [stateStepOK,hm,Bool.false_eq_true] at h
    | some mv =>
      refine ⟨move0 mv ⟨q,l,r⟩, by simp only [step0,hm,Option.bind_some,id_eq,Option.map_some],?_⟩
      cases hd : mv.right with
      | false =>
        simp only [stateStepOK,hm,hd,Bool.false_eq_true,ite_false,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
        have hp := tape_push mv.write hr h.1
        have ht := tape_tail hl
        have he := h.2 _ (tape_top hl)
        simp only [ite_true,decide_eq_true_eq] at he
        simpa only [Inv,move0,hd,Bool.false_eq_true,ite_false,summary] using And.intro ht (And.intro hp he)
      | true =>
        simp only [stateStepOK,hm,hd,ite_true,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
        have hp := tape_push mv.write hl h.1
        have ht := tape_tail hr
        have he := h.2 _ (tape_top hr)
        simp only [ite_true,decide_eq_true_eq] at he
        simpa only [Inv,move0,hd,ite_true,List.tail_cons,List.headD_cons,summary] using And.intro hp (And.intro ht he)

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
end BB6Coverage.Agent16BiDFA
