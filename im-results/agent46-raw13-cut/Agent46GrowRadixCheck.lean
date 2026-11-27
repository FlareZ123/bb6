import Agent46OpenSweep2
import Agent46RadixCheck
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto2.GrowRadix
open BB6Coverage Agent31Pump Agent50Zipper Auto2
open BB6Coverage.Agent31Pump.Auto (rep_add)
open BB6Coverage.Agent31Pump.Auto.Radix (splitCarry)
structure Shape where
  digit : Fin 4 → List Bool
  terminal : Bool → List Bool

def P : List Bool := [false,true,false]
def pre : List Bool := [true,false]
def base (s : Shape) : Auto.Radix.Shape 3 := ⟨0,[],s.digit, s.terminal,[0]⟩
def enc (s : Shape) := Auto.Radix.enc (base s)
def frame (s : Shape) (n : Nat) (ds : List (Fin 4)) (b : Bool) : Z0 := ⟨0,[],P ++ rep P n ++ pre ++ enc s ds ++ s.terminal b⟩
def param (s : Shape) (out long : Bool) (tail : List Bool) : PZ :=
  let d := s.digit (if out then 0 else 3)
  ⟨0,.lit [],.periodic (if out then P++P else P) P false (if long then .periodic (pre++d) d true (.lit tail) else .lit (pre++tail))⟩
structure Macro where
  ops : List Action
  a : Nat
  b : Nat
  c : Nat

def macroCert (f g : PZ) (m : Macro) : Auto2.Cert := ⟨f,g,m.ops,m.a,m.b,m.c⟩
def checkOpen (p : PartialMachine) (f g : PZ) (m : Macro) : Bool :=
  match OpenRight.traceRun p m.ops f with
  | none => false
  | some out => decide (0 < m.c ∧ out.a=m.a ∧ out.b=m.b ∧ out.c=m.c ∧ out.z.norm=g.norm)
def checkClosed (p : PartialMachine) (f g : PZ) (m : Macro) : Prop := 0 < m.c ∧ check p (macroCert f g m) = true

theorem open_sound (p : PartialMachine) (f g : PZ) (m : Macro) (h : checkOpen p f g m = true) (n k : Nat) (tail : List Bool) :
    0 < m.a*n+m.b*k+m.c ∧ run0 p (m.a*n+m.b*k+m.c) ((OpenRight.attachZ f tail).eval n k) = some ((OpenRight.attachZ g tail).eval n k) := by
  unfold checkOpen at h
  cases hr : OpenRight.traceRun p m.ops f with
  | none => simp [hr] at h
  | some out =>
    simp only [hr,decide_eq_true_eq] at h
    have hs := OpenRight.traceRun_sound p m.ops hr n k tail
    have hn := congrArg (fun z => (OpenRight.attachZ z tail).eval n k) h.2.2.2.2
    rw [OpenRight.norm_attachZ_eval,OpenRight.norm_attachZ_eval] at hn
    rw [h.2.1,h.2.2.1,h.2.2.2.1,hn] at hs
    exact ⟨by omega,hs⟩

theorem closed_sound (p : PartialMachine) (f g : PZ) (m : Macro) (h : checkClosed p f g m) (n k : Nat) :
    0 < m.a*n+m.b*k+m.c ∧ run0 p (m.a*n+m.b*k+m.c) (f.eval n k) = some (g.eval n k) := by
  exact ⟨by have := h.1; omega,Auto2.sound p _ h.2 n k⟩
structure Cert where
  shape : Shape
  entry : Nat
  normalZ : Fin 3 → Macro
  normalS : Fin 3 → Macro
  terminalZ : Bool → Macro
  terminalS : Bool → Macro

def endWord (s : Shape) (b : Bool) : List Bool := if b then s.digit 0 ++ s.terminal false else s.terminal true
structure Checked (p : PartialMachine) (c : Cert) : Prop where
  seed : run0 p c.entry ⟨0,[],[]⟩ = some (frame c.shape 0 [] false)
  normalZ : ∀ i : Fin 3, checkOpen p (param c.shape false false (c.shape.digit i.castSucc)) (param c.shape true false (c.shape.digit i.succ)) (c.normalZ i) = true
  normalS : ∀ i : Fin 3, checkOpen p (param c.shape false true (c.shape.digit i.castSucc)) (param c.shape true true (c.shape.digit i.succ)) (c.normalS i) = true
  terminalZ : ∀ b : Bool, checkClosed p (param c.shape false false (c.shape.terminal b)) (param c.shape true false (endWord c.shape b)) (c.terminalZ b)
  terminalS : ∀ b : Bool, checkClosed p (param c.shape false true (c.shape.terminal b)) (param c.shape true true (endWord c.shape b)) (c.terminalS b)

theorem live (p : PartialMachine) (c : Cert) (h : Checked p c) (n : Nat) (ds : List (Fin 4)) (b : Bool) :
    ∃ t ds' b', 0<t ∧ run0 p t (frame c.shape n ds b) = some (frame c.shape (n+1) ds' b') := by
  obtain ⟨k,hk⟩ := splitCarry (r:=3) ds
  rcases hk with hk | ⟨i,rest,hk⟩
  · subst ds
    cases k with
    | zero =>
      obtain ⟨ht,hr⟩ := closed_sound p _ _ _ (h.terminalZ b) n 0
      cases b
      · exact ⟨_,[],true,ht,by simpa [param,base,endWord,frame,PZ.eval,Word.eval,enc,Auto.Radix.enc,rep,List.append_assoc] using hr⟩
      · exact ⟨_,[0],false,ht,by simpa [param,base,endWord,frame,PZ.eval,Word.eval,enc,Auto.Radix.enc,rep,List.append_assoc] using hr⟩
    | succ k =>
      obtain ⟨ht,hr⟩ := closed_sound p _ _ _ (h.terminalS b) n k
      cases b
      · exact ⟨_,List.replicate (k+1) 0,true,ht,by simpa [param,base,endWord,frame,PZ.eval,Word.eval,enc,Auto.Radix.enc_append,Auto.Radix.enc_rep,rep,Auto.Radix.enc,List.append_assoc] using hr⟩
      · exact ⟨_,List.replicate (k+1) 0 ++ [0],false,ht,by simpa [param,base,endWord,frame,PZ.eval,Word.eval,enc,Auto.Radix.enc_append,Auto.Radix.enc_rep,rep,Auto.Radix.enc,List.append_assoc] using hr⟩
  · subst ds
    cases k with
    | zero =>
      obtain ⟨ht,hr⟩ := open_sound p _ _ _ (h.normalZ i) n 0 (enc c.shape rest ++ c.shape.terminal b)
      exact ⟨_,i.succ::rest,b,ht,by simpa [param,base,frame,OpenRight.attachZ_eval,Word.eval,enc,Auto.Radix.enc,rep,List.append_assoc] using hr⟩
    | succ k =>
      obtain ⟨ht,hr⟩ := open_sound p _ _ _ (h.normalS i) n k (enc c.shape rest ++ c.shape.terminal b)
      exact ⟨_,List.replicate (k+1) 0 ++ i.succ::rest,b,ht,by simpa [param,base,frame,OpenRight.attachZ_eval,Word.eval,enc,Auto.Radix.enc_append,Auto.Radix.enc_rep,rep,Auto.Radix.enc,List.append_assoc] using hr⟩

theorem never (p : PartialMachine) (c : Cert) (h : Checked p c) (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have arbitrary : ∀ k : Nat, ∃ t n ds b, k ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some (frame c.shape n ds b) := by
    intro k
    induction k with
    | zero => exact ⟨c.entry,0,[],false,by omega,h.seed⟩
    | succ k ih =>
      obtain ⟨t,n,ds,b,ht,hr⟩ := ih
      obtain ⟨d,es,e,hd,hs⟩ := live p c h n ds b
      exact ⟨t+d,n+1,es,e,by omega,join0 hr hs⟩
  intro n
  obtain ⟨t,k,ds,b,ht,hr⟩ := arbitrary n
  have hz : (zrun p t start).map project = some (frame c.shape k ds b) :=
    (run_project p t start).trans hr
  cases he : zrun p t start with
  | none => simp [he] at hz
  | some z =>
    have H := zrun_sound p m hm t start z he
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he' : run m n blank with
    | none => simp [he'] at H
    | some c => rfl
#print axioms never
end BB6Coverage.Agent31Pump.Auto2.GrowRadix
