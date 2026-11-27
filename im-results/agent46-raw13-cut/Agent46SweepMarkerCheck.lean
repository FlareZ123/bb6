import Agent46RadixCheck

set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto.SweepMarker
open BB6Coverage Agent31Pump Auto Agent50Zipper Counter Radix

structure Shape where
  q : Fin 6
  left : List Bool
  free : Fin 4 → List Bool
  mark : List Bool
  sentinel : List Bool
  unmarked : List Bool

def base (s : Shape) : Radix.Shape 3 := ⟨s.q,s.left,s.free,fun _ => [],[]⟩
def enc (s : Shape) := Radix.enc (base s)
def param (s : Shape) := Radix.param (base s)
def frame (s : Shape) (ds : List (Fin 4)) (tail : Option Nat) : Z0 :=
  ⟨s.q,s.left,enc s ds ++ (match tail with
    | none => s.unmarked
    | some n => s.mark ++ rep (s.free 0) n ++ s.sentinel)⟩
def overIn (s : Shape) (long : Bool) : PZ :=
  ⟨s.q,.lit s.left,if long then .periodic (s.free 3 ++ s.free 3) (s.free 3) (.lit s.unmarked) else .lit (s.free 3 ++ s.unmarked)⟩
def overOut (s : Shape) (long : Bool) : PZ :=
  ⟨s.q,.lit s.left,if long then .periodic (s.free 0 ++ s.mark ++ s.free 0) (s.free 0) (.lit s.sentinel) else .lit (s.free 0 ++ s.mark ++ s.sentinel)⟩
structure Cert where
  shape : Shape
  entry : Nat
  normalZ : Fin 3 → Macro
  normalS : Fin 3 → Macro
  moveZ : Macro
  moveS : Macro
  endZ : Macro
  endS : Macro
  overZ : Macro
  overS : Macro
structure Checked (p : PartialMachine) (c : Cert) : Prop where
  seed : run0 p c.entry ⟨0,[],[]⟩ = some (frame c.shape [0] none)
  normalZ : ∀ i : Fin 3, checkOpen p (param c.shape false false (c.shape.free i.castSucc)) (param c.shape true false (c.shape.free i.succ)) (c.normalZ i) = true
  normalS : ∀ i : Fin 3, checkOpen p (param c.shape false true (c.shape.free i.castSucc)) (param c.shape true true (c.shape.free i.succ)) (c.normalS i) = true
  moveZ : checkOpen p (param c.shape false false (c.shape.mark ++ c.shape.free 0)) (param c.shape true false (c.shape.free 0 ++ c.shape.mark)) c.moveZ = true
  moveS : checkOpen p (param c.shape false true (c.shape.mark ++ c.shape.free 0)) (param c.shape true true (c.shape.free 0 ++ c.shape.mark)) c.moveS = true
  endZ : checkClosed p (param c.shape false false (c.shape.mark ++ c.shape.sentinel)) (param c.shape true false (c.shape.free 0 ++ c.shape.unmarked)) c.endZ = true
  endS : checkClosed p (param c.shape false true (c.shape.mark ++ c.shape.sentinel)) (param c.shape true true (c.shape.free 0 ++ c.shape.unmarked)) c.endS = true
  overZ : checkClosed p (overIn c.shape false) (overOut c.shape false) c.overZ = true
  overS : checkClosed p (overIn c.shape true) (overOut c.shape true) c.overS = true

theorem live (p : PartialMachine) (c : Cert) (h : Checked p c)
    (ds : List (Fin 4)) (b : Option Nat) (hb : ds ≠ []) :
    ∃ t ds' b', ds' ≠ [] ∧ 0<t ∧ run0 p t (frame c.shape ds b) = some (frame c.shape ds' b') := by
  obtain ⟨k,hk⟩ := Radix.splitCarry (r:=3) ds
  rcases hk with hk | ⟨i,rest,hk⟩
  · subst ds
    cases b with
    | none =>
      cases k with
      | zero => exact False.elim (hb rfl)
      | succ k =>
        cases k with
        | zero =>
          obtain ⟨ht,hr⟩ := closed_sound p _ _ _ h.overZ 0
          exact ⟨_,[0],some 0,by simp,ht,by simpa [frame,enc,base,Radix.enc,overIn,overOut,PZ.eval,Word.eval,rep] using hr⟩
        | succ k =>
          obtain ⟨ht,hr⟩ := closed_sound p _ _ _ h.overS k
          exact ⟨_,[0],some (k+1),by simp,ht,by simpa [frame,enc,base,Radix.enc_rep,Radix.enc,overIn,overOut,PZ.eval,Word.eval,rep,List.append_assoc] using hr⟩
    | some n =>
      cases n with
      | zero =>
        cases k with
        | zero => exact False.elim (hb rfl)
        | succ k =>
          obtain ⟨ht,hr⟩ := closed_sound p _ _ _ h.endS k
          exact ⟨_,List.replicate (k+1) 0 ++ [0],none,by simp,ht,by simpa [frame,enc,base,Radix.enc_append,Radix.enc_rep,Radix.enc,param,Radix.param,PZ.eval,Word.eval,rep,List.append_assoc] using hr⟩
      | succ n =>
        cases k with
        | zero => exact False.elim (hb rfl)
        | succ k =>
          obtain ⟨ht,hr⟩ := open_sound p _ _ _ h.moveS k (rep (c.shape.free 0) n ++ c.shape.sentinel)
          exact ⟨_,List.replicate (k+1) 0 ++ [0],some n,by simp,ht,by simpa [frame,enc,base,Radix.enc_append,Radix.enc_rep,Radix.enc,param,Radix.param,OpenRight.attachZ_eval,Word.eval,rep,List.append_assoc] using hr⟩
  · subst ds
    let tail := match b with | none => c.shape.unmarked | some n => c.shape.mark ++ rep (c.shape.free 0) n ++ c.shape.sentinel
    cases k with
    | zero =>
      obtain ⟨ht,hr⟩ := open_sound p _ _ _ (h.normalZ i) 0 (enc c.shape rest ++ tail)
      exact ⟨_,i.succ::rest,b,by simp,ht,by simpa [frame,enc,base,Radix.enc,param,Radix.param,OpenRight.attachZ_eval,Word.eval,tail,List.append_assoc] using hr⟩
    | succ k =>
      obtain ⟨ht,hr⟩ := open_sound p _ _ _ (h.normalS i) k (enc c.shape rest ++ tail)
      exact ⟨_,List.replicate (k+1) 0 ++ i.succ::rest,b,by simp,ht,by simpa [frame,enc,base,Radix.enc_append,Radix.enc_rep,Radix.enc,param,Radix.param,OpenRight.attachZ_eval,Word.eval,rep,tail,List.append_assoc] using hr⟩

theorem never (p : PartialMachine) (c : Cert) (h : Checked p c)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have arbitrary : ∀ k : Nat, ∃ t ds b, ds ≠ [] ∧ k ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some (frame c.shape ds b) := by
    intro k
    induction k with
    | zero => exact ⟨c.entry,[0],none,by simp,by omega,h.seed⟩
    | succ k ih =>
      obtain ⟨t,ds,b,hb,ht,hr⟩ := ih
      obtain ⟨d,es,e,he,hd,hs⟩ := live p c h ds b hb
      exact ⟨t+d,es,e,he,by omega,join0 hr hs⟩
  intro n
  obtain ⟨t,ds,b,hb,ht,hr⟩ := arbitrary n
  have hz : (zrun p t start).map project = some (frame c.shape ds b) := (run_project p t start).trans hr
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
end BB6Coverage.Agent31Pump.Auto.SweepMarker
