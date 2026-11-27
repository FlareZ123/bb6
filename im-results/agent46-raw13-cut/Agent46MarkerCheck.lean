import Agent46RadixCheck

set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto.Marker
open BB6Coverage Agent31Pump Auto Agent50Zipper Counter Radix

/-- Little-endian radix-four digits with one distinguished movable marker.
    All digits above the marker are zero. -/
structure Shape where
  q : Fin 6
  left : List Bool
  free : Fin 4 → List Bool
  mark : Fin 4 → List Bool
  sentinel : List Bool

def freeShape (s : Shape) : Radix.Shape 3 := ⟨s.q,s.left,s.free,fun _ => [],[]⟩
def enc (s : Shape) (ds : List (Fin 4)) : List Bool := Radix.enc (freeShape s) ds

def frame (s : Shape) (ds : List (Fin 4)) (d : Fin 4) (n : Nat) : Z0 :=
  ⟨s.q,s.left,enc s ds ++ s.mark d ++ rep (s.free 0) n ++ s.sentinel⟩

def param (s : Shape) (reset long : Bool) (tail : List Bool) : PZ :=
  Radix.param (freeShape s) reset long tail

def over (s : Shape) (long : Bool) : PZ :=
  ⟨s.q,.lit s.left,if long then .periodic (s.mark 0 ++ s.free 0) (s.free 0)
    (.lit (s.free 0 ++ s.sentinel)) else .lit (s.mark 0 ++ s.free 0 ++ s.sentinel)⟩

structure Cert where
  shape : Shape
  entry : Nat
  freeZ : Fin 3 → Macro
  freeS : Fin 3 → Macro
  markZ : Fin 3 → Macro
  markS : Fin 3 → Macro
  moveZ : Macro
  moveS : Macro
  overZ : Macro
  overS : Macro

structure Checked (p : PartialMachine) (c : Cert) : Prop where
  seed : run0 p c.entry ⟨0,[],[]⟩ = some (frame c.shape [] 0 0)
  freeZ : ∀ i : Fin 3, checkOpen p (param c.shape false false (c.shape.free i.castSucc))
    (param c.shape true false (c.shape.free i.succ)) (c.freeZ i) = true
  freeS : ∀ i : Fin 3, checkOpen p (param c.shape false true (c.shape.free i.castSucc))
    (param c.shape true true (c.shape.free i.succ)) (c.freeS i) = true
  markZ : ∀ i : Fin 3, checkOpen p (param c.shape false false (c.shape.mark i.castSucc))
    (param c.shape true false (c.shape.mark i.succ)) (c.markZ i) = true
  markS : ∀ i : Fin 3, checkOpen p (param c.shape false true (c.shape.mark i.castSucc))
    (param c.shape true true (c.shape.mark i.succ)) (c.markS i) = true
  moveZ : checkOpen p (param c.shape false false (c.shape.mark 3 ++ c.shape.free 0))
    (param c.shape true false (c.shape.free 0 ++ c.shape.mark 0)) c.moveZ = true
  moveS : checkOpen p (param c.shape false true (c.shape.mark 3 ++ c.shape.free 0))
    (param c.shape true true (c.shape.free 0 ++ c.shape.mark 0)) c.moveS = true
  overZ : checkClosed p (param c.shape false false (c.shape.mark 3 ++ c.shape.sentinel))
    (over c.shape false) c.overZ = true
  overS : checkClosed p (param c.shape false true (c.shape.mark 3 ++ c.shape.sentinel))
    (over c.shape true) c.overS = true

theorem rep_shift (P : List Bool) (k : Nat) : rep P k ++ P = P ++ rep P k := rep_snoc P k

theorem live (p : PartialMachine) (c : Cert) (h : Checked p c)
    (ds : List (Fin 4)) (d : Fin 4) (n : Nat) :
    ∃ t ds' d' n', 0<t ∧ run0 p t (frame c.shape ds d n) = some (frame c.shape ds' d' n') := by
  obtain ⟨k,hk⟩ := Radix.splitCarry (r:=3) ds
  rcases hk with hk | ⟨i,rest,hk⟩
  · subst ds
    by_cases hd : d.val = 3
    · have e : d = 3 := Fin.ext hd
      subst d
      cases n with
      | zero =>
        cases k with
        | zero =>
          obtain ⟨ht,hr⟩ := closed_sound p _ _ _ h.overZ 0
          exact ⟨_,[],0,1,ht,by simpa [frame,enc,freeShape,Radix.enc,param,Radix.param,over,PZ.eval,Word.eval,rep] using hr⟩
        | succ k =>
          obtain ⟨ht,hr⟩ := closed_sound p _ _ _ h.overS k
          exact ⟨_,[],0,k+2,ht,by simpa [frame,enc,Radix.enc_rep,freeShape,Radix.enc,param,Radix.param,over,PZ.eval,Word.eval,rep,List.append_assoc,← List.append_assoc (rep (c.shape.free 0) k) (c.shape.free 0) c.shape.sentinel,rep_shift] using hr⟩
      | succ n =>
        cases k with
        | zero =>
          obtain ⟨ht,hr⟩ := open_sound p _ _ _ h.moveZ 0 (rep (c.shape.free 0) n ++ c.shape.sentinel)
          exact ⟨_,[0],0,n,ht,by simpa [frame,enc,freeShape,Radix.enc,param,Radix.param,OpenRight.attachZ_eval,Word.eval,rep,List.append_assoc] using hr⟩
        | succ k =>
          obtain ⟨ht,hr⟩ := open_sound p _ _ _ h.moveS k (rep (c.shape.free 0) n ++ c.shape.sentinel)
          have hr' : run0 p (c.moveS.a*k+c.moveS.b) (frame c.shape (List.replicate (k+1) (Fin.last 3)) 3 (n+1)) =
              some (frame c.shape (List.replicate (k+1) 0 ++ [0]) 0 n) := by
            simpa [frame,enc,Radix.enc_append,Radix.enc_rep,freeShape,Radix.enc,param,Radix.param,OpenRight.attachZ_eval,Word.eval,rep,List.append_assoc] using hr
          exact ⟨_,List.replicate (k+1) 0 ++ [0],0,n,ht,hr'⟩
    · let i : Fin 3 := ⟨d.val,by omega⟩
      have e : i.castSucc = d := Fin.ext rfl
      rw [← e]
      cases k with
      | zero =>
        obtain ⟨ht,hr⟩ := open_sound p _ _ _ (h.markZ i) 0 (rep (c.shape.free 0) n ++ c.shape.sentinel)
        exact ⟨_,[],i.succ,n,ht,by simpa [frame,enc,freeShape,Radix.enc,param,Radix.param,OpenRight.attachZ_eval,Word.eval,List.append_assoc] using hr⟩
      | succ k =>
        obtain ⟨ht,hr⟩ := open_sound p _ _ _ (h.markS i) k (rep (c.shape.free 0) n ++ c.shape.sentinel)
        exact ⟨_,List.replicate (k+1) 0,i.succ,n,ht,by simpa [frame,enc,Radix.enc_rep,freeShape,param,Radix.param,OpenRight.attachZ_eval,Word.eval,rep,List.append_assoc] using hr⟩
  · subst ds
    cases k with
    | zero =>
      obtain ⟨ht,hr⟩ := open_sound p _ _ _ (h.freeZ i) 0 (enc c.shape rest ++ c.shape.mark d ++ rep (c.shape.free 0) n ++ c.shape.sentinel)
      exact ⟨_,i.succ::rest,d,n,ht,by simpa [frame,enc,freeShape,Radix.enc,param,Radix.param,OpenRight.attachZ_eval,Word.eval,List.append_assoc] using hr⟩
    | succ k =>
      obtain ⟨ht,hr⟩ := open_sound p _ _ _ (h.freeS i) k (enc c.shape rest ++ c.shape.mark d ++ rep (c.shape.free 0) n ++ c.shape.sentinel)
      exact ⟨_,List.replicate (k+1) 0 ++ i.succ::rest,d,n,ht,by simpa [frame,enc,Radix.enc_append,Radix.enc_rep,freeShape,param,Radix.param,OpenRight.attachZ_eval,Word.eval,rep,List.append_assoc] using hr⟩

theorem never (p : PartialMachine) (c : Cert) (h : Checked p c)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have arbitrary : ∀ k : Nat, ∃ t ds d n, k ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some (frame c.shape ds d n) := by
    intro k
    induction k with
    | zero => exact ⟨c.entry,[],0,0,by omega,h.seed⟩
    | succ k ih =>
      obtain ⟨t,ds,d,n,ht,hr⟩ := ih
      obtain ⟨dt,es,e,n',hd,hs⟩ := live p c h ds d n
      exact ⟨t+dt,es,e,n',by omega,join0 hr hs⟩
  intro n
  obtain ⟨t,ds,d,k,ht,hr⟩ := arbitrary n
  have hz : (zrun p t start).map project = some (frame c.shape ds d k) := (run_project p t start).trans hr
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
end BB6Coverage.Agent31Pump.Auto.Marker
