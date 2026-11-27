import Agent46CounterCheck

set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto.Radix
open BB6Coverage Agent31Pump Auto Agent50Zipper Counter

/-- A finite little-endian digit alphabet and a two-valued terminal digit.
    The maximum digit is reset during carry. Terminal overflow can extend
    by any fixed list of ordinary digits. -/
structure Shape (r : Nat) where
  q : Fin 6
  left : List Bool
  digit : Fin (r+1) → List Bool
  terminal : Bool → List Bool
  extension : List (Fin (r+1))

def enc {r : Nat} (s : Shape r) : List (Fin (r+1)) → List Bool
  | [] => []
  | d::ds => s.digit d ++ enc s ds

theorem enc_append {r : Nat} (s : Shape r) (ds es : List (Fin (r+1))) :
    enc s (ds++es) = enc s ds ++ enc s es := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [enc,ih,List.append_assoc]

theorem enc_rep {r : Nat} (s : Shape r) (d : Fin (r+1)) (k : Nat) :
    enc s (List.replicate k d) = rep (s.digit d) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ,enc,rep,ih]

def frame {r : Nat} (s : Shape r) (ds : List (Fin (r+1))) (b : Bool) : Z0 :=
  ⟨s.q,s.left,enc s ds ++ s.terminal b⟩

def param {r : Nat} (s : Shape r) (reset long : Bool) (tail : List Bool) : PZ :=
  let d := s.digit (if reset then 0 else Fin.last r)
  ⟨s.q,.lit s.left,if long then .periodic d d (.lit tail) else .lit tail⟩

theorem splitCarry {r : Nat} (ds : List (Fin (r+1))) :
    ∃ k, ds = List.replicate k (Fin.last r) ∨
      ∃ (i : Fin r) (rest : List (Fin (r+1))), ds = List.replicate k (Fin.last r) ++ i.castSucc::rest := by
  induction ds with
  | nil => exact ⟨0,Or.inl rfl⟩
  | cons d ds ih =>
    by_cases h : d.val = r
    · have e : d = Fin.last r := Fin.ext h
      subst d
      obtain ⟨k,he⟩ := ih
      refine ⟨k+1,?_⟩
      rcases he with he | ⟨i,rest,he⟩
      · exact Or.inl (by simp only [List.replicate_succ,he])
      · exact Or.inr ⟨i,rest,by simp only [List.replicate_succ,List.cons_append,he]⟩
    · have hlt : d.val < r := by omega
      let i : Fin r := ⟨d.val,hlt⟩
      exact ⟨0,Or.inr ⟨i,ds,by have e : i.castSucc = d := Fin.ext rfl; simp [e]⟩⟩

structure Cert (r : Nat) where
  shape : Shape r
  entry : Nat
  seed : List (Fin (r+1))
  top : Bool
  normalZ : Fin r → Macro
  normalS : Fin r → Macro
  terminalZ : Bool → Macro
  terminalS : Bool → Macro

def endWord {r : Nat} (s : Shape r) (b : Bool) : List Bool :=
  if b then enc s s.extension ++ s.terminal false else s.terminal true

structure Checked {r : Nat} (p : PartialMachine) (c : Cert r) : Prop where
  seed : run0 p c.entry ⟨0,[],[]⟩ = some (frame c.shape c.seed c.top)
  normalZ : ∀ i : Fin r, checkOpen p (param c.shape false false (c.shape.digit i.castSucc))
    (param c.shape true false (c.shape.digit i.succ)) (c.normalZ i) = true
  normalS : ∀ i : Fin r, checkOpen p (param c.shape false true (c.shape.digit i.castSucc))
    (param c.shape true true (c.shape.digit i.succ)) (c.normalS i) = true
  terminalZ : ∀ b : Bool, checkClosed p (param c.shape false false (c.shape.terminal b))
    (param c.shape true false (endWord c.shape b)) (c.terminalZ b) = true
  terminalS : ∀ b : Bool, checkClosed p (param c.shape false true (c.shape.terminal b))
    (param c.shape true true (endWord c.shape b)) (c.terminalS b) = true

/-- Every legal digit list admits another positive-cost return to the language. -/
theorem live {r : Nat} (p : PartialMachine) (c : Cert r) (h : Checked p c)
    (ds : List (Fin (r+1))) (b : Bool) :
    ∃ t ds' b', 0<t ∧ run0 p t (frame c.shape ds b) = some (frame c.shape ds' b') := by
  obtain ⟨k,hk⟩ := splitCarry ds
  rcases hk with hk | ⟨i,rest,hk⟩
  · subst ds
    cases k with
    | zero =>
      obtain ⟨ht,hr⟩ := closed_sound p _ _ _ (h.terminalZ b) 0
      cases b
      · exact ⟨_,[],true,ht,by simpa [param,endWord,frame,PZ.eval,Word.eval,enc] using hr⟩
      · exact ⟨_,c.shape.extension,false,ht,by simpa [param,endWord,frame,PZ.eval,Word.eval,enc] using hr⟩
    | succ k =>
      obtain ⟨ht,hr⟩ := closed_sound p _ _ _ (h.terminalS b) k
      cases b
      · exact ⟨_,List.replicate (k+1) 0,true,ht,by simpa [param,endWord,frame,PZ.eval,Word.eval,enc_append,enc_rep,rep,enc,List.append_assoc] using hr⟩
      · exact ⟨_,List.replicate (k+1) 0 ++ c.shape.extension,false,ht,by simpa [param,endWord,frame,PZ.eval,Word.eval,enc_append,enc_rep,rep,enc,List.append_assoc] using hr⟩
  · subst ds
    cases k with
    | zero =>
      obtain ⟨ht,hr⟩ := open_sound p _ _ _ (h.normalZ i) 0 (enc c.shape rest ++ c.shape.terminal b)
      exact ⟨_,i.succ::rest,b,ht,by simpa [param,frame,OpenRight.attachZ_eval,Word.eval,enc,List.append_assoc] using hr⟩
    | succ k =>
      obtain ⟨ht,hr⟩ := open_sound p _ _ _ (h.normalS i) k (enc c.shape rest ++ c.shape.terminal b)
      exact ⟨_,List.replicate (k+1) 0 ++ i.succ::rest,b,ht,by simpa [param,frame,OpenRight.attachZ_eval,Word.eval,enc_append,enc_rep,rep,enc,List.append_assoc] using hr⟩

theorem never {r : Nat} (p : PartialMachine) (c : Cert r) (h : Checked p c)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have arbitrary : ∀ k : Nat, ∃ t ds b, k ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some (frame c.shape ds b) := by
    intro k
    induction k with
    | zero => exact ⟨c.entry,c.seed,c.top,by omega,h.seed⟩
    | succ k ih =>
      obtain ⟨t,ds,b,ht,hr⟩ := ih
      obtain ⟨d,es,e,hd,hs⟩ := live p c h ds b
      exact ⟨t+d,es,e,by omega,join0 hr hs⟩
  intro n
  obtain ⟨t,ds,b,ht,hr⟩ := arbitrary n
  have hz : (zrun p t start).map project = some (frame c.shape ds b) :=
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
end BB6Coverage.Agent31Pump.Auto.Radix
