import Agent46RadixCheck

set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto.PrefixTerminal
open BB6Coverage Agent31Pump Auto Agent50Zipper Counter Radix

/-- A finite ordinary digit alphabet and an independently finite terminal
    alphabet. Each terminal transition can append a specified list of digits. -/
structure Shape (r s : Nat) where
  q : Fin 6
  left : List Bool
  pre : List Bool
  digit : Fin (r+1) → List Bool
  terminal : Fin (s+1) → List Bool
  next : Fin (s+1) → Fin (s+1)
  extension : Fin (s+1) → List (Fin (r+1))

def base {r s : Nat} (z : Shape r s) : Radix.Shape r := ⟨z.q,z.left,z.digit,fun _ => [],[]⟩
def enc {r s : Nat} (z : Shape r s) := Radix.enc (base z)
def frame {r s : Nat} (z : Shape r s) (ds : List (Fin (r+1))) (b : Fin (s+1)) : Z0 :=
  ⟨z.q,z.left,z.pre ++ enc z ds ++ z.terminal b⟩
def param {r s : Nat} (z : Shape r s) (reset long : Bool) (tail : List Bool) : PZ :=
  let d := z.digit (if reset then 0 else Fin.last r)
  ⟨z.q,.lit z.left,if long then .periodic (z.pre++d) d (.lit tail) else .lit (z.pre++tail)⟩
structure Cert (r s : Nat) where
  shape : Shape r s
  entry : Nat
  seed : List (Fin (r+1))
  top : Fin (s+1)
  normalZ : Fin r → Macro
  normalS : Fin r → Macro
  terminalZ : Fin (s+1) → Macro
  terminalS : Fin (s+1) → Macro

def endWord {r s : Nat} (z : Shape r s) (b : Fin (s+1)) := enc z (z.extension b) ++ z.terminal (z.next b)
structure Checked {r s : Nat} (p : PartialMachine) (c : Cert r s) : Prop where
  seed : run0 p c.entry ⟨0,[],[]⟩ = some (frame c.shape c.seed c.top)
  normalZ : ∀ i : Fin r, checkOpen p (param c.shape false false (c.shape.digit i.castSucc))
    (param c.shape true false (c.shape.digit i.succ)) (c.normalZ i) = true
  normalS : ∀ i : Fin r, checkOpen p (param c.shape false true (c.shape.digit i.castSucc))
    (param c.shape true true (c.shape.digit i.succ)) (c.normalS i) = true
  terminalZ : ∀ b : Fin (s+1), checkClosed p (param c.shape false false (c.shape.terminal b))
    (param c.shape true false (endWord c.shape b)) (c.terminalZ b) = true
  terminalS : ∀ b : Fin (s+1), checkClosed p (param c.shape false true (c.shape.terminal b))
    (param c.shape true true (endWord c.shape b)) (c.terminalS b) = true

theorem live {r s : Nat} (p : PartialMachine) (c : Cert r s) (h : Checked p c)
    (ds : List (Fin (r+1))) (b : Fin (s+1)) :
    ∃ t ds' b', 0<t ∧ run0 p t (frame c.shape ds b) = some (frame c.shape ds' b') := by
  obtain ⟨k,hk⟩ := Radix.splitCarry ds
  rcases hk with hk | ⟨i,rest,hk⟩
  · subst ds
    cases k with
    | zero =>
      obtain ⟨ht,hr⟩ := closed_sound p _ _ _ (h.terminalZ b) 0
      exact ⟨_,c.shape.extension b,c.shape.next b,ht,by simpa [param,base,endWord,frame,PZ.eval,Word.eval,enc,Radix.param,Radix.enc,List.append_assoc] using hr⟩
    | succ k =>
      obtain ⟨ht,hr⟩ := closed_sound p _ _ _ (h.terminalS b) k
      exact ⟨_,List.replicate (k+1) 0 ++ c.shape.extension b,c.shape.next b,ht,by simpa [param,base,endWord,frame,PZ.eval,Word.eval,enc,Radix.param,Radix.enc_append,Radix.enc_rep,rep,Radix.enc,List.append_assoc] using hr⟩
  · subst ds
    cases k with
    | zero =>
      obtain ⟨ht,hr⟩ := open_sound p _ _ _ (h.normalZ i) 0 (enc c.shape rest ++ c.shape.terminal b)
      exact ⟨_,i.succ::rest,b,ht,by simpa [param,base,frame,OpenRight.attachZ_eval,Word.eval,enc,Radix.param,Radix.enc,List.append_assoc] using hr⟩
    | succ k =>
      obtain ⟨ht,hr⟩ := open_sound p _ _ _ (h.normalS i) k (enc c.shape rest ++ c.shape.terminal b)
      exact ⟨_,List.replicate (k+1) 0 ++ i.succ::rest,b,ht,by simpa [param,base,frame,OpenRight.attachZ_eval,Word.eval,enc,Radix.param,Radix.enc_append,Radix.enc_rep,rep,Radix.enc,List.append_assoc] using hr⟩

theorem never {r s : Nat} (p : PartialMachine) (c : Cert r s) (h : Checked p c)
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
end BB6Coverage.Agent31Pump.Auto.PrefixTerminal
