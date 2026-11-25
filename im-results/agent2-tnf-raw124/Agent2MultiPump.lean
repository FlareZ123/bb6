import BlockPump

/- Multi-block sweeps: each tape side may have any number of repeated words.
   Every repetition exponent is the same arbitrary n; constants are explicit.
   Transfers leave the untouched symbolic tails entirely unconstrained. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2MultiPump
open BB6Coverage BB6Coverage.Agent50Pump Agent50Zipper

structure Piece where
  block : List Bool
  post : List Bool
  deriving DecidableEq, Repr
structure MWord where
  pre : List Bool
  rest : List Piece
  deriving DecidableEq, Repr

def evalRest (n : Nat) : List Piece → List Bool
  | [] => []
  | b :: bs => rep b.block n ++ b.post ++ evalRest n bs

def MWord.eval (w : MWord) (n : Nat) := w.pre ++ evalRest n w.rest
def MWord.closed (w : MWord) := w.rest.isEmpty

theorem MWord.closed_sound (w : MWord) (n : Nat) (h : w.closed = true) :
    evalRest n w.rest = [] := by
  have h' : w.rest = [] := by simpa [MWord.closed] using h
  simp [h',evalRest]

def MWord.grow (w : MWord) : MWord := {w with rest := w.rest.map fun b => ⟨b.block,b.block++b.post⟩}

theorem evalRest_grow (n : Nat) (xs : List Piece) :
    evalRest n (xs.map fun b => ⟨b.block,b.block++b.post⟩) = evalRest (n+1) xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons,evalRest,ih,rep,List.append_assoc,← List.append_assoc (rep b.block n) b.block,rep_snoc]

theorem MWord.grow_sound (w : MWord) (n : Nat) : w.grow.eval n = w.eval (n+1) := by
  simp only [MWord.eval,MWord.grow,evalRest_grow]

def MWord.eqCheck (w v : MWord) : Bool :=
  if w = v then true else
  match w.rest,v.rest with
  | a::as,b::bs => decide (as=bs) && (Word.mk w.pre a.block a.post).eqCheck ⟨v.pre,b.block,b.post⟩
  | _,_ => false

theorem MWord.eqCheck_sound (w v : MWord) (h : w.eqCheck v = true) (n : Nat) :
    w.eval n = v.eval n := by
  by_cases he : w=v
  · rw [he]
  · unfold MWord.eqCheck at h
    simp only [he,if_false] at h
    cases ha : w.rest with
    | nil => simp [ha] at h
    | cons a as =>
      cases hb : v.rest with
      | nil => simp [ha,hb] at h
      | cons b bs =>
        simp only [ha,hb,Bool.and_eq_true,decide_eq_true_eq] at h
        have H := Word.eqCheck_sound _ _ h.2 n
        simp only [Word.eval] at H
        simp only [MWord.eval,ha,hb,evalRest,h.1]
        simpa only [List.append_assoc] using congrArg (fun s : List Bool => s ++ evalRest n bs) H

structure MShape where
  q : Fin 6
  l : MWord
  r : MWord
  deriving DecidableEq, Repr

def MShape.eval (s : MShape) (n : Nat) : HZ := ⟨s.q,s.l.eval n,s.r.eval n⟩
def MShape.grow (s : MShape) : MShape := ⟨s.q,s.l.grow,s.r.grow⟩
theorem MShape.grow_sound (s : MShape) (n : Nat) : s.grow.eval n = s.eval (n+1) := by
  simp [MShape.eval,MShape.grow,MWord.grow_sound]

inductive MOp where
  | step
  | rewriteL (w : MWord)
  | rewriteR (w : MWord)
  | right (k c : Nat) (v : List Bool)
  | left (k c : Nat) (v : List Bool)
  deriving Repr

def MOp.lower : MOp → Nat | .step => 1 | _ => 0

def MOp.apply (p : PartialMachine) (s : MShape) : MOp → Option MShape
  | .step => (openStep p s.l.closed s.r.closed ⟨s.q,s.l.pre,s.r.pre⟩).map fun z =>
      ⟨z.q,{s.l with pre := z.l},{s.r with pre := z.r}⟩
  | .rewriteL w => if s.l.eqCheck w then some {s with l := w} else none
  | .rewriteR w => if s.r.eqCheck w then some {s with r := w} else none
  | .right k c v =>
      match s.r.rest with
      | [] => none
      | b::bs =>
        let o := s.l.pre.take k
        let a := s.r.pre
        if openRun p false false c ⟨s.q,o,a++b.block⟩ = some ⟨s.q,o++v,a⟩ then
          some ⟨s.q,⟨o,⟨v,s.l.pre.drop k⟩::s.l.rest⟩,⟨a++b.post,bs⟩⟩
        else none
  | .left k c v =>
      match s.l.rest with
      | [] => none
      | b::bs =>
        let o := s.r.pre.take k
        let a := s.l.pre
        if openRun p false false c ⟨s.q,a++b.block,o⟩ = some ⟨s.q,a,o++v⟩ then
          some ⟨s.q,⟨a++b.post,bs⟩,⟨o,⟨v,s.r.pre.drop k⟩::s.r.rest⟩⟩
        else none

theorem MOp.sound (p : PartialMachine) (s t : MShape) (op : MOp)
    (h : op.apply p s = some t) (n : Nat) :
    ∃ c, op.lower ≤ c ∧ hrun p c (s.eval n) = some (t.eval n) := by
  cases op with
  | step =>
    cases hs : openStep p s.l.closed s.r.closed ⟨s.q,s.l.pre,s.r.pre⟩ with
    | none => simp [MOp.apply,hs] at h
    | some z =>
      simp [MOp.apply,hs] at h; subst t
      have H := openStep_sound p s.l.closed s.r.closed ⟨s.q,s.l.pre,s.r.pre⟩ z
        (evalRest n s.l.rest) (evalRest n s.r.rest) (s.l.closed_sound n) (s.r.closed_sound n) hs
      exact ⟨1,by decide,by simpa [hrun,MShape.eval,MWord.eval,tail] using H⟩
  | rewriteL w =>
    by_cases H : s.l.eqCheck w = true
    · simp [MOp.apply,H] at h; subst t
      exact ⟨0,by simp [MOp.lower],by simp [hrun,MShape.eval,s.l.eqCheck_sound w H n]⟩
    · simp [MOp.apply,H] at h
  | rewriteR w =>
    by_cases H : s.r.eqCheck w = true
    · simp [MOp.apply,H] at h; subst t
      exact ⟨0,by simp [MOp.lower],by simp [hrun,MShape.eval,s.r.eqCheck_sound w H n]⟩
    · simp [MOp.apply,H] at h
  | right k c v =>
    cases hb : s.r.rest with
    | nil => simp [MOp.apply,hb] at h
    | cons b bs =>
      let o := s.l.pre.take k
      let a := s.r.pre
      by_cases H : openRun p false false c ⟨s.q,o,a++b.block⟩ = some ⟨s.q,o++v,a⟩
      · have HH := H; dsimp [o,a] at HH
        simp [MOp.apply,hb,HH] at h; subst t
        have Hr := sweepR p s.q a b.block o v c H n (s.l.pre.drop k ++ evalRest n s.l.rest) (b.post++evalRest n bs)
        refine ⟨c*n,by simp [MOp.lower],?_⟩
        simpa [MShape.eval,MWord.eval,hb,evalRest,o,a,List.append_assoc,← List.append_assoc (s.l.pre.take k) (s.l.pre.drop k)] using Hr
      · have HH := H; dsimp [o,a] at HH
        simp [MOp.apply,hb,HH] at h
  | left k c v =>
    cases hb : s.l.rest with
    | nil => simp [MOp.apply,hb] at h
    | cons b bs =>
      let o := s.r.pre.take k
      let a := s.l.pre
      by_cases H : openRun p false false c ⟨s.q,a++b.block,o⟩ = some ⟨s.q,a,o++v⟩
      · have HH := H; dsimp [o,a] at HH
        simp [MOp.apply,hb,HH] at h; subst t
        have Hr := sweepL p s.q a b.block o v c H n (b.post++evalRest n bs) (s.r.pre.drop k++evalRest n s.r.rest)
        refine ⟨c*n,by simp [MOp.lower],?_⟩
        simpa [MShape.eval,MWord.eval,hb,evalRest,o,a,List.append_assoc,← List.append_assoc (s.r.pre.take k) (s.r.pre.drop k)] using Hr
      · have HH := H; dsimp [o,a] at HH
        simp [MOp.apply,hb,HH] at h

def runM (p : PartialMachine) : List MOp → MShape → Option MShape
  | [],s => some s
  | op::ops,s => (op.apply p s).bind (runM p ops)

def lowerM (ops : List MOp) : Nat := (ops.map MOp.lower).sum

theorem runM_sound (p : PartialMachine) (ops : List MOp) (s t : MShape)
    (h : runM p ops s = some t) (n : Nat) :
    ∃ c, lowerM ops ≤ c ∧ hrun p c (s.eval n) = some (t.eval n) := by
  induction ops generalizing s with
  | nil => simp [runM] at h; subst t; exact ⟨0,by simp [lowerM],rfl⟩
  | cons op ops ih =>
    simp only [runM] at h
    cases hs : op.apply p s with
    | none => simp [hs] at h
    | some u =>
      obtain ⟨c,hc,Hc⟩ := op.sound p s u hs n
      obtain ⟨d,hd,Hd⟩ := ih u (by simpa [hs] using h)
      exact ⟨c+d,by simp [lowerM] at *;omega,hjoin Hc Hd⟩

structure MCertificate where
  entry : Nat
  shape : MShape
  ops : List MOp
  deriving Repr

def MCertificate.check (p : PartialMachine) (c : MCertificate) : Bool :=
  decide (hrun p c.entry ⟨0,[],[]⟩ = some (c.shape.eval 0)) &&
  decide (runM p c.ops c.shape = some c.shape.grow) &&
  decide (0 < lowerM c.ops)

theorem MCertificate.arbitrary (p : PartialMachine) (c : MCertificate) (h : c.check p = true) (n : Nat) :
    ∃ k, n ≤ k ∧ hrun p k ⟨0,[],[]⟩ = some (c.shape.eval n) := by
  simp [MCertificate.check] at h
  induction n with
  | zero => exact ⟨c.entry,by omega,h.1.1⟩
  | succ n ih =>
    obtain ⟨k,hk,Hk⟩ := ih
    obtain ⟨t,ht,Ht⟩ := runM_sound p c.ops c.shape c.shape.grow h.1.2 n
    exact ⟨k+t,by omega,hjoin Hk (by simpa [MShape.grow_sound] using Ht)⟩

theorem MCertificate.never (p : PartialMachine) (c : MCertificate) (h : c.check p = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  obtain ⟨k,hk,Hk⟩ := c.arbitrary p h n
  obtain ⟨h',H'⟩ := hrun_sound p k _ _ 0 Hk
  have H := zrun_sound p m hm k _ _ H'
  rw [blank_embed] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl

#print axioms MCertificate.arbitrary
#print axioms MCertificate.never
end BB6.Agent2MultiPump
