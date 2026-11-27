import Agent46OpenLeftSweep

set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto.CounterLeft
open BB6Coverage Agent31Pump Auto Agent50Zipper

structure Macro where
  ops : List Action
  a : Nat
  b : Nat
  deriving DecidableEq, Repr

def checkOpen (p : PartialMachine) (f g : PZ) (m : Macro) : Bool :=
  match OpenLeft.traceRun p m.ops f with
  | none => false
  | some out => decide (0 < m.b ∧ out.a=m.a ∧ out.b=m.b ∧ out.z.norm=g.norm)

def checkClosed (p : PartialMachine) (f g : PZ) (m : Macro) : Bool :=
  match Auto.traceRun p m.ops f with
  | none => false
  | some out => decide (0 < m.b ∧ out.a=m.a ∧ out.b=m.b ∧ out.z.norm=g.norm)

theorem open_sound (p : PartialMachine) (f g : PZ) (m : Macro)
    (h : checkOpen p f g m = true) (n : Nat) (tail : List Bool) :
    0 < m.a*n+m.b ∧
    run0 p (m.a*n+m.b) ((OpenLeft.attachZ f tail).eval n) = some ((OpenLeft.attachZ g tail).eval n) := by
  unfold checkOpen at h
  cases hr : OpenLeft.traceRun p m.ops f with
  | none => simp [hr] at h
  | some out =>
    simp only [hr,decide_eq_true_eq] at h
    have hs := OpenLeft.traceRun_sound p m.ops hr n tail
    have hn := congrArg (fun z => (OpenLeft.attachZ z tail).eval n) h.2.2.2
    rw [OpenLeft.norm_attachZ_eval,OpenLeft.norm_attachZ_eval] at hn
    rw [h.2.1,h.2.2.1,hn] at hs
    exact ⟨by omega,hs⟩

theorem closed_sound (p : PartialMachine) (f g : PZ) (m : Macro)
    (h : checkClosed p f g m = true) (n : Nat) :
    0 < m.a*n+m.b ∧ run0 p (m.a*n+m.b) (f.eval n) = some (g.eval n) := by
  unfold checkClosed at h
  cases hr : Auto.traceRun p m.ops f with
  | none => simp [hr] at h
  | some out =>
    simp only [hr,decide_eq_true_eq] at h
    have hs := Auto.traceRun_sound p m.ops hr n
    have hn := congrArg (fun z : PZ => z.eval n) h.2.2.2
    rw [PZ.norm_sound,PZ.norm_sound] at hn
    rw [h.2.1,h.2.2.1,hn] at hs
    exact ⟨by omega,hs⟩

structure Shape where
  q : Fin 6
  right : List Bool
  pre : List Bool
  zero : List Bool
  one : List Bool
  post : List Bool
  extension : List Bool
  deriving DecidableEq, Repr

def encode (s : Shape) : List Bool → List Bool
  | [] => []
  | false::bs => s.zero ++ encode s bs
  | true::bs => s.one ++ encode s bs

theorem encode_append (s : Shape) (bs cs : List Bool) :
    encode s (bs++cs) = encode s bs ++ encode s cs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [encode,ih,List.append_assoc]

theorem encode_rep (s : Shape) (b : Bool) (k : Nat) :
    encode s (rep [b] k) = rep (if b then s.one else s.zero) k := by
  induction k with
  | zero => rfl
  | succ k ih => cases b <;> simp [rep,encode,ih]

def next (ext : List Bool) : List Bool → List Bool
  | [] => ext
  | false::bs => true::bs
  | true::bs => false::next ext bs

theorem split_next (ext bs : List Bool) :
    ∃ k, (bs = rep [true] k ∧ next ext bs = rep [false] k ++ ext) ∨
      ∃ rest, bs = rep [true] k ++ false::rest ∧ next ext bs = rep [false] k ++ true::rest := by
  induction bs with
  | nil => exact ⟨0,Or.inl ⟨rfl,rfl⟩⟩
  | cons b bs ih =>
    cases b with
    | false => exact ⟨0,Or.inr ⟨bs,rfl,rfl⟩⟩
    | true =>
      obtain ⟨k,h⟩ := ih
      refine ⟨k+1,?_⟩
      rcases h with ⟨h1,h2⟩ | ⟨rest,h1,h2⟩
      · exact Or.inl ⟨by simp [rep,h1],by simp [next,rep,h2]⟩
      · exact Or.inr ⟨rest,by simp [rep,h1],by simp [next,rep,h2]⟩

def frame (s : Shape) (bs : List Bool) : Z0 := ⟨s.q,s.pre++encode s bs++s.post,s.right⟩
def param (s : Shape) (r : Word) : PZ := ⟨s.q,r,.lit s.right⟩
def normal0 (s : Shape) (b : Bool) : PZ := param s (.lit (s.pre ++ if b then s.one else s.zero))
def normalS (s : Shape) (b : Bool) : PZ :=
  let d := if b then s.one else s.zero
  let e := if b then s.zero else s.one
  param s (.periodic (s.pre++d) d (.lit e))
def overflow0 (s : Shape) (out : Bool) : PZ := param s (.lit (s.pre++(if out then encode s s.extension else [])++s.post))
def overflowS (s : Shape) (out : Bool) : PZ :=
  let d := if out then s.zero else s.one
  param s (.periodic (s.pre++d) d (.lit ((if out then encode s s.extension else [])++s.post)))

structure Cert where
  shape : Shape
  entry : Nat
  seed : List Bool
  stop0 : Macro
  stopS : Macro
  over0 : Macro
  overS : Macro
  deriving DecidableEq, Repr

def check (p : PartialMachine) (c : Cert) : Bool :=
  decide (run0 p c.entry ⟨0,[],[]⟩ = some (frame c.shape c.seed)) &&
  checkOpen p (normal0 c.shape false) (normal0 c.shape true) c.stop0 &&
  checkOpen p (normalS c.shape true) (normalS c.shape false) c.stopS &&
  checkClosed p (overflow0 c.shape false) (overflow0 c.shape true) c.over0 &&
  checkClosed p (overflowS c.shape false) (overflowS c.shape true) c.overS

theorem live_step (p : PartialMachine) (c : Cert) (hc : check p c = true) (bs : List Bool) :
    ∃ t, 0 < t ∧ run0 p t (frame c.shape bs) = some (frame c.shape (next c.shape.extension bs)) := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hf,h0⟩,hs⟩,ho0⟩,hos⟩ := hc
  obtain ⟨k,h⟩ := split_next c.shape.extension bs
  rcases h with ⟨h1,h2⟩ | ⟨rest,h1,h2⟩
  · rw [h2,h1]
    cases k with
    | zero =>
      obtain ⟨ht,hr⟩ := closed_sound p _ _ _ ho0 0
      exact ⟨_,ht,by simpa [overflow0,param,PZ.eval,Word.eval,frame,rep,encode] using hr⟩
    | succ k =>
      obtain ⟨ht,hr⟩ := closed_sound p _ _ _ hos k
      exact ⟨_,ht,by simpa [overflowS,param,PZ.eval,Word.eval,frame,encode_append,encode_rep,rep,encode,List.append_assoc] using hr⟩
  · rw [h2,h1]
    cases k with
    | zero =>
      obtain ⟨ht,hr⟩ := open_sound p _ _ _ h0 0 (encode c.shape rest++c.shape.post)
      exact ⟨_,ht,by simpa [normal0,param,OpenLeft.attachZ_eval,Word.eval,frame,rep,encode,List.append_assoc] using hr⟩
    | succ k =>
      obtain ⟨ht,hr⟩ := open_sound p _ _ _ hs k (encode c.shape rest++c.shape.post)
      exact ⟨_,ht,by simpa [normalS,param,OpenLeft.attachZ_eval,Word.eval,frame,encode_append,encode_rep,rep,encode,List.append_assoc] using hr⟩

theorem never (p : PartialMachine) (c : Cert) (hc : check p c = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have first : run0 p c.entry ⟨0,[],[]⟩ = some (frame c.shape c.seed) := by
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
    exact hc.1.1.1.1
  have arbitrary : ∀ k : Nat, ∃ t bs, k ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some (frame c.shape bs) := by
    intro k
    induction k with
    | zero => exact ⟨c.entry,c.seed,by omega,first⟩
    | succ k ih =>
      obtain ⟨t,bs,ht,hr⟩ := ih
      obtain ⟨d,hd,hstep⟩ := live_step p c hc bs
      exact ⟨t+d,next c.shape.extension bs,by omega,join0 hr hstep⟩
  intro n
  obtain ⟨t,bs,ht,hr⟩ := arbitrary n
  have hz : (zrun p t start).map project = some (frame c.shape bs) :=
    (run_project p t start).trans hr
  cases h : zrun p t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound p m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms live_step
#print axioms never
end BB6Coverage.Agent31Pump.Auto.CounterLeft
