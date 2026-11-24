import SparseZipper

set_option maxRecDepth 24000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent50Pump
open BB6Coverage Agent50Zipper

structure HZ where
  q : Fin 6
  l : List Bool
  r : List Bool
  deriving DecidableEq, Repr

def HZ.at (z : HZ) (h : Int) : Z := ⟨z.q,h,z.l,z.r⟩
def hmove (mv : Move) (z : HZ) : HZ :=
  if mv.right then ⟨mv.next,z.r.headD false::mv.write::z.l.tail,z.r.tail⟩
  else ⟨mv.next,z.l.tail,mv.write::z.r⟩
def hstep (p : PartialMachine) (z : HZ) : Option HZ :=
  ((p (z.q,z.l.headD false)).bind id).map (fun mv => hmove mv z)
def hrun (p : PartialMachine) : Nat → HZ → Option HZ
  | 0,z => some z
  | n+1,z => (hstep p z).bind (hrun p n)

theorem hrun_add (p : PartialMachine) (n k : Nat) (z : HZ) :
    hrun p (n+k) z = (hrun p n z).bind (hrun p k) := by
  induction n generalizing z with
  | zero => simp [hrun]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    simp only [hrun]
    cases hstep p z with
    | none => rfl
    | some t => exact ih t

theorem hjoin {p : PartialMachine} {n k : Nat} {a b c : HZ}
    (h : hrun p n a = some b) (g : hrun p k b = some c) :
    hrun p (n+k) a = some c := by rw [hrun_add,h]; exact g

theorem hstep_sound (p : PartialMachine) (a b : HZ) (h : Int)
    (H : hstep p a = some b) : ∃ h', step p (a.at h) = some (b.at h') := by
  unfold hstep at H
  cases hm : (p (a.q,a.l.headD false)).bind id with
  | none => rw [hm] at H; contradiction
  | some mv =>
    simp only [hm,Option.map_none,Option.map_some,Option.some.injEq] at H
    subst b
    cases hr : mv.right
    · refine ⟨h-1,?_⟩; change ((p (a.q,a.l.headD false)).bind id).map (fun mv => move mv (a.at h)) = _; rw [hm]; simp [HZ.at,move,hmove,hr]
    · refine ⟨h+1,?_⟩; change ((p (a.q,a.l.headD false)).bind id).map (fun mv => move mv (a.at h)) = _; rw [hm]; simp [HZ.at,move,hmove,hr]

theorem hrun_sound (p : PartialMachine) (n : Nat) (a b : HZ) (h : Int)
    (H : hrun p n a = some b) : ∃ h', zrun p n (a.at h) = some (b.at h') := by
  induction n generalizing a h with
  | zero => simp [hrun] at H; subst b; exact ⟨h,rfl⟩
  | succ n ih =>
    simp only [hrun] at H
    cases hs : hstep p a with
    | none => simp [hs] at H
    | some c =>
      obtain ⟨hc,Hc⟩ := hstep_sound p a c h hs
      obtain ⟨hd,Hd⟩ := ih c hc (by simpa [hs] using H)
      exact ⟨hd,by simpa [zrun,Hc] using Hd⟩

def tail (z : HZ) (L R : List Bool) : HZ := ⟨z.q,z.l++L,z.r++R⟩
-- cl and cr say whether a missing explicit symbol really is blank.
def openStep (p : PartialMachine) (cl cr : Bool) (z : HZ) : Option HZ :=
  if z.l.isEmpty && !cl then none else
  match (p (z.q,z.l.headD false)).bind id with
  | none => none
  | some mv => if mv.right && z.r.isEmpty && !cr then none else some (hmove mv z)

theorem openStep_sound (p : PartialMachine) (cl cr : Bool) (a b : HZ)
    (L R : List Bool) (hl : cl=true → L=[]) (hr : cr=true → R=[])
    (H : openStep p cl cr a = some b) :
    hstep p (tail a L R) = some (tail b L R) := by
  rcases a with ⟨q,l,r⟩
  cases l with
  | nil =>
    cases cl with
    | false => simp [openStep] at H
    | true =>
      have he := hl rfl; subst L
      simp only [openStep,List.isEmpty_nil,Bool.not_true,Bool.and_false,if_false] at H
      cases hp : (p (q,false)).bind id with
      | none => simp [hp] at H
      | some mv =>
        cases hm : mv.right <;> cases r with
        | nil =>
          cases cr with
          | false => simp [hp,hm] at H ⊢; all_goals try (subst b; simp [hstep,tail,hp,hmove,hm])
          | true =>
            have he := hr rfl; subst R
            simp [hp,hm] at H; subst b; simp [hstep,tail,hp,hmove,hm]
        | cons x xs =>
          simp [hp,hm] at H; subst b; simp [hstep,tail,hp,hmove,hm]
  | cons x xs =>
    simp only [openStep,List.isEmpty_cons,Bool.false_and,if_false] at H
    cases hp : (p (q,x)).bind id with
    | none => simp [hp] at H
    | some mv =>
      cases hm : mv.right <;> cases r with
      | nil =>
        cases cr with
        | false => simp [hp,hm] at H; all_goals try (subst b; simp [hstep,tail,hp,hmove,hm])
        | true =>
          have he := hr rfl; subst R
          simp [hp,hm] at H; subst b; simp [hstep,tail,hp,hmove,hm]
      | cons y ys => simp [hp,hm] at H; subst b; simp [hstep,tail,hp,hmove,hm]

def openRun (p : PartialMachine) (cl cr : Bool) : Nat → HZ → Option HZ
  | 0,z => some z
  | n+1,z => (openStep p cl cr z).bind (openRun p cl cr n)

theorem openRun_sound (p : PartialMachine) (cl cr : Bool) (n : Nat) (a b : HZ)
    (L R : List Bool) (hl : cl=true → L=[]) (hr : cr=true → R=[])
    (H : openRun p cl cr n a = some b) :
    hrun p n (tail a L R) = some (tail b L R) := by
  induction n generalizing a with
  | zero => simp [openRun] at H; subst b; rfl
  | succ n ih =>
    simp only [openRun] at H
    cases hs : openStep p cl cr a with
    | none => simp [hs] at H
    | some c =>
      have Hc := openStep_sound p cl cr a c L R hl hr hs
      simp only [hrun,Hc,Option.bind_some]
      exact ih c (by simpa [hs] using H)

def rep (w : List Bool) : Nat → List Bool
  | 0 => []
  | n+1 => w ++ rep w n
@[simp] theorem rep_nil (n : Nat) : rep [] n = [] := by induction n with
  | zero => rfl
  | succ n ih => simp [rep,ih]

theorem rep_intertwine (u w v : List Bool) (h : w++u=u++v) (n : Nat) :
    rep w n ++ u = u ++ rep v n := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep,List.append_assoc,ih,← List.append_assoc w u, h]

theorem rep_snoc (w : List Bool) (n : Nat) : rep w n ++ w = w ++ rep w n :=
  rep_intertwine w w w rfl n

theorem sweepR (p : PartialMachine) (q : Fin 6) (a b o v : List Bool) (c : Nat)
    (H : openRun p false false c ⟨q,o,a++b⟩ = some ⟨q,o++v,a⟩)
    (n : Nat) (L R : List Bool) :
    hrun p (c*n) ⟨q,o++L,a++rep b n++R⟩ = some ⟨q,o++rep v n++L,a++R⟩ := by
  induction n generalizing L with
  | zero => simp [rep,hrun]
  | succ n ih =>
    have H1 := openRun_sound p false false c _ _ L (rep b n++R) (by simp) (by simp) H
    have H2 := ih (v++L)
    simp only [tail,List.append_assoc] at H1 H2
    have H3 := hjoin H1 H2
    rw [Nat.mul_succ,Nat.add_comm]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep v n) v L,rep_snoc] using H3

theorem sweepL (p : PartialMachine) (q : Fin 6) (a b o v : List Bool) (c : Nat)
    (H : openRun p false false c ⟨q,a++b,o⟩ = some ⟨q,a,o++v⟩)
    (n : Nat) (L R : List Bool) :
    hrun p (c*n) ⟨q,a++rep b n++L,o++R⟩ = some ⟨q,a++L,o++rep v n++R⟩ := by
  induction n generalizing R with
  | zero => simp [rep,hrun]
  | succ n ih =>
    have H1 := openRun_sound p false false c _ _ (rep b n++L) R (by simp) (by simp) H
    have H2 := ih (v++R)
    simp only [tail,List.append_assoc] at H1 H2
    have H3 := hjoin H1 H2
    rw [Nat.mul_succ,Nat.add_comm]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep v n) v R,rep_snoc] using H3

structure Word where
  pre : List Bool
  block : List Bool
  post : List Bool
  deriving DecidableEq, Repr

def Word.eval (w : Word) (n : Nat) : List Bool := w.pre++rep w.block n++w.post
def Word.rest (w : Word) (n : Nat) : List Bool := rep w.block n++w.post
def Word.closed (w : Word) : Bool := w.block.isEmpty && w.post.isEmpty

theorem Word.closed_sound (w : Word) (n : Nat) (h : w.closed=true) : w.rest n=[] := by
  simp [Word.closed] at h
  simp [Word.rest,h.1,h.2]

def Word.eqForward (w v : Word) : Bool :=
  let u := v.pre.drop w.pre.length
  decide (v.pre = w.pre++u ∧ w.post = u++v.post ∧ w.block++u=u++v.block)

theorem Word.eqForward_sound (w v : Word) (h : w.eqForward v = true) (n : Nat) :
    w.eval n = v.eval n := by
  let u := v.pre.drop w.pre.length
  have H : v.pre = w.pre++u ∧ w.post = u++v.post ∧ w.block++u=u++v.block := of_decide_eq_true h
  simp only [Word.eval,H.1,H.2,List.append_assoc]
  rw [← List.append_assoc (rep w.block n) u,rep_intertwine u w.block v.block H.2.2]
  simp [List.append_assoc]

def Word.eqCheck (w v : Word) : Bool := w.eqForward v || v.eqForward w
theorem Word.eqCheck_sound (w v : Word) (h : w.eqCheck v = true) (n : Nat) :
    w.eval n = v.eval n := by
  have H : w.eqForward v = true ∨ v.eqForward w = true := by simpa [Word.eqCheck] using h
  rcases H with h|h
  · exact w.eqForward_sound v h n
  · exact (v.eqForward_sound w h n).symm

def Word.grow (w : Word) : Word := {w with post:=w.block++w.post}
theorem Word.grow_sound (w : Word) (n : Nat) : w.grow.eval n = w.eval (n+1) := by
  simp only [Word.grow,Word.eval,rep,List.append_assoc,← List.append_assoc (rep w.block n) w.block,rep_snoc]

structure Shape where
  q : Fin 6
  l : Word
  r : Word
  deriving DecidableEq, Repr

def Shape.eval (s : Shape) (n : Nat) : HZ := ⟨s.q,s.l.eval n,s.r.eval n⟩
def Shape.eqCheck (a b : Shape) : Bool := decide (a.q=b.q) && a.l.eqCheck b.l && a.r.eqCheck b.r
theorem Shape.eqCheck_sound (a b : Shape) (h : a.eqCheck b=true) (n : Nat) : a.eval n=b.eval n := by
  simp [Shape.eqCheck] at h
  simp [Shape.eval,h.1.1,a.l.eqCheck_sound b.l h.1.2 n,a.r.eqCheck_sound b.r h.2 n]

def Shape.grow (s : Shape) : Shape := ⟨s.q,s.l.grow,s.r.grow⟩
theorem Shape.grow_sound (s : Shape) (n : Nat) : s.grow.eval n=s.eval (n+1) := by
  simp [Shape.grow,Shape.eval,Word.grow_sound]

inductive Op where
  | step
  | rewrite (s : Shape)
  | right (k c : Nat) (v : List Bool)
  | left (k c : Nat) (v : List Bool)
  deriving Repr

def Op.apply (p : PartialMachine) (s : Shape) : Op → Option Shape
  | .step => (openStep p s.l.closed s.r.closed ⟨s.q,s.l.pre,s.r.pre⟩).map fun z =>
      ⟨z.q,{s.l with pre:=z.l},{s.r with pre:=z.r}⟩
  | .rewrite t => if s.eqCheck t then some t else none
  | .right k c v =>
      let o := s.l.pre.take k
      let a := s.r.pre
      let b := s.r.block
      if s.l.closed && decide (openRun p false false c ⟨s.q,o,a++b⟩=some ⟨s.q,o++v,a⟩) then
        some ⟨s.q,⟨o,v,s.l.pre.drop k⟩,⟨a++s.r.post,[],[]⟩⟩
      else none
  | .left k c v =>
      let o := s.r.pre.take k
      let a := s.l.pre
      let b := s.l.block
      if s.r.closed && decide (openRun p false false c ⟨s.q,a++b,o⟩=some ⟨s.q,a,o++v⟩) then
        some ⟨s.q,⟨a++s.l.post,[],[]⟩,⟨o,v,s.r.pre.drop k⟩⟩
      else none

def Op.lower : Op → Nat | .step => 1 | _ => 0

theorem Op.sound (p : PartialMachine) (s t : Shape) (op : Op) (h : op.apply p s=some t) (n : Nat) :
    ∃ c, op.lower≤c ∧ hrun p c (s.eval n)=some (t.eval n) := by
  cases op with
  | step =>
    cases hs : openStep p s.l.closed s.r.closed ⟨s.q,s.l.pre,s.r.pre⟩ with
    | none => simp [Op.apply,hs] at h
    | some z =>
      simp [Op.apply,hs] at h; subst t
      have H := openStep_sound p s.l.closed s.r.closed ⟨s.q,s.l.pre,s.r.pre⟩ z (s.l.rest n) (s.r.rest n)
        (s.l.closed_sound n) (s.r.closed_sound n) hs
      exact ⟨1,by decide,by simpa [hrun,Shape.eval,Word.eval,Word.rest,tail,List.append_assoc] using H⟩
  | rewrite t' =>
    by_cases H : s.eqCheck t'=true
    · simp [Op.apply,H] at h; subst t
      exact ⟨0,by simp [Op.lower],by rw [s.eqCheck_sound t' H n];rfl⟩
    · simp [Op.apply,H] at h
  | right k c v =>
    let o := s.l.pre.take k
    let a := s.r.pre
    let b := s.r.block
    by_cases H : s.l.closed=true ∧ openRun p false false c ⟨s.q,o,a++b⟩=some ⟨s.q,o++v,a⟩
    · have HH := H
      dsimp [o,a,b] at HH
      simp only [Op.apply,Bool.and_eq_true,decide_eq_true_eq,HH,and_self,ite_true,Option.some.injEq] at h
      subst t
      have Hr := sweepR p s.q a b o v c H.2 n (s.l.pre.drop k) s.r.post
      have Hl : s.l.eval n = s.l.pre := by
        have ht := s.l.closed_sound n H.1
        simpa [Word.eval,Word.rest,List.append_assoc] using congrArg (s.l.pre ++ ·) ht
      refine ⟨c*n,by simp [Op.lower],?_⟩
      simp only [Shape.eval,Hl]
      simpa [Word.eval,o,a,b,List.take_append_drop,List.append_assoc] using Hr
    · have HH := H
      dsimp [o,a,b] at HH
      simp [Op.apply,HH] at h
  | left k c v =>
    let o := s.r.pre.take k
    let a := s.l.pre
    let b := s.l.block
    by_cases H : s.r.closed=true ∧ openRun p false false c ⟨s.q,a++b,o⟩=some ⟨s.q,a,o++v⟩
    · have HH := H
      dsimp [o,a,b] at HH
      simp only [Op.apply,Bool.and_eq_true,decide_eq_true_eq,HH,and_self,ite_true,Option.some.injEq] at h
      subst t
      have Hr := sweepL p s.q a b o v c H.2 n s.l.post (s.r.pre.drop k)
      have Hl : s.r.eval n = s.r.pre := by
        have ht := s.r.closed_sound n H.1
        simpa [Word.eval,Word.rest,List.append_assoc] using congrArg (s.r.pre ++ ·) ht
      refine ⟨c*n,by simp [Op.lower],?_⟩
      simp only [Shape.eval,Hl]
      simpa [Word.eval,o,a,b,List.take_append_drop,List.append_assoc] using Hr
    · have HH := H
      dsimp [o,a,b] at HH
      simp [Op.apply,HH] at h

def runOps (p : PartialMachine) : List Op → Shape → Option Shape
  | [],s => some s
  | op::ops,s => (op.apply p s).bind (runOps p ops)
def lower (ops : List Op) : Nat := (ops.map Op.lower).sum

theorem runOps_sound (p : PartialMachine) (ops : List Op) (s t : Shape)
    (h : runOps p ops s=some t) (n : Nat) :
    ∃ c, lower ops≤c ∧ hrun p c (s.eval n)=some (t.eval n) := by
  induction ops generalizing s with
  | nil => simp [runOps] at h; subst t; exact ⟨0,by simp [lower],rfl⟩
  | cons op ops ih =>
    simp only [runOps] at h
    cases hs : op.apply p s with
    | none => simp [hs] at h
    | some u =>
      obtain ⟨c,hc,Hc⟩ := op.sound p s u hs n
      obtain ⟨d,hd,Hd⟩ := ih u (by simpa [hs] using h)
      exact ⟨c+d,by simp [lower] at *;omega,hjoin Hc Hd⟩

structure Certificate where
  entry : Nat
  shape : Shape
  ops : List Op
  deriving Repr

def Certificate.check (p : PartialMachine) (c : Certificate) : Bool :=
  decide (hrun p c.entry ⟨0,[],[]⟩=some (c.shape.eval 0)) &&
  decide (runOps p c.ops c.shape=some c.shape.grow) &&
  decide (0<lower c.ops)

theorem Certificate.arbitrary (p : PartialMachine) (c : Certificate) (h : c.check p=true) (n : Nat) :
    ∃ k, n≤k ∧ hrun p k ⟨0,[],[]⟩=some (c.shape.eval n) := by
  simp [Certificate.check] at h
  induction n with
  | zero => exact ⟨c.entry,by omega,h.1.1⟩
  | succ n ih =>
    obtain ⟨k,hk,Hk⟩ := ih
    obtain ⟨t,ht,Ht⟩ := runOps_sound p c.ops c.shape c.shape.grow h.1.2 n
    exact ⟨k+t,by omega,hjoin Hk (by simpa [Shape.grow_sound] using Ht)⟩

theorem blank_embed : embed (HZ.at ⟨0,[],[]⟩ 0) = blank := by
  unfold embed HZ.at blank
  congr 1
  funext x
  simp [atCell]

theorem Certificate.never (p : PartialMachine) (c : Certificate) (h : c.check p=true)
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

def bits (s : String) : List Bool := s.toList.map (· == '1')
def word (a b c : String) : Word := ⟨bits a,bits b,bits c⟩

#print axioms openRun_sound
#print axioms sweepR
#print axioms sweepL
#print axioms Certificate.arbitrary
#print axioms Certificate.never

end BB6Coverage.Agent50Pump
