import SweepPumping
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent4RunStack
open BB6Coverage BB6Coverage.Agent31Pump

-- Words are interpreted with infinitely many trailing zeros.
def cell : List Bool → Nat → Bool
  | [], _ => false
  | a::_, 0 => a
  | _::xs, n+1 => cell xs n

def WEq (a b : List Bool) : Prop := ∀ n, cell a n = cell b n

theorem WEq.refl (a : List Bool) : WEq a a := fun _ => rfl
theorem WEq.symm {a b} (h : WEq a b) : WEq b a := fun n => (h n).symm
theorem WEq.trans {a b c} (h : WEq a b) (g : WEq b c) : WEq a c := fun n => (h n).trans (g n)
theorem WEq.cons (v : Bool) {a b} (h : WEq a b) : WEq (v::a) (v::b) := by
  intro n; cases n with
  | zero => rfl
  | succ n => exact h n
theorem cell_head (a : List Bool) : cell a 0 = a.headD false := by cases a <;> rfl
theorem cell_tail (a : List Bool) (n : Nat) : cell a.tail n = cell a (n+1) := by cases a <;> rfl
theorem WEq.head {a b} (h : WEq a b) : a.headD false = b.headD false := by simpa only [cell_head] using h 0
theorem WEq.tail {a b} (h : WEq a b) : WEq a.tail b.tail := by
  intro n; simpa only [cell_tail] using h (n+1)

def trim : List Bool → List Bool
  | [] => []
  | b::bs => let t := trim bs; if b || !t.isEmpty then b::t else []

theorem trim_sound (w : List Bool) : WEq w (trim w) := by
  induction w with
  | nil => exact WEq.refl _
  | cons b bs ih =>
    cases hb : b with
    | true => simpa [trim,hb] using WEq.cons true ih
    | false =>
      cases ht : trim bs with
      | nil =>
        have h : WEq bs [] := by simpa [ht] using ih
        have h0 : WEq [false] [] := by intro n; cases n <;> rfl
        simpa [trim,hb,ht] using (WEq.cons false h).trans h0
      | cons x xs => simpa [trim,hb,ht] using WEq.cons false ih

theorem trim_eq {a b : List Bool} (h : trim a = trim b) : WEq a b :=
  (trim_sound a).trans (h ▸ (trim_sound b).symm)

structure ZEq (a b : Z0) : Prop where
  state : a.q = b.q
  left : WEq a.l b.l
  right : WEq a.r b.r

theorem ZEq.refl (a : Z0) : ZEq a a := ⟨rfl,WEq.refl _,WEq.refl _⟩
theorem ZEq.symm {a b} (h : ZEq a b) : ZEq b a := ⟨h.state.symm,h.left.symm,h.right.symm⟩
theorem ZEq.trans {a b c} (h : ZEq a b) (g : ZEq b c) : ZEq a c :=
  ⟨h.state.trans g.state,h.left.trans g.left,h.right.trans g.right⟩
theorem moveEq (mv : Move) {a b : Z0} (h : ZEq a b) : ZEq (move0 mv a) (move0 mv b) := by
  cases hd : mv.right with
  | false =>
    simp only [move0,hd,Bool.false_eq_true,ite_false]
    exact ⟨rfl,h.left.tail,WEq.cons _ h.right⟩
  | true =>
    simp only [move0,hd,ite_true]
    have hr := h.right.head
    exact ⟨rfl,by rw [hr]; exact WEq.cons _ (WEq.cons _ h.left.tail),h.right.tail⟩
theorem runEq (p : PartialMachine) (k : Nat) {a b c : Z0}
    (hab : ZEq a b) (h : run0 p k a = some c) :
    ∃ d, run0 p k b = some d ∧ ZEq c d := by
  induction k generalizing a b c with
  | zero =>
    simp [run0] at h
    subst c
    exact ⟨b,rfl,hab⟩
  | succ k ih =>
    have he : (p (a.q,a.l.headD false)).bind id = (p (b.q,b.l.headD false)).bind id := by
      rw [hab.state,hab.left.head]
    cases hm : (p (a.q,a.l.headD false)).bind id with
    | none => simp only [run0,step0,hm,Option.map_none,Option.bind_none] at h; cases h
    | some mv =>
      have hm' : (p (b.q,b.l.headD false)).bind id = some mv := he.symm.trans hm
      have h' : run0 p k (move0 mv a) = some c := by simpa only [run0,step0,hm,Option.map_some,Option.bind_some] using h
      obtain ⟨d,hd,hcd⟩ := ih (moveEq mv hab) h'
      exact ⟨d,by simpa only [run0,step0,hm',Option.map_some,Option.bind_some] using hd,hcd⟩

-- A frame can be read at its empty end only when that end is known blank.
def safe (o : Bool) (w : List Bool) : Bool := !o || !w.isEmpty

def fstep (p : PartialMachine) (ol or : Bool) (z : Z0) : Option Z0 :=
  if safe ol z.l then
    match (p (z.q,z.l.headD false)).bind id with
    | none => none
    | some mv => if mv.right && !safe or z.r then none else some (move0 mv z)
  else none

def frun (p : PartialMachine) (ol or : Bool) : Nat → Z0 → Option Z0
  | 0,z => some z
  | n+1,z => (fstep p ol or z).bind (frun p ol or n)

def extend (z : Z0) (l r : List Bool) : Z0 := ⟨z.q,z.l++l,z.r++r⟩

theorem safe_head {o : Bool} {w t : List Bool} (hs : safe o w = true)
    (ht : o = false → t = []) : (w++t).headD false = w.headD false := by
  cases w with
  | nil => cases o <;> simp_all [safe]
  | cons b w => rfl

theorem safe_tail {o : Bool} {w t : List Bool} (hs : safe o w = true)
    (ht : o = false → t = []) : (w++t).tail = w.tail++t := by
  cases w with
  | nil => cases o <;> simp_all [safe]
  | cons b w => rfl

theorem fstep_sound {p ol or a b} (h : fstep p ol or a = some b)
    (l r : List Bool) (hl : ol = false → l = []) (hr : or = false → r = []) :
    step0 p (extend a l r) = some (extend b l r) := by
  unfold fstep at h
  split at h
  next hs =>
    have hhead := safe_head hs hl
    have htail := safe_tail hs hl
    split at h
    next he => simp at h
    next mv hm =>
      split at h
      next hb => simp at h
      next hb =>
        have eq : move0 mv a = b := Option.some.inj h
        subst b
        simp only [step0,extend,hhead,hm,Option.map_some]
        congr 1
        cases hd : mv.right with
        | false => simp [move0,extend,hd,htail]
        | true =>
          have hs' : safe or a.r = true := by cases hsr : safe or a.r <;> simp_all
          have hhead' := safe_head hs' hr
          have htail' := safe_tail hs' hr
          simp only [move0,hd,ite_true,htail,hhead',htail',List.cons_append]
  next hs => simp at h

theorem frun_sound {p ol or k a b} (h : frun p ol or k a = some b)
    (l r : List Bool) (hl : ol = false → l = []) (hr : or = false → r = []) :
    run0 p k (extend a l r) = some (extend b l r) := by
  induction k generalizing a with
  | zero => have e := Option.some.inj h; subst b; rfl
  | succ k ih =>
    cases hs : fstep p ol or a with
    | none => simp [frun,hs] at h
    | some t =>
      have h' : frun p ol or k t = some b := by simpa [frun,hs] using h
      rw [run0,fstep_sound hs l r hl hr]; exact ih h'

-- Run words with arbitrary unconsumed run tails.
def enc (block : Nat → List Bool) : List Nat → List Bool
  | [] => []
  | a::xs => block a ++ enc block xs

theorem enc_append (block : Nat → List Bool) (a b : List Nat) :
    enc block (a++b) = enc block a ++ enc block b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [enc,ih,List.append_assoc]

def lb (a : Nat) : List Bool := List.replicate a true ++ [false]
def rb (a : Nat) : List Bool := List.replicate (a/256) false ++ List.replicate (a%256) true

def left (xs : List Nat) : List Bool := [false,false] ++ enc lb xs
def right (xs : List Nat) : List Bool := enc rb xs

def sec (l r : List Nat) : Z0 := ⟨0,left l,right r⟩

-- Compare open words exactly and closed words modulo trailing zeros.
def eqWord (o : Bool) (a b : List Bool) : Bool := if o then a == b else trim a == trim b

theorem eqWord_sound {o a b} (h : eqWord o a b = true) (t : List Bool)
    (ht : o = false → t = []) : WEq (a++t) (b++t) := by
  cases o with
  | false =>
    have he : trim a = trim b := by simpa [eqWord] using h
    simpa [ht rfl] using trim_eq he
  | true =>
    have he : a = b := by simpa [eqWord] using h
    subst b; exact WEq.refl _

structure Rule where
  lp : List Nat
  rp : List Nat
  lo : List Nat
  ro : List Nat
  cost : Nat
  deriving Repr

def Rule.check (p : PartialMachine) (w : Rule) : Bool :=
  0 < w.cost && match frun p (w.lp.length == 2) (w.rp.length == 3) w.cost (sec w.lp w.rp) with
  | none => false
  | some z => z.q == 0 && eqWord (w.lp.length == 2) z.l (left w.lo) && eqWord (w.rp.length == 3) z.r (right w.ro)

theorem Rule.sound {p : PartialMachine} {w : Rule} (h : w.check p = true) (l r : List Nat)
    (hl : (w.lp.length == 2) = false → l = []) (hr : (w.rp.length == 3) = false → r = []) :
    ∃ z, 0 < w.cost ∧ run0 p w.cost (sec (w.lp++l) (w.rp++r)) = some z ∧ ZEq z (sec (w.lo++l) (w.ro++r)) := by
  simp only [Rule.check,Bool.and_eq_true,decide_eq_true_eq] at h
  cases he : frun p (w.lp.length == 2) (w.rp.length == 3) w.cost (sec w.lp w.rp) with
  | none => simp [he] at h
  | some z =>
    simp only [he,Bool.and_eq_true,beq_iff_eq] at h
    have hL : (w.lp.length == 2) = false → enc lb l = [] := by intro hf; rw [hl hf]; rfl
    have hR : (w.rp.length == 3) = false → enc rb r = [] := by intro hf; rw [hr hf]; rfl
    have hs := frun_sound he (enc lb l) (enc rb r) hL hR
    refine ⟨extend z (enc lb l) (enc rb r),h.1,?_,?_⟩
    · simpa only [extend,sec,left,right,enc_append,List.append_assoc] using hs
    · exact ⟨h.2.1.1,by simpa only [extend,sec,left,enc_append,List.append_assoc] using eqWord_sound h.2.1.2 (enc lb l) hL,
        by simpa only [extend,sec,right,enc_append] using eqWord_sound h.2.2 (enc rb r) hR⟩

structure Stack where
  rev : Nat → List (Nat × Nat)
  fwd : Nat → List (Nat × Nat)

def Stack.pop (s : Stack) (i : Nat) := s.rev i
inductive Stack.Tape (s : Stack) : List Nat → Nat → Prop
  | nil : Tape s [] 0
  | cons {x xs i j} : j ≠ 0 → (x,i) ∈ s.pop j → Tape s xs i → Tape s (x::xs) j

def Stack.pops (s : Stack) : Nat → Nat → List (List Nat × Nat)
  | 0,i => [([],i)]
  | k+1,i => if i == 0 then [([],0)] else
      (s.pop i).flatMap fun (x,j) => (s.pops k j).map fun (xs,t) => (x::xs,t)

theorem Stack.pops_complete {s : Stack} {xs i} (h : s.Tape xs i) (k : Nat) :
    ∃ pre tail t, xs = pre++tail ∧ s.Tape tail t ∧ (pre,t) ∈ s.pops k i ∧ (pre.length ≠ k → tail = []) := by
  induction k generalizing xs i with
  | zero => exact ⟨[],xs,i,rfl,h,by simp [Stack.pops],by simp⟩
  | succ k ih =>
    cases h with
    | nil => exact ⟨[],[],0,rfl,.nil,by simp [Stack.pops],fun _ => rfl⟩
    | @cons x xs i j hj he ht =>
      obtain ⟨pre,tail,t,heq,htail,hm,hend⟩ := ih ht
      refine ⟨x::pre,tail,t,by simp [heq],htail,?_,?_⟩
      · simp only [Stack.pops,beq_iff_eq,if_neg hj,List.mem_flatMap,List.mem_map]
        exact ⟨(x,i),he,(pre,t),hm,rfl⟩
      · intro hne
        apply hend
        simpa using hne

def Stack.push (s : Stack) (i x : Nat) : List Nat :=
  (s.fwd i).filterMap fun (y,j) =>
    if y == x && j != 0 && (s.pop j).contains (x,i) then some j else none

theorem Stack.push_sound {s : Stack} {xs i x j} (h : s.Tape xs i) (hj : j ∈ s.push i x) : s.Tape (x::xs) j := by
  unfold Stack.push at hj
  obtain ⟨⟨y,t⟩,_,he⟩ := List.mem_filterMap.mp hj
  change (if y == x && t != 0 && (s.pop t).contains (x,i) then some t else none) = some j at he
  split at he
  next hc =>
    have heq : t = j := Option.some.inj he
    subst t
    simp only [Bool.and_eq_true,beq_iff_eq,bne_iff_ne,List.contains_iff_mem] at hc
    exact .cons hc.1.2 hc.2 h
  next hc => simp at he

def Stack.pushes (s : Stack) : List Nat → Nat → List Nat
  | [],i => [i]
  | x::xs,i => (s.pushes xs i).flatMap fun j => s.push j x

theorem Stack.pushes_sound {s : Stack} {tail i} (h : s.Tape tail i) (pre : List Nat) {j} (hj : j ∈ s.pushes pre i) : s.Tape (pre++tail) j := by
  induction pre generalizing j with
  | nil => simp [Stack.pushes] at hj; subst j; exact h
  | cons x xs ih =>
    obtain ⟨t,ht,hj'⟩ := List.mem_flatMap.mp hj
    exact Stack.push_sound (ih ht) hj'

structure Cert where
  L : Stack
  R : Stack
  size : Nat
  rows : Nat → List (Nat × Rule)

def Cert.row (c : Cert) (i : Nat) : List (Nat × Rule) := if i < c.size then c.rows i else []
def Cert.allowed (c : Cert) (i j : Nat) : Bool := (c.row i).any fun x => x.1 == j

theorem Cert.allowed_sound {c : Cert} {i j} (h : c.allowed i j = true) : ∃ w, (j,w) ∈ c.row i := by
  obtain ⟨⟨t,w⟩,hm,he⟩ := List.any_eq_true.mp h
  have heq : t = j := by simpa using he
  subst t; exact ⟨w,hm⟩

def Cert.checkPair (c : Cert) (w : Rule) (l r : List Nat × Nat) : Bool :=
  l.1 == w.lp && r.1 == w.rp &&
  (c.L.pushes w.lo l.2).any fun i => (c.R.pushes w.ro r.2).any fun j => c.allowed i j

def Cert.checkSec (p : PartialMachine) (c : Cert) (i j : Nat) (w : Rule) : Bool :=
  w.check p && (c.L.pops 2 i).all fun l => (c.R.pops 3 j).all fun r => c.checkPair w l r

def Cert.checkRow (p : PartialMachine) (c : Cert) (i : Nat) : Bool :=
  (c.row i).all fun (j,w) => c.checkSec p i j w

def Cert.check (p : PartialMachine) (c : Cert) : Bool :=
  (List.range c.size).all (c.checkRow p)

theorem Cert.row_bound {c : Cert} {i j w} (h : (j,w) ∈ c.row i) : i < c.size := by
  by_cases hn : i < c.size
  · exact hn
  · simp [Cert.row,hn] at h

theorem Cert.checked {p : PartialMachine} {c : Cert} (h : c.check p = true) {i j w} (hm : (j,w) ∈ c.row i) : c.checkSec p i j w = true := by
  have hr := List.all_eq_true.mp h i (List.mem_range.mpr (Cert.row_bound hm))
  exact List.all_eq_true.mp hr (j,w) hm

def Cert.Inv (c : Cert) (z : Z0) : Prop :=
  ∃ l r i j w, c.L.Tape l i ∧ c.R.Tape r j ∧ (j,w) ∈ c.row i ∧ ZEq z (sec l r)

theorem Cert.closed {p : PartialMachine} {c : Cert} (hc : c.check p = true) {z : Z0} (hz : c.Inv z) :
    ∃ k z', 0 < k ∧ run0 p k z = some z' ∧ c.Inv z' := by
  obtain ⟨l,r,i,j,w,hl,hr,hm,he⟩ := hz
  have h := Cert.checked hc hm
  simp only [Cert.checkSec,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨lp,lt,li,hel,hlt,hml,hlend⟩ := Stack.pops_complete hl 2
  obtain ⟨rp,rt,ri,her,hrt,hmr,hrend⟩ := Stack.pops_complete hr 3
  have hp := h.2 (lp,li) hml (rp,ri) hmr
  simp only [Cert.checkPair,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at hp
  obtain ⟨⟨hlp,hrp⟩,i',hi',j',hj',ha⟩ := hp
  subst lp; subst rp; subst l; subst r
  have hL : (w.lp.length == 2) = false → lt = [] := by
    intro hf; apply hlend; simpa using hf
  have hR : (w.rp.length == 3) = false → rt = [] := by
    intro hf; apply hrend; simpa using hf
  obtain ⟨t,hk,ht,hte⟩ := Rule.sound h.1 lt rt hL hR
  obtain ⟨z',hz',he'⟩ := runEq p w.cost he.symm ht
  obtain ⟨w',hw'⟩ := Cert.allowed_sound ha
  exact ⟨w.cost,z',hk,hz',w.lo++lt,w.ro++rt,i',j',w',Stack.pushes_sound hlt _ hi',Stack.pushes_sound hrt _ hj',hw',he'.symm.trans hte⟩

theorem Cert.entryInv {c : Cert} {z : Z0} (h : ZEq z (sec [1] [259]))
    (hs : (c.L.pushes [1] 0).any (fun i => (c.R.pushes [259] 0).any fun j => c.allowed i j) = true) : c.Inv z := by
  obtain ⟨i,hi,j,hj,hij⟩ := by simpa only [List.any_eq_true] using hs
  obtain ⟨w,hw⟩ := Cert.allowed_sound hij
  exact ⟨[1],[259],i,j,w,Stack.pushes_sound .nil [1] hi,Stack.pushes_sound .nil [259] hj,hw,h⟩

theorem Cert.live {p : PartialMachine} {c : Cert} (hc : c.check p = true) {entry : Nat} {z : Z0}
    (he : run0 p entry ⟨0,[],[]⟩ = some z) (hi : c.Inv z) (k : Nat) :
    ∃ t u, k ≤ t ∧ run0 p t ⟨0,[],[]⟩ = some u ∧ c.Inv u := by
  induction k with
  | zero => exact ⟨entry,z,by omega,he,hi⟩
  | succ k ih =>
    obtain ⟨t,u,ht,hu,hi'⟩ := ih
    obtain ⟨v,w,hv,hw,hwi⟩ := Cert.closed hc hi'
    exact ⟨t+v,w,by omega,join0 hu hw,hwi⟩

#print axioms Cert.live

open BB6Coverage.Agent50Zipper

theorem Cert.never {p : PartialMachine} {c : Cert} (hc : c.check p = true) {entry : Nat} {z : Z0}
    (he : run0 p entry ⟨0,[],[]⟩ = some z) (hi : c.Inv z)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro k
  obtain ⟨t,u,ht,hr,_⟩ := Cert.live hc he hi k
  have hz : (zrun p t start).map project = some u := (run_project p t start).trans hr
  cases h : zrun p t start with
  | none => simp [h] at hz
  | some zz =>
    have H := zrun_sound p m hm t start zz h
    rw [start_embed] at H
    rw [show t=k+(t-k) by omega,run_append] at H
    cases he : run m k blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms Cert.never
end BB6.Agent4RunStack
