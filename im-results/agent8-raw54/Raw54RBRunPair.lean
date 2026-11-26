import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RBRunPair
open BB6Coverage BB6Coverage.Agent31Pump Agent50Zipper

def table (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => if v then some (some ⟨true,false,3⟩) else some (some ⟨false,false,2⟩)
  | _,_ => none

def O : List Bool := [true]
def Z : List Bool := [false]
def blk (k : Nat) : List Bool := false::rep O (k+1)
def stack : List Nat → List Bool
  | [] => blk 2
  | k::s => blk k ++ stack s
def out : List Nat → List Bool
  | [] => [true,true]
  | k::s => out s ++ rep Z k ++ [true,true]
def sec (w : List Bool) : Z0 := ⟨4,[],rep Z 5 ++ w⟩
def scan (s : List Nat) (w : List Bool) : Z0 := ⟨4,blk 0 ++ stack s,false::w⟩

theorem rep_add (P : List Bool) (a b : Nat) : rep P (a+b) = rep P a ++ rep P b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; simp only [rep,ih,List.append_assoc]

theorem swap (v : Bool) (l r : List Bool) (t : Nat) :
    run0 (table v) (t+1) ⟨0,false::l,r⟩ = run0 (table v) (t+1) ⟨4,false::l,r⟩ := by cases v <;> rfl

theorem drainRaw (v : Bool) (k : Nat) (L R : List Bool) :
    run0 (table v) (k+8) ⟨4,blk k ++ L,false::false::false::R⟩ =
      some ⟨4,L,rep Z (k+3) ++ true::true::R⟩ := by
  have a : run0 (table v) 6 ⟨4,blk k ++ L,false::false::false::R⟩ =
      some ⟨4,rep O (k+2) ++ L,false::true::true::R⟩ := by cases v <;> rfl
  have b := sweepL (table v) 4 [] [] O Z 1 (by intro L R; cases v <;> rfl) (k+2) L (false::true::true::R)
  simp only [List.nil_append,Nat.one_mul] at b
  have H := join0 a b
  rw [show 6+(k+2)=k+8 by omega] at H
  simpa only [rep_add Z (k+2) 1,List.append_assoc,show rep Z 1 = [false] by rfl,List.cons_append,List.nil_append] using H

theorem drainBlank (v : Bool) (k : Nat) (L : List Bool) :
    run0 (table v) (k+8) ⟨0,blk k ++ L,[]⟩ = some ⟨4,L,rep Z (k+3) ++ [true,true]⟩ := by
  have a : run0 (table v) 6 ⟨0,blk k ++ L,[]⟩ =
      some ⟨4,rep O (k+2) ++ L,[false,true,true]⟩ := by cases v <;> rfl
  have b : run0 (table v) 6 ⟨4,blk k ++ L,[false,false,false]⟩ =
      some ⟨4,rep O (k+2) ++ L,[false,true,true]⟩ := by cases v <;> rfl
  have H := drainRaw v k L []
  rw [show k+8=6+(k+2) by omega,run0_add,b] at H
  rw [show k+8=6+(k+2) by omega,run0_add,a]
  exact H

theorem drain (v : Bool) (s : List Nat) (R : List Bool) :
    ∃ t, 0<t ∧ run0 (table v) t ⟨4,stack s,false::false::false::R⟩ = some (sec (out s ++ R)) := by
  induction s generalizing R with
  | nil => exact ⟨10,by omega,drainRaw v 2 [] R⟩
  | cons k s ih =>
    have a := drainRaw v k (stack s) R
    rw [show k+3=3+k by omega,rep_add Z 3 k] at a
    obtain ⟨t,ht,b⟩ := ih (rep Z k ++ true::true::R)
    refine ⟨k+8+t,by omega,?_⟩
    have H := join0 a b
    simpa only [stack,out,List.append_assoc,List.cons_append,List.nil_append] using H

theorem extend (v : Bool) (k : Nat) (L R : List Bool) :
    run0 (table v) (if v then 9 else 11) ⟨4,blk k ++ L,false::true::true::true::R⟩ =
      some ⟨4,blk (k+1) ++ L,false::true::true::R⟩ := by cases v <;> rfl

theorem push1 (v : Bool) (k : Nat) (L R : List Bool) :
    run0 (table v) (if v then 11 else 13) ⟨4,blk k ++ L,false::true::true::false::true::true::R⟩ =
      some ⟨4,blk 0 ++ blk (k+1) ++ L,false::true::true::R⟩ := by cases v <;> rfl

theorem push3 (v : Bool) (k : Nat) (L R : List Bool) :
    run0 (table v) 7 ⟨4,blk k ++ L,false::true::true::false::false::false::R⟩ =
      some ⟨0,blk 0 ++ blk 0 ++ blk (k+1) ++ L,false::R⟩ := by cases v <;> rfl

theorem pushEnd (v : Bool) (k : Nat) (L : List Bool) :
    run0 (table v) 7 ⟨4,blk k ++ L,[false,true,true]⟩ =
      some ⟨0,blk 0 ++ blk 0 ++ blk (k+1) ++ L,[]⟩ := by cases v <;> rfl

theorem scanOnes (v : Bool) (a k : Nat) (L R : List Bool) :
    run0 (table v) (a * (if v then 9 else 11)) ⟨4,blk k ++ L,false::true::true::(rep O a ++ R)⟩ =
      some ⟨4,blk (k+a) ++ L,false::true::true::R⟩ := by
  induction a generalizing k with
  | zero => simp [run0,rep]
  | succ a ih =>
    have h := extend v k L (rep O a ++ R)
    have H := join0 h (ih (k+1))
    rw [show k+1+a=k+(a+1) by omega] at H
    cases v <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.succ_mul] at * <;>
      simpa only [rep,O,List.cons_append,List.nil_append,Nat.add_comm] using H
#print axioms drain
#print axioms scanOnes

abbrev Tok := Nat × Nat -- actual one-run length is first component + 2

def encTok (x : Tok) : List Bool := rep O (x.1+2) ++ rep Z x.2

def enc : List Tok → List Bool
  | [] => []
  | x::xs => encTok x ++ enc xs

def trans (p : Nat) : List Tok → List Tok
  | [] => []
  | (a,g)::xs => (p,a+1)::
    (if g=0 then [(4,0)] else if g=1 then trans 0 xs else if g=3 then trans 2 xs
     else if g=5 then match xs with | [] => [] | (b,h)::ys => (b+6,h)::ys
     else (4,g-5)::xs)

inductive Shape : List Tok → Prop
  | last (a : Nat) : Shape [(a,0)]
  | more (a g : Nat) (xs : List Tok) : (g=1 ∨ g=3 ∨ 5≤g) → Shape xs → Shape ((a,g)::xs)

theorem enc_head (a g : Nat) (xs : List Tok) : enc ((a,g)::xs) = true::true::(rep O a ++ rep Z g ++ enc xs) := by
  rw [enc,encTok,show a+2=2+a by omega,rep_add O 2 a]
  rfl

theorem scanHead (v : Bool) (s : List Nat) (a g : Nat) (xs : List Tok) :
    run0 (table v) (a*(if v then 9 else 11)) (scan s (enc ((a,g)::xs))) =
      some ⟨4,blk a ++ stack s,false::true::true::(rep Z g ++ enc xs)⟩ := by
  rw [enc_head]
  simpa only [scan,Nat.zero_add,List.append_assoc] using scanOnes v a 0 (stack s) (rep Z g ++ enc xs)

theorem scan1 (v : Bool) (s : List Nat) (a b h : Nat) (ys : List Tok) :
    run0 (table v) (if v then 11 else 13)
      ⟨4,blk a ++ stack s,false::true::true::(rep Z 1 ++ enc ((b,h)::ys))⟩ =
        some (scan ((a+1)::s) (enc ((b,h)::ys))) := by
  rw [enc_head]
  simpa only [scan,stack,List.append_assoc,show rep Z 1 = [false] by rfl,List.cons_append,List.nil_append] using push1 v a (stack s) (rep O b ++ rep Z h ++ enc ys)

theorem scan3 (v : Bool) (s : List Nat) (a : Nat) (xs : List Tok) :
    run0 (table v) 7 ⟨4,blk a ++ stack s,false::true::true::(rep Z 3 ++ enc xs)⟩ =
      some ⟨0,blk 0 ++ stack (0::(a+1)::s),false::enc xs⟩ := by
  simpa only [stack,List.append_assoc,show rep Z 3 = [false,false,false] by rfl,List.cons_append,List.nil_append] using push3 v a (stack s) (enc xs)

theorem positiveSwap (v : Bool) (s : List Nat) (w : List Bool) (t : Nat) (ht : 0<t) :
    run0 (table v) t ⟨0,blk 0 ++ stack s,false::w⟩ = run0 (table v) t (scan s w) := by
  cases t with
  | zero => omega
  | succ t => exact swap v _ _ t

theorem stop (v : Bool) (s : List Nat) (a j : Nat) (xs : List Tok) :
    ∃ t, 0<t ∧ run0 (table v) t ⟨4,blk a ++ stack s,false::true::true::(rep Z (j+5) ++ enc xs)⟩ =
      some (sec (out (0::0::(a+1)::s) ++ rep Z j ++ enc xs)) := by
  have a₁ := push3 v a (stack s) (rep Z (j+2) ++ enc xs)
  rw [show j+5=3+(j+2) by omega,rep_add Z 3 (j+2)]
  obtain ⟨t,ht,b⟩ := drain v (0::0::(a+1)::s) (rep Z j ++ enc xs)
  have c : run0 (table v) t ⟨0,blk 0 ++ blk 0 ++ blk (a+1) ++ stack s,false::(rep Z (j+2) ++ enc xs)⟩ =
      some (sec (out (0::0::(a+1)::s) ++ rep Z j ++ enc xs)) := by
    cases t with
    | zero => omega
    | succ t =>
      rw [show rep Z (j+2) = false::false::rep Z j by rfl]
      change run0 (table v) (t+1) ⟨0,false::_,_⟩ = _
      rw [swap v]
      change run0 (table v) (t+1) ⟨4,blk 0 ++ blk 0 ++ blk (a+1) ++ stack s,false::false::false::(rep Z j ++ enc xs)⟩ = _
      simpa only [stack,List.append_assoc] using b
  refine ⟨7+t,by omega,?_⟩
  simpa only [rep, Z,List.cons_append,List.nil_append,List.append_assoc] using join0 a₁ c

theorem stopEnd (v : Bool) (s : List Nat) (a : Nat) :
    ∃ t, 0<t ∧ run0 (table v) t ⟨4,blk a ++ stack s,[false,true,true]⟩ =
      some (sec (out (0::0::(a+1)::s))) := by
  have a₁ := pushEnd v a (stack s)
  have b := drainBlank v 0 (blk 0 ++ blk (a+1) ++ stack s)
  obtain ⟨t,ht,c⟩ := drain v (0::(a+1)::s) [true,true]
  refine ⟨7+8+t,by omega,?_⟩
  simpa only [stack,out,rep,List.append_nil,List.append_assoc] using join0 (join0 a₁ b) c

theorem out1 (s : List Nat) (a p : Nat) (pre : List Bool) (h : out s = pre ++ rep O (p+2)) :
    out ((a+1)::s) = (pre ++ encTok (p,a+1)) ++ rep O (0+2) := by
  simp only [out,h,encTok,List.append_assoc]
  rfl

theorem out3 (s : List Nat) (a p : Nat) (pre : List Bool) (h : out s = pre ++ rep O (p+2)) :
    out (0::(a+1)::s) = (pre ++ encTok (p,a+1)) ++ rep O (2+2) := by
  simp only [out,h,encTok,rep,List.append_nil,List.append_assoc,List.cons_append,List.nil_append]
  rfl

theorem out5 (s : List Nat) (a p : Nat) (pre : List Bool) (h : out s = pre ++ rep O (p+2)) :
    out (0::0::(a+1)::s) = (pre ++ encTok (p,a+1)) ++ rep O (4+2) := by
  simp only [out,h,encTok,rep,List.append_nil,List.append_assoc,List.cons_append,List.nil_append]
  rfl

theorem encMerge (b h : Nat) (ys : List Tok) : rep O 6 ++ enc ((b,h)::ys) = enc ((b+6,h)::ys) := by
  simp only [enc,encTok,List.append_assoc]
  rw [show b+6+2=6+(b+2) by omega,rep_add O 6 (b+2),List.append_assoc]


theorem scanAll (v : Bool) (w : List Tok) (hw : Shape w) (s : List Nat) (p : Nat) (pre : List Bool)
    (h : out s = pre ++ rep O (p+2)) :
    ∃ t, 0<t ∧ run0 (table v) t (scan s (enc w)) = some (sec (pre ++ enc (trans p w))) := by
  induction hw generalizing s p pre with
  | last a =>
    have A := scanHead v s a 0 []
    obtain ⟨t,ht,B⟩ := stopEnd v s a
    refine ⟨a*(if v then 9 else 11)+t,by omega,?_⟩
    have H := join0 A B
    rw [out5 s a p pre h] at H
    simpa only [trans,ite_eq_left rfl,ite_true,ite_false,enc,encTok,rep,List.append_nil,List.nil_append,List.append_assoc] using H
  | more a g xs hg hw ih =>
    have A := scanHead v s a g xs
    rcases hg with hg|hg|hg
    · subst g
      cases xs with
      | nil => cases hw
      | cons x ys =>
        rcases x with ⟨b,hb⟩
        have B := scan1 v s a b hb ys
        obtain ⟨t,ht,C⟩ := ih ((a+1)::s) 0 (pre ++ encTok (p,a+1)) (out1 s a p pre h)
        refine ⟨a*(if v then 9 else 11)+(if v then 11 else 13)+t,by omega,?_⟩
        simpa only [trans,show (1:Nat) ≠ 0 by decide,ite_eq_right,ite_eq_left rfl,ite_true,ite_false,enc,List.append_assoc] using join0 (join0 A B) C
    · subst g
      have B := scan3 v s a xs
      obtain ⟨t,ht,C⟩ := ih (0::(a+1)::s) 2 (pre ++ encTok (p,a+1)) (out3 s a p pre h)
      rw [← positiveSwap v _ _ _ ht] at C
      refine ⟨a*(if v then 9 else 11)+7+t,by omega,?_⟩
      simpa only [trans,show (3:Nat) ≠ 0 by decide,show (3:Nat) ≠ 1 by decide,ite_eq_right,ite_eq_left rfl,ite_true,ite_false,enc,List.append_assoc] using join0 (join0 A B) C
    · cases xs with
      | nil => cases hw
      | cons x ys =>
        rcases x with ⟨b,hb⟩
        let j := g-5
        have hg' : g=j+5 := by dsimp [j]; omega
        obtain ⟨t,ht,B⟩ := stop v s a j ((b,hb)::ys)
        rw [← hg'] at B
        have H := join0 A B
        rw [out5 s a p pre h] at H
        refine ⟨a*(if v then 9 else 11)+t,by omega,?_⟩
        by_cases h5 : g=5
        · have hj : j=0 := by simp [j,h5]
          rw [hj] at H
          simp only [show rep Z 0 = [] by rfl,List.append_nil] at H
          rw [List.append_assoc,encMerge] at H
          simpa only [trans,h5,show (5:Nat) ≠ 0 by decide,show (5:Nat) ≠ 1 by decide,show (5:Nat) ≠ 3 by decide,ite_eq_right,ite_eq_left rfl,ite_true,ite_false,enc,List.append_assoc] using H
        · have h0 : g≠0 := by omega
          have h1 : g≠1 := by omega
          have h3 : g≠3 := by omega
          simpa only [trans,h0,h1,h3,h5,ite_eq_right,ite_true,ite_false,enc,encTok,List.append_assoc,j] using H

theorem sectionReturn (v : Bool) (w : List Tok) (hw : Shape w) :
    ∃ t, 0<t ∧ run0 (table v) t (sec (enc w)) = some (sec (enc (trans 0 w))) := by
  have A : run0 (table v) 16 (sec (enc w)) = some ⟨0,blk 0 ++ stack [],false::enc w⟩ := by cases v <;> rfl
  obtain ⟨t,ht,B⟩ := scanAll v w hw [] 0 [] (by rfl)
  rw [← positiveSwap v _ _ _ ht] at B
  exact ⟨16+t,by omega,join0 A B⟩

#print axioms sectionReturn

inductive Mode where
  | scan (p : Nat)
  | merge
  | copy
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def emit (m : Mode) (x : Tok) : Mode × List Tok :=
  match m with
  | .copy => (.copy,[x])
  | .merge => (.copy,[(x.1+6,x.2)])
  | .scan p =>
    let (a,g) := x
    if g=0 then (.copy,[(p,a+1),(4,0)])
    else if g=1 then (.scan 0,[(p,a+1)])
    else if g=3 then (.scan 2,[(p,a+1)])
    else if g=5 then (.merge,[(p,a+1)])
    else (.copy,[(p,a+1),(4,g-5)])

def stream (m : Mode) : List Tok → List Tok
  | [] => []
  | x::xs => (emit m x).2 ++ stream (emit m x).1 xs

theorem copy_stream (xs : List Tok) : stream .copy xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [stream,emit,ih]

theorem merge_stream (xs : List Tok) : stream .merge xs = (match xs with | [] => [] | (b,h)::ys => (b+6,h)::ys) := by
  cases xs with
  | nil => rfl
  | cons x xs => rcases x with ⟨b,h⟩; simp [stream,emit,copy_stream]

theorem stream_trans (w : List Tok) (p : Nat) (hw : Shape w) : stream (.scan p) w = trans p w := by
  induction hw generalizing p with
  | last a => simp [stream,emit,trans]
  | more a g xs hg hw ih =>
    have h0 : g≠0 := by omega
    by_cases h1 : g=1
    · subst g; simp [stream,emit,trans,ih]
    by_cases h3 : g=3
    · subst g; simp [stream,emit,trans,ih]
    by_cases h5 : g=5
    · subst g; simp [stream,emit,trans,merge_stream]
    · simp [stream,emit,trans,h0,h1,h3,h5,copy_stream]

abbrev Q := Option Tok
abbrev Product := Q × Q × Mode

def edges : Q → List Tok
  | none => [(0,1),(0,3),(2,0)]
  | some (0,3) => [(4,6),(10,0),(10,1),(4,0)]
  | some (0,1) => [(10,1),(0,1),(10,0),(0,3),(2,5),(4,6),(2,11),(0,5),(0,11)]
  | some (2,5) | some (0,5) => [(4,1),(4,0)]
  | some (2,11) | some (4,6) | some (4,1) | some (10,1) | some (0,11) => [(0,5),(0,1),(4,0)]
  | _ => []

def final : Q → Bool
  | some (2,0) | some (4,0) | some (10,0) => true
  | _ => false

def legal (q : Q) : List Tok → Prop
  | [] => final q = true
  | x::xs => x ∈ edges q ∧ legal (some x) xs

def walk (q : Q) : List Tok → Option Q
  | [] => some q
  | x::xs => if (edges q).contains x then walk (some x) xs else none

theorem walk_legal (q r : Q) (xs ys : List Tok) (h : walk q xs = some r) (hy : legal r ys) : legal q (xs ++ ys) := by
  induction xs generalizing q with
  | nil => simp [walk] at h; subst r; exact hy
  | cons x xs ih =>
    simp only [walk] at h
    split at h
    · rename_i hx
      exact ⟨List.contains_iff_mem.mp hx,ih (some x) h⟩
    · contradiction

-- Explicit finite product certificate: input state, output state, transducer mode.
def reach : List Product := [
  (some (10,0),some (10,0),.copy),
  (some (10,0),some (4,0),.copy),
  (some (10,1),some (10,1),.copy),
  (some (10,1),some (0,11),.scan 0),
  (some (10,1),some (2,11),.scan 0),
  (some (0,1),some (0,1),.copy),
  (some (0,1),some (0,1),.scan 0),
  (some (0,11),some (0,11),.copy),
  (some (0,11),some (4,6),.copy),
  (some (0,3),some (0,1),.scan 2),
  (some (0,3),some (0,3),.copy),
  (some (0,5),some (0,1),.merge),
  (some (0,5),some (0,5),.copy),
  (some (2,0),some (4,0),.copy),
  (some (2,11),some (2,11),.copy),
  (some (2,11),some (4,6),.copy),
  (some (2,5),some (0,3),.merge),
  (some (2,5),some (2,5),.copy),
  (some (4,0),some (10,0),.copy),
  (some (4,0),some (4,0),.copy),
  (some (4,1),some (10,1),.copy),
  (some (4,1),some (4,1),.copy),
  (some (4,6),some (4,1),.copy),
  (some (4,6),some (4,6),.copy),
  (none,none,.scan 0)
]

def checkProduct (s : Product) : Bool :=
  let (q,r,m) := s
  ((!final q) || (final r && decide (m = .copy))) &&
    (edges q).all (fun x =>
      let (m',ys) := emit m x
      match walk r ys with
      | none => false
      | some r' => reach.contains (some x,r',m'))

theorem checked : reach.all checkProduct = true := by decide

theorem stream_legal (q r : Q) (m : Mode) (w : List Tok)
    (hr : (q,r,m) ∈ reach) (hw : legal q w) : legal r (stream m w) := by
  induction w generalizing q r m with
  | nil =>
    change final q = true at hw
    change final r = true
    have hc := List.all_eq_true.mp checked (q,r,m) hr
    simp [checkProduct,hw] at hc
    exact hc.1.1
  | cons x xs ih =>
    obtain ⟨hx,hxs⟩ := hw
    have hc := List.all_eq_true.mp checked (q,r,m) hr
    simp only [checkProduct,Bool.and_eq_true] at hc
    have ht := List.all_eq_true.mp hc.2 x hx
    cases he : emit m x with
    | mk m' ys =>
      simp only [he] at ht
      cases hh : walk r ys with
      | none => simp [hh] at ht
      | some r' =>
        simp only [hh,List.contains_iff_mem] at ht
        have hrec := ih (some x) r' m' ht hxs
        simpa only [stream,he] using walk_legal r r' ys (stream m' xs) hh hrec

-- Every accepted nonempty word satisfies the macro theorem's shape hypothesis.
def nodes : List Q := [none,some (0,1),some (0,3),some (0,5),some (0,11),some (2,0),some (2,5),some (2,11),some (4,0),some (4,1),some (4,6),some (10,0),some (10,1)]

def checkNode (q : Q) : Bool := (edges q).all (fun x =>
  nodes.contains (some x) &&
  (if final (some x) then decide (x.2=0 ∧ edges (some x)=[])
   else decide (x.2=1 ∨ x.2=3 ∨ 5≤x.2)))

theorem nodesChecked : nodes.all checkNode = true := by decide

theorem legal_shape (q : Q) (w : List Tok) (hq : q ∈ nodes) (hw : legal q w) (hne : w ≠ []) : Shape w := by
  induction w generalizing q with
  | nil => contradiction
  | cons x xs ih =>
    obtain ⟨hx,hxs⟩ := hw
    have hn := List.all_eq_true.mp nodesChecked q hq
    have h := List.all_eq_true.mp hn x hx
    simp only [Bool.and_eq_true,List.contains_iff_mem] at h
    rcases x with ⟨a,g⟩
    cases hf : final (some (a,g)) with
    | true =>
      simp only [hf,ite_true,decide_eq_true_eq] at h
      obtain ⟨hg,he⟩ := h.2
      subst g
      cases xs with
      | nil => exact Shape.last a
      | cons y ys =>
        obtain ⟨hy,_⟩ := hxs
        rw [he] at hy
        contradiction
    | false =>
      simp [hf] at h
      have hs : xs ≠ [] := by
        intro he; subst xs; exact Bool.noConfusion (hf.symm.trans hxs)
      exact Shape.more a g xs h.2 (ih _ h.1 hxs hs)

theorem legal_ne (w : List Tok) (hw : legal none w) : w ≠ [] := by
  intro h; subst w; contradiction

theorem closed (w : List Tok) (hw : legal none w) : legal none (trans 0 w) := by
  have sh := legal_shape none w (List.contains_iff_mem.mp (by decide)) hw (legal_ne w hw)
  rw [← stream_trans w 0 sh]
  exact stream_legal none none (.scan 0) w (List.contains_iff_mem.mp (by decide)) hw

theorem first (v : Bool) : run0 (table v) 34 ⟨0,[],[]⟩ = some (sec (enc [(2,0)])) := by cases v <;> rfl

theorem arbitrary (v : Bool) (k : Nat) : ∃ t, k≤t ∧ ∃ w, legal none w ∧ run0 (table v) t ⟨0,[],[]⟩ = some (sec (enc w)) := by
  induction k with
  | zero => exact ⟨34,by omega,[(2,0)],by simp [legal,edges,final],first v⟩
  | succ k ih =>
    obtain ⟨t,ht,w,hw,H⟩ := ih
    obtain ⟨s,hs,G⟩ := sectionReturn v w (legal_shape none w (List.contains_iff_mem.mp (by decide)) hw (legal_ne w hw))
    exact ⟨t+s,by omega,trans 0 w,closed w hw,join0 H G⟩

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  intro n
  obtain ⟨t,ht,w,hw,hr⟩ := arbitrary v n
  have hz : (zrun (table v) t start).map project = some (sec (enc w)) := (run_project (table v) t start).trans hr
  cases h : zrun (table v) t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound (table v) m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some _ => rfl

#print axioms checkProduct
#print axioms walk
#print axioms checked
#print axioms stream_legal
#print axioms legal_shape
#print axioms stream_trans
#print axioms nodesChecked
#print axioms closed
#print axioms never
end BB6.Agent8Raw54.RBRunPair
