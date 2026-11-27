import Std
import Lean.Elab.Tactic.Omega

namespace Counter286

abbrev Ray := Nat → Bool
abbrev Word := List Bool
abbrev z := false
abbrev o := true

def nilRay : Ray := fun _ => false
def cons (b : Bool) (r : Ray) : Ray
  | 0 => b
  | n+1 => r n

def tail (r : Ray) : Ray := fun n => r (n+1)

def pre : Word → Ray → Ray
  | [], r => r
  | b::w, r => cons b (pre w r)

def push (l : Ray) : Word → Ray
  | [] => l
  | b::w => push (cons b l) w

@[simp] theorem pre_append (u v : Word) (r : Ray) :
    pre (u++v) r = pre u (pre v r) := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [pre, ih]

@[simp] theorem push_append (l : Ray) (u v : Word) :
    push l (u++v) = push (push l u) v := by
  induction u generalizing l with
  | nil => rfl
  | cons b u ih => exact ih (cons b l)

@[simp] theorem cons_zero_blank : cons z nilRay = nilRay := by
  funext n; cases n <;> rfl

@[simp] theorem tail_cons (b : Bool) (r : Ray) : tail (cons b r) = r := rfl
@[simp] theorem head_cons (b : Bool) (r : Ray) : cons b r 0 = b := rfl

theorem etaRay (r : Ray) : cons (r 0) (tail r) = r := by
  funext n; cases n <;> rfl

structure C where
  q : Fin 6
  l : Ray
  r : Ray

def B (l r : Ray) : C := ⟨1,l,r⟩
def atL (l r : Ray) : C := B (tail l) (cons (l 0) r)

-- Exact partial table: write, right?, next state. D0 is absent.
def table (q : Fin 6) (b : Bool) : Option (Bool × Bool × Fin 6) :=
  match q.val, b with
  | 0, false => some (true,true,1)
  | 0, true => some (false,true,5)
  | 1, false => some (true,true,2)
  | 1, true => some (false,true,3)
  | 2, false => some (true,false,3)
  | 2, true => some (false,true,0)
  | 3, false => none
  | 3, true => some (false,false,4)
  | 4, false => some (true,false,1)
  | 4, true => some (true,true,2)
  | 5, false => some (false,false,4)
  | 5, true => some (true,true,2)
  | _, _ => none

def step (c : C) : Option C :=
  (table c.q (c.r 0)).map fun (w,d,q) =>
    if d then ⟨q, cons w c.l, tail c.r⟩
    else ⟨q, tail c.l, cons (c.l 0) (cons w (tail c.r))⟩

def run : Nat → C → Option C
  | 0,c => some c
  | n+1,c => (step c).bind (run n)

theorem run_add (n k : Nat) (c : C) :
    run (n+k) c = (run n c).bind (run k) := by
  induction n generalizing c with
  | zero => simp [run]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    simp only [run]
    cases step c with
    | none => rfl
    | some t => exact ih t

def Reach (c d : C) : Prop := ∃ n, run n c = some d
def Plus (c d : C) : Prop := ∃ n, n > 0 ∧ run n c = some d

theorem Reach.refl (c : C) : Reach c c := ⟨0,rfl⟩
theorem Reach.trans {c d e : C} (h : Reach c d) (g : Reach d e) : Reach c e := by
  obtain ⟨n,hn⟩ := h; obtain ⟨k,hk⟩ := g
  exact ⟨n+k, by rw [run_add,hn]; exact hk⟩
theorem Plus.reach {c d : C} (h : Plus c d) : Reach c d := by
  obtain ⟨n,_,hn⟩ := h; exact ⟨n,hn⟩
theorem Reach.thenPlus {c d e : C} (h : Reach c d) (g : Plus d e) : Plus c e := by
  obtain ⟨n,hn⟩ := h; obtain ⟨k,hk,h⟩ := g
  exact ⟨n+k, by omega, by rw [run_add,hn]; exact h⟩
theorem Plus.thenReach {c d e : C} (h : Plus c d) (g : Reach d e) : Plus c e := by
  obtain ⟨n,hn,h⟩ := h; obtain ⟨k,hk⟩ := g
  exact ⟨n+k, by omega, by rw [run_add,h]; exact hk⟩

-- The five exact local B-return rules.
theorem rule1 (l r : Ray) (a : Bool) :
    run 3 (B (cons a l) (pre [o,o] r)) = some (B l (pre [a,o,z] r)) := rfl

theorem rule2 (l r : Ray) :
    run 3 (B l (pre [z,o,z] r)) = some (B (push l [o,z,o]) r) := rfl

theorem rule3 (l r : Ray) (a : Bool) :
    run 7 (B (push l [a,z,o]) (pre [z,z] r)) = some (B l (pre [a,o,z,o,o] r)) := rfl

theorem rule4 (l r : Ray) :
    run 5 (B l (pre [z,o,o,z] r)) = some (B (cons o l) (pre [z,o,z] r)) := rfl

theorem rule5 (l r : Ray) :
    run 6 (B l (pre [z,o,o,o,o,z] r)) = some (B (push l [o,z,z,o,z,o]) r) := rfl

def P : Word := [z,z,o,o]
def Q : Word := [z,o,o,o,o]
def O : Word := [z,z,z,o,o]
def H : Word := [z,o,o]
def X : Word := [o,z,o,o]
def M : Word := [z,o,z,z,o,o,o,o]
def lead : Word := [o,z,z,o,o]

def g (n : Nat) : Word := List.replicate n z ++ [o,o]
def h (n : Nat) : Word := z :: List.replicate (n+1) o

-- 13-step turn, including the unread left endpoint.
theorem turn (l r : Ray) :
    Reach (B l (pre [z,o,z,z,z] r)) (atL l (pre lead r)) := by
  have e := etaRay l
  conv => lhs; rw [← e]
  exact ⟨13,rfl⟩

-- Scan a positive run from its final 1 to its initial zero.
theorem sweepOnes (n : Nat) (l r : Ray) :
    Reach (B (push l (List.replicate n o)) (pre [o,o] r))
      (B l (pre [o,o] (pre (List.replicate n z) r))) := by
  induction n generalizing l with
  | zero => exact Reach.refl _
  | succ n ih =>
    rw [List.replicate_succ, push]
    apply Reach.trans (ih (cons o l))
    exact ⟨3,rfl⟩

-- Sweep a block 0 1^(n+1), mapping it to g(n) on the right.
theorem rep_end (n : Nat) (b : Bool) : List.replicate (n+1) b = List.replicate n b ++ [b] := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append] at *; rw [← ih]

theorem sweep (n : Nat) (l r : Ray) :
    Reach (atL (push l (h n)) (pre lead r))
      (atL l (pre lead (pre (g n) r))) := by
  have hr : List.replicate (n+1) o = List.replicate n o ++ [o] := by
    exact rep_end n o
  have hstart : atL (push l (h n)) (pre lead r) =
      B (push (cons z l) (List.replicate n o)) (pre [o,o] (pre P r)) := by
    unfold h
    rw [hr]
    simp only [push, push_append]
    rfl
  rw [hstart]
  apply Reach.trans (sweepOnes n (cons z l) (pre P r))
  have hstep : Reach (B (cons z l) (pre [o,o] (pre (List.replicate n z) (pre P r))))
      (B l (pre [z,o,z] (pre (List.replicate n z) (pre P r)))) := ⟨3,rfl⟩
  apply Reach.trans hstep
  have he : pre [z,o,z] (pre (List.replicate n z) (pre P r)) =
      pre [z,o,z,z,z] (pre (g n) r) := by
    simp only [← pre_append]
    congr 1
    simp only [P,g,List.cons_append,List.nil_append]
    have hh : List.replicate n z ++ [z,z] = z :: z :: List.replicate n z := by
      calc
        _ = (List.replicate n z ++ [z]) ++ [z] := by simp [List.append_assoc]
        _ = List.replicate (n+1) z ++ [z] := by rw [← rep_end]
        _ = List.replicate (n+2) z := (rep_end (n+1) z).symm
        _ = _ := rfl
    change [z,o,z] ++ (List.replicate n z ++ ([z,z] ++ [o,o])) = _
    rw [← List.append_assoc (List.replicate n z) [z,z] [o,o], hh]
    rfl
  rw [he]
  exact turn l (pre (g n) r)

-- Data tokens; only the final H may be a half digit.
inductive Data where
  | nil | half | p (rest : Data) | q (rest : Data) | b (rest : Data)
  deriving DecidableEq, Repr

def tape : Data → Ray
  | .nil => nilRay
  | .half => pre H nilRay
  | .p d => pre P (tape d)
  | .q d => pre Q (tape d)
  | .b d => pre O (tape d)

def inc : Data → Data
  | .nil => .half
  | .half => .p .nil
  | .p d => .p (inc d)
  | .q d => .b (inc d)
  | .b d => .q d

@[simp] theorem tape_zero (d : Data) : tape d 0 = z := by cases d <;> rfl

def anchor (l : Ray) (d : Data) : C := B l (pre M (tape d))
def scan (l : Ray) (d : Data) : C := B l (pre [z,o] (tape d))

theorem zero_eta (r : Ray) (hr : r 0 = z) : cons z (tail r) = r := by
  rw [← hr]; exact etaRay r

theorem scanP (l : Ray) (d : Data) : Reach (scan l (.p d)) (scan (push l X) d) := by
  unfold scan
  simp only [tape]
  generalize hr : tape d = r
  have hz : r 0 = z := hr ▸ tape_zero d
  rw [← zero_eta r hz]
  exact ⟨8,rfl⟩

theorem scanQ (l : Ray) (d : Data) : Reach (scan l (.q d)) (scan (push l (o::X)) d) := by
  unfold scan
  simp only [tape]
  generalize hr : tape d = r
  have hz : r 0 = z := hr ▸ tape_zero d
  rw [← zero_eta r hz]
  exact ⟨17,rfl⟩

theorem scanH (l : Ray) : Reach (scan l .half) (scan (cons o l) .nil) := by
  refine ⟨9, ?_⟩
  change some (B (cons o l) (pre [z,o,z,z] nilRay)) = some (scan (cons o l) .nil)
  simp [scan,tape,pre]

theorem scanO (l : Ray) (d : Data) : Reach (scan l (.b d))
    (atL l (pre lead (pre (g 0) (tape d)))) := by
  exact turn l (pre (g 0) (tape d))

theorem scanNil (l : Ray) : Reach (scan l .nil) (atL l (pre lead nilRay)) := by
  simpa [scan,tape,pre,cons_zero_blank] using turn l nilRay

-- Left run merging when one or two ones precede X.
theorem mergeP (l : Ray) : push (push l (h 1)) X = push (push l (h 2)) (h 1) := rfl

theorem mergeQ (l : Ray) : push (push l (h 1)) (o::X) = push (push l (h 3)) (h 1) := rfl

theorem mergeH (l : Ray) : cons o (push l (h 1)) = push l (h 2) := rfl

-- A right borrow scan and its return sweep, over arbitrary data.
theorem borrow (d : Data) (l : Ray) :
    Reach (scan (push l (h 1)) d) (atL l (pre lead (tape (inc d)))) := by
  induction d generalizing l with
  | nil =>
    apply Reach.trans (scanNil (push l (h 1)))
    exact sweep 1 l nilRay
  | half =>
    apply Reach.trans (scanH (push l (h 1)))
    rw [mergeH]
    apply Reach.trans (scanNil (push l (h 2)))
    exact sweep 2 l nilRay
  | p d ih =>
    apply Reach.trans (scanP (push l (h 1)) d)
    rw [mergeP]
    apply Reach.trans (ih (push l (h 2)))
    exact sweep 2 l (tape (inc d))
  | q d ih =>
    apply Reach.trans (scanQ (push l (h 1)) d)
    rw [mergeQ]
    apply Reach.trans (ih (push l (h 3)))
    exact sweep 3 l (tape (inc d))
  | b d =>
    apply Reach.trans (scanO (push l (h 1)) d)
    exact sweep 1 l (pre (g 0) (tape d))

-- Consume a P at the anchor, append X and increment remaining data.
theorem anchorP (l : Ray) (d : Data) : Reach (anchor l (.p d)) (anchor (push l X) (inc d)) := by
  have hpre : Reach (anchor l (.p d)) (scan (push (push (cons z (push l X)) (h 0)) (h 1)) d) := by
    unfold anchor scan
    simp only [tape]
    generalize hr : tape d = r
    have hz : r 0 = z := hr ▸ tape_zero d
    rw [← zero_eta r hz]
    exact ⟨14,rfl⟩
  apply Reach.trans hpre
  apply Reach.trans (borrow d (push (cons z (push l X)) (h 0)))
  exact sweep 0 (cons z (push l X)) (tape (inc d))

theorem anchorO (l : Ray) (d : Data) : Reach (anchor l (.b d)) (anchor (push l (X++[z])) d) := by
  exact ⟨19,rfl⟩

theorem anchorH (l : Ray) : Reach (anchor l .half) (anchor (push l X) .nil) := by
  have hp : Reach (anchor l .half) (scan (push (cons z (push l X)) (h 0)) .nil) := by
    refine ⟨15, ?_⟩
    change some (B (push (cons z (push l X)) (h 0)) (pre [z,o,z,z] nilRay)) = _
    simp [scan,tape,pre]
  apply Reach.trans hp
  apply Reach.trans (scanNil (push (cons z (push l X)) (h 0)))
  exact sweep 0 (cons z (push l X)) nilRay

theorem anchorEmpty (l : Ray) : Plus (anchor l .nil) (atL (push l (X++[z]++X)) (pre lead nilRay)) := by
  have hp : Plus (anchor l .nil) (scan (push l (X++[z])) (.p .nil)) := ⟨19,by decide,rfl⟩
  apply Plus.thenReach hp
  apply Reach.trans (scanP (push l (X++[z])) .nil)
  rw [push_append]
  exact scanNil _

-- Group lengths and nonnegative complement-counter code.
def bump : List Nat → List Nat
  | [] => []
  | n::ns => (n+1)::ns

def shape : Data → List Nat
  | .nil | .half => []
  | .p d => bump (shape d)
  | .q d | .b d => 0 :: shape d

def code : Data → Nat
  | .nil => 0
  | .half => 1
  | .p d => code d + if shape d = [] then 2 else 0
  | .q d => 2*code d+1
  | .b d => 2*code d

@[simp] theorem shape_inc (d : Data) : shape (inc d) = shape d := by
  induction d <;> simp [inc,shape,bump, *]

@[simp] theorem code_inc (d : Data) : code (inc d) = code d+1 := by
  induction d with
  | nil => rfl
  | half => rfl
  | p d ih => simp only [inc,code,shape_inc,ih]; omega
  | q d ih => simp only [inc,code,ih]; omega
  | b d => simp [inc,code]

def rep (w : Word) : Nat → Word
  | 0 => []
  | n+1 => w ++ rep w n

def groupWord (x : Nat) : Word := rep X x ++ X ++ [z]

def packed (xs : List Nat) : Word := xs.flatMap groupWord

theorem group (x : Nat) (xs : List Nat) (d : Data) (l : Ray)
    (hs : shape d = x::xs) (hp : (code d+x)%2 = 0) :
    ∃ e, shape e = xs ∧ code e = (code d+x)/2 ∧
      Reach (anchor l d) (anchor (push l (groupWord x)) e) := by
  induction x generalizing d l with
  | zero =>
    cases d with
    | nil | half => simp [shape] at hs
    | p d =>
      cases hd : shape d <;> simp [shape,bump,hd] at hs
    | q d => simp [code] at hp
    | b d =>
      refine ⟨d, ?_, ?_, ?_⟩
      · simpa [shape] using hs
      · simp [code]
      · exact anchorO l d
  | succ x ih =>
    cases d with
    | nil | half => simp [shape] at hs
    | q d | b d => simp [shape] at hs
    | p d =>
      have hd : shape d = x::xs := by
        cases hsh : shape d with
        | nil => simp [shape,bump,hsh] at hs
        | cons a as =>
          simp [shape,bump,hsh] at hs
          obtain ⟨h1,h2⟩ := hs
          have heq : a = x := by omega
          rw [heq,h2]
      have hc : code (.p d) = code d := by simp [code,hd]
      have hi := ih (inc d) (push l X) (by simpa using hd) (by simp only [code_inc]; rw [hc] at hp; omega)
      obtain ⟨e,he,hcode,hreach⟩ := hi
      refine ⟨e,he,?_,?_⟩
      · rw [hcode, code_inc, hc]; congr 1; omega
      · have hword : groupWord (x+1) = X ++ groupWord x := by simp [groupWord,rep,List.append_assoc]
        rw [hword,push_append]
        exact (anchorP l d).trans hreach

-- With no separators left, each anchor operation decrements the terminal counter.
theorem terminal (n : Nat) (d : Data) (l : Ray) (hs : shape d = []) (hc : code d = n) :
    Reach (anchor l d) (anchor (push l (rep X n)) .nil) := by
  induction n generalizing d l with
  | zero =>
    cases d with
    | nil => exact Reach.refl _
    | half => simp [code] at hc
    | q d | b d => simp [shape] at hs
    | p d =>
      have hd : shape d = [] := by cases hsh : shape d <;> simp [shape,bump,hsh] at hs ⊢
      simp [code,hd] at hc
  | succ n ih =>
    cases d with
    | nil => simp [code] at hc
    | half =>
      have hn : n=0 := by simp [code] at hc; omega
      subst n
      exact anchorH l
    | q d | b d => simp [shape] at hs
    | p d =>
      have hd : shape d = [] := by cases hsh : shape d <;> simp [shape,bump,hsh] at hs ⊢
      have hcode : code (inc d) = n := by simp [code,hd] at hc; simp only [code_inc]; omega
      have hreach := ih (inc d) (push l X) (by simpa using hd) hcode
      simp only [rep,push_append]
      exact (anchorP l d).trans hreach

-- A list of group lengths is admissible when each separator becomes a one.
inductive Allowed : Nat → List Nat → Nat → Prop where
  | nil (a : Nat) : Allowed a [] (a+1)
  | cons {a x : Nat} {xs : List Nat} {t : Nat} :
      (a+x)%2 = 1 → Allowed ((a+x+1)/2) xs t → Allowed a (x::xs) t

theorem groups {a : Nat} {xs : List Nat} {t : Nat} (ha : Allowed a xs t)
    (d : Data) (l : Ray) (hs : shape d = xs) (hc : code d+1 = 2^(xs.length+1)+a) :
    ∃ e, shape e = [] ∧ code e = t ∧ Reach (anchor l d) (anchor (push l (packed xs)) e) := by
  induction ha generalizing d l with
  | nil a =>
    refine ⟨d,hs,?_,Reach.refl _⟩
    simp at hc; omega
  | @cons a x xs t hp ha ih =>
    have hpow : 2^((x::xs).length+1) = 2 * 2^(xs.length+1) := by
      simp only [List.length_cons,Nat.pow_succ]; omega
    rw [hpow] at hc
    have heven : (code d+x)%2 = 0 := by omega
    obtain ⟨e,he,hcode,hreach⟩ := group x xs d l hs heven
    have hc' : code e+1 = 2^(xs.length+1)+(a+x+1)/2 := by rw [hcode]; omega
    obtain ⟨f,hf,hft,hh⟩ := ih e (push l (groupWord x)) he hc'
    refine ⟨f,hf,hft,?_⟩
    simp only [packed,List.flatMap_cons,push_append]
    exact hreach.trans hh

def addP : Nat → Data → Data
  | 0,d => d
  | n+1,d => .p (addP n d)

def row : List Nat → Data
  | [] => .half
  | x::xs => addP x (.q (row xs))

theorem tape_addP (n : Nat) (d : Data) : tape (addP n d) = pre (rep P n) (tape d) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [addP,tape,rep,pre_append,ih]

theorem shape_addP (n x : Nat) (xs : List Nat) (d : Data) (hs : shape d = x::xs) :
    shape (addP n d) = (x+n)::xs := by
  induction n with
  | zero => simpa [addP] using hs
  | succ n ih => simp [addP,shape,bump,ih,Nat.add_assoc]

theorem code_addP (n x : Nat) (xs : List Nat) (d : Data) (hs : shape d = x::xs) :
    code (addP n d) = code d := by
  induction n with
  | zero => rfl
  | succ n ih => simp [addP,code,shape_addP n x xs d hs,ih]

@[simp] theorem row_shape (xs : List Nat) : shape (row xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    unfold row
    rw [shape_addP x 0 xs _ (by simp [shape,ih])]
    simp

@[simp] theorem row_code (xs : List Nat) : code (row xs)+1 = 2^(xs.length+1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    unfold row
    rw [code_addP x 0 xs _ (by simp [shape])]
    simp only [code,List.length_cons,Nat.pow_succ]
    omega

-- Packing left-side output into positive runs; each run can be swept independently.
def wordH (ns : List Nat) : Word := ns.flatMap h
def wordG (ns : List Nat) : Word := ns.flatMap g

@[simp] theorem wordH_append (xs ys : List Nat) : wordH (xs++ys) = wordH xs ++ wordH ys := by
  simp [wordH]
@[simp] theorem wordG_append (xs ys : List Nat) : wordG (xs++ys) = wordG xs ++ wordG ys := by
  simp [wordG]

theorem sweepAll (ns : List Nat) (l r : Ray) :
    Reach (atL (push l (wordH ns)) (pre lead r))
      (atL l (pre lead (pre (wordG ns) r))) := by
  induction ns generalizing l with
  | nil => exact Reach.refl _
  | cons n ns ih =>
    simp only [wordH,wordG,List.flatMap_cons,push_append,pre_append]
    apply Reach.trans (ih (push l (h n)))
    exact sweep n l (pre (wordG ns) r)

def blockRuns (x : Nat) : List Nat := 0 :: List.replicate x 2 ++ [1]
def leftRuns (xs : List Nat) : List Nat := xs.flatMap blockRuns

@[simp] theorem leftRuns_append (xs ys : List Nat) : leftRuns (xs++ys) = leftRuns xs ++ leftRuns ys := by
  simp [leftRuns]
@[simp] theorem packed_append (xs ys : List Nat) : packed (xs++ys) = packed xs ++ packed ys := by
  simp [packed]

theorem rep_end_word (w : Word) (n : Nat) : rep w (n+1) = rep w n ++ w := by
  induction n with
  | zero => simp [rep]
  | succ n ih =>
    change w ++ rep w (n+1) = (w ++ rep w n) ++ w
    rw [ih,List.append_assoc]

theorem flatMap_rep (f : Nat → Word) (n a : Nat) : (List.replicate n a).flatMap f = rep (f a) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,rep,ih]

theorem group_left (x : Nat) : z :: groupWord x = wordH (blockRuns x) ++ [z] := by
  have hv : [z] ++ rep X (x+1) = h 0 ++ rep (h 2) x ++ h 1 := by
    induction x with
    | zero => rfl
    | succ x ih =>
      rw [rep_end_word X (x+1), ← List.append_assoc, ih, rep_end_word (h 2) x]
      simp only [List.append_assoc]
      rfl
  unfold groupWord blockRuns wordH
  simp only [List.flatMap_cons,List.flatMap_append,flatMap_rep]
  change ([z] ++ rep X x ++ X) ++ [z] = (h 0 ++ (rep (h 2) x ++ h 1)) ++ [z]
  rw [List.append_assoc [z], ← rep_end_word, hv]
  simp only [List.append_assoc]

theorem packed_left (xs : List Nat) (l : Ray) :
    push (cons z l) (packed xs) = cons z (push l (wordH (leftRuns xs))) := by
  induction xs generalizing l with
  | nil => rfl
  | cons x xs ih =>
    simp only [packed,List.flatMap_cons,push_append,leftRuns,wordH_append]
    have hx : push (cons z l) (groupWord x) = cons z (push l (wordH (blockRuns x))) := by
      change push l (z::groupWord x) = _
      rw [group_left,push_append]
      rfl
    rw [hx]
    exact ih (push l (wordH (blockRuns x)))

theorem group_right (x : Nat) : wordG (blockRuns x) = g 0 ++ rep P x ++ H := by
  unfold wordG blockRuns
  simp only [List.flatMap_cons,List.flatMap_append,flatMap_rep]
  change g 0 ++ (rep P x ++ H) = _
  rw [List.append_assoc]

theorem right_pack (xs : List Nat) : pre (wordG (leftRuns xs ++ [0,1])) nilRay = pre (g 0) (tape (row xs)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [leftRuns,List.flatMap_cons,List.append_assoc,wordG_append,pre_append,group_right,row,tape_addP,tape]
    have he : pre (wordG (xs.flatMap blockRuns)) (pre (wordG [0,1]) nilRay) = pre (g 0) (tape (row xs)) := by
      simpa only [leftRuns,wordG_append,pre_append] using ih
    rw [he]
    rfl

theorem finish (xs : List Nat) (t : Nat) :
    Plus (anchor (push (push nilRay (packed xs)) (rep X t)) .nil)
      (anchor nilRay (row (xs++[t]))) := by
  apply Plus.thenReach (anchorEmpty _)
  have hp : push (push (push nilRay (packed xs)) (rep X t)) (X++[z]++X) =
      push nilRay (packed (xs++[t]) ++ X) := by
    simp only [← push_append,packed_append]
    change push nilRay ((packed xs ++ rep X t) ++ (X++[z]++X)) =
      push nilRay ((packed xs ++ (groupWord t ++ [])) ++ X)
    simp [groupWord,List.append_assoc]
  rw [hp,push_append]
  have hx : push nilRay (packed (xs++[t])) = cons z (push nilRay (wordH (leftRuns (xs++[t])))) := by
    simpa using packed_left (xs++[t]) nilRay
  rw [hx]
  have he : push (cons z (push nilRay (wordH (leftRuns (xs++[t]))))) X =
      push nilRay (wordH (leftRuns (xs++[t])++[0,1])) := by
    simp only [wordH_append,push_append]
    rfl
  rw [he]
  have hf := sweepAll (leftRuns (xs++[t])++[0,1]) nilRay nilRay
  rw [right_pack] at hf
  exact hf

theorem row_step (xs : List Nat) (t : Nat) (ha : Allowed 0 xs t) :
    Plus (anchor nilRay (row xs)) (anchor nilRay (row (xs++[t]))) := by
  obtain ⟨e,he,hc,hreach⟩ := groups ha (row xs) nilRay (row_shape xs) (by simp)
  have ht := terminal t e (push nilRay (packed xs)) he hc
  exact (hreach.trans ht).thenPlus (finish xs t)

def ramp (a : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => (a+1)::ramp (a+1) n

def family (n : Nat) : List Nat := 5 :: ramp 3 n

theorem ramp_allowed (a n : Nat) : Allowed a (ramp a n) (a+n+1) := by
  induction n generalizing a with
  | zero => exact Allowed.nil a
  | succ n ih =>
    unfold ramp
    apply Allowed.cons (by omega)
    have he : (a+(a+1)+1)/2 = a+1 := by omega
    rw [he]
    have ht : a+(n+1)+1 = (a+1)+n+1 := by omega
    rw [ht]
    exact ih (a+1)

theorem family_allowed (n : Nat) : Allowed 0 (family n) (n+4) := by
  unfold family
  apply Allowed.cons (by decide)
  have he : (0+5+1)/2 = 3 := by decide
  rw [he]
  have hf := ramp_allowed 3 n
  rwa [show 3+n+1=n+4 by omega] at hf

theorem ramp_next (a n : Nat) : ramp a (n+1) = ramp a n ++ [a+n+1] := by
  induction n generalizing a with
  | zero => simp [ramp]
  | succ n ih =>
    change (a+1)::ramp (a+1) (n+1) = (a+1)::(ramp (a+1) n ++ [a+(n+1)+1])
    rw [ih (a+1)]
    rw [show (a+1)+n+1=a+(n+1)+1 by omega]

theorem family_next (n : Nat) : family (n+1) = family n ++ [n+4] := by
  simp only [family,ramp_next,List.cons_append]
  rw [show 3+n+1=n+4 by omega]

def cfg (n : Nat) := anchor nilRay (row (family n))

theorem cfg_next (n : Nat) : Plus (cfg n) (cfg (n+1)) := by
  unfold cfg
  rw [family_next]
  exact row_step (family n) (n+4) (family_allowed n)

def blankC : C := ⟨0,nilRay,nilRay⟩

-- Finite-list evaluator for the exact 928-move seed, linked to the ray model.
structure F where
  q : Fin 6
  l : Word
  r : Word
  deriving DecidableEq, Repr

def embedF (f : F) : C := ⟨f.q,pre f.l nilRay,pre f.r nilRay⟩
def stepF (f : F) : Option F :=
  (table f.q (f.r.headD false)).map fun (w,d,q) =>
    if d then ⟨q,w::f.l,f.r.tail⟩
    else ⟨q,f.l.tail,f.l.headD false::w::f.r.tail⟩

def runF : Nat → F → Option F
  | 0,f => some f
  | n+1,f => (stepF f).bind (runF n)

theorem pre_head (w : Word) : pre w nilRay 0 = w.headD false := by cases w <;> rfl
theorem pre_tail (w : Word) : tail (pre w nilRay) = pre w.tail nilRay := by cases w <;> rfl

theorem stepF_sound (f : F) : step (embedF f) = (stepF f).map embedF := by
  unfold step embedF stepF
  simp only [pre_head,pre_tail]
  cases ht : table f.q (f.r.headD false) with
  | none => rfl
  | some v =>
    rcases v with ⟨w,d,q⟩
    cases d <;> rfl

theorem runF_sound (n : Nat) (f : F) : run n (embedF f) = (runF n f).map embedF := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [run,runF,stepF_sound]
    cases stepF f with
    | none => rfl
    | some t => exact ih t

def seedF : F := ⟨0,[],[]⟩
def seedEnd : F := ⟨1,[],M ++ rep P 5 ++ Q ++ H⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem seed_exact : runF 928 seedF = some seedEnd := by decide

theorem seed : Reach blankC (cfg 0) := by
  refine ⟨928, ?_⟩
  change run 928 (embedF seedF) = some (embedF seedEnd)
  rw [runF_sound,seed_exact]; rfl

theorem run_none_add (n k : Nat) (c : C) (hn : run n c = none) : run (n+k) c = none := by
  rw [run_add,hn]; rfl

-- Arbitrarily long finite prefixes, not merely a single bounded simulation.
theorem long_prefix (n : Nat) : ∃ k, n ≤ k ∧ run k blankC = some (cfg n) := by
  induction n with
  | zero => obtain ⟨k,hk⟩ := seed; exact ⟨k,Nat.zero_le _,hk⟩
  | succ n ih =>
    obtain ⟨k,hk,hr⟩ := ih
    obtain ⟨j,hj,hs⟩ := cfg_next n
    exact ⟨k+j,by omega,by rw [run_add,hr]; exact hs⟩

theorem never : ∀ n, ∃ c, run n blankC = some c := by
  intro n
  obtain ⟨k,hk,hr⟩ := long_prefix n
  cases h : run n blankC with
  | some c => exact ⟨c,rfl⟩
  | none =>
    obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hk
    rw [hj,run_none_add n j blankC h] at hr
    contradiction

#print axioms seed_exact
#print axioms cfg_next
#print axioms never

end Counter286
