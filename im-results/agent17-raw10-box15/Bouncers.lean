import Lean
namespace Box15
abbrev Ray := Nat → Bool
abbrev Q := Fin 6
structure Move where
  write : Bool
  right : Bool
  next : Q
abbrev Table := Q → Bool → Option Move
structure Prim where
  q : Q
  l : Ray
  r : Ray
def cons (a : Bool) (r : Ray) : Ray | 0 => a | n+1 => r n
def tail (r : Ray) : Ray := fun n => r (n+1)
def blank : Ray := fun _ => false
@[simp] theorem cons_zero (a : Bool) (r : Ray) : cons a r 0 = a := rfl
@[simp] theorem tail_cons (a : Bool) (r : Ray) : tail (cons a r) = r := rfl
@[simp] theorem blank_cons : cons false blank = blank := by funext n; cases n <;> rfl
@[simp] theorem blank_tail : tail blank = blank := rfl
def step (M : Table) (c : Prim) : Option Prim := do
  let mv ← M c.q (c.r 0)
  if mv.right then return ⟨mv.next,cons mv.write c.l,tail c.r⟩
  else return ⟨mv.next,tail c.l,cons (c.l 0) (cons mv.write (tail c.r))⟩
def run (M : Table) : Nat → Prim → Option Prim
  | 0,c => some c
  | n+1,c => (step M c).bind (run M n)
theorem run_add (M : Table) (m n : Nat) (c : Prim) : run M (m+n) c = (run M m c).bind (run M n) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => simp only [Nat.succ_add,run,Option.bind_assoc]; cases step M c <;> simp [ih]
def table (t : List Nat) : Table := fun q b =>
  let v := t[2*q.val + b.toNat]!
  if v = 0 then none else some ⟨(v-1)/2%2 == 1, (v-1)%2 == 1, Fin.ofNat _ ((v-1)/4)⟩
def pre : List Bool → Ray → Ray
  | [],r => r
  | a::as,r => cons a (pre as r)
def rep (w : List Bool) : Nat → Ray → Ray
  | 0,r => r
  | k+1,r => pre w (rep w k r)
theorem pre_append (u v : List Bool) (r : Ray) : pre (u++v) r = pre u (pre v r) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append,pre,ih]
theorem rep_push (w : List Bool) (n : Nat) (r : Ray) : rep w n (pre w r) = rep w (n+1) r := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,ih]
def six : List Bool := [true,true,true,true,true,true]
def w : List Bool := [false,false,true,false,false,true]
def root (k : Nat) : Prim := ⟨1,cons true (rep six k blank),blank⟩
def init : Prim := ⟨0,blank,blank⟩
-- One generic finite-word sweep transports an arbitrary number of repetitions.
theorem sweep (M : Table) (q : Q) (u v x y : List Bool) (a : Nat)
    (h : ∀ l r, run M a ⟨q,pre u (pre x l),pre v r⟩ = some ⟨q,pre u l,pre v (pre y r)⟩)
    (k : Nat) (l r : Ray) :
    run M (a*k) ⟨q,pre u (rep x k l),pre v r⟩ = some ⟨q,pre u l,pre v (rep y k r)⟩ := by
  induction k generalizing r with
  | zero => simp [rep,run]
  | succ k ih =>
    rw [show a*(k+1)=a+a*k by rw [Nat.mul_succ,Nat.add_comm],run_add]
    change (run M a ⟨q,pre u (pre x (rep x k l)),pre v r⟩).bind (run M (a*k)) = _
    rw [h,Option.bind_some,ih,rep_push]
theorem sweepR (M : Table) (q : Q) (u v x y : List Bool) (a : Nat)
    (h : ∀ l r, run M a ⟨q,pre u l,pre v (pre x r)⟩ = some ⟨q,pre u (pre y l),pre v r⟩)
    (k : Nat) (l r : Ray) :
    run M (a*k) ⟨q,pre u l,pre v (rep x k r)⟩ = some ⟨q,pre u (rep y k l),pre v r⟩ := by
  induction k generalizing l with
  | zero => simp [rep,run]
  | succ k ih =>
    rw [show a*(k+1)=a+a*k by rw [Nat.mul_succ,Nat.add_comm],run_add]
    change (run M a ⟨q,pre u l,pre v (pre x (rep x k r))⟩).bind (run M (a*k)) = _
    rw [h,Option.bind_some,ih,rep_push]
-- The two directional sweeps combine into a positive-time recurrent section.
theorem forever (M : Table) (f : Nat → Prim) (cost : Nat → Nat)
    (pos : ∀ k, 0 < cost k) (h : ∀ k, run M (cost k) (f k) = some (f (k+1))) :
    ∀ n k, ∃ c, run M n (f k) = some c := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k
    by_cases hk : cost k ≤ n
    · obtain ⟨c,hc⟩ := ih (n-cost k) (by have := pos k; omega) (k+1)
      exact ⟨c,by rw [show n=cost k+(n-cost k) by omega,run_add,h]; exact hc⟩
    · have hh := h k
      rw [show cost k=n+(cost k-n) by omega,run_add] at hh
      cases hn : run M n (f k) with
      | none => simp [hn] at hh
      | some c => exact ⟨c,rfl⟩
theorem init_forever (M : Table) (f : Nat → Prim) (cost : Nat → Nat)
    (pos : ∀ k, 0 < cost k) (h : ∀ k, run M (cost k) (f k) = some (f (k+1)))
    (t : Nat) (start : run M t init = some (f 1)) : ∀ n, ∃ c, run M n init = some c := by
  intro n
  by_cases hn : t ≤ n
  · obtain ⟨c,hc⟩ := forever M f cost pos h (n-t) 1
    exact ⟨c,by rw [show n=t+(n-t) by omega,run_add,start]; exact hc⟩
  · rw [show t=n+(t-n) by omega,run_add] at start
    cases hc : run M n init with
    | none => simp [hc] at start
    | some c => exact ⟨c,rfl⟩
def two : List Bool := [true,true]
theorem bounce (M : Table) (a b turn finish : Nat) (q : Q) (u v : List Bool)
    (entry : ∀ l, run M 1 ⟨1,cons true l,blank⟩ = some ⟨2,l,pre two blank⟩)
    (leftStep : ∀ l r, run M a ⟨2,pre six l,pre two r⟩ = some ⟨2,l,pre two (pre w r)⟩)
    (turnStep : ∀ r, run M turn ⟨2,blank,pre two r⟩ = some ⟨q,pre u blank,pre v r⟩)
    (rightStep : ∀ l r, run M b ⟨q,pre u l,pre v (pre w r)⟩ = some ⟨q,pre u (pre six l),pre v r⟩)
    (endStep : ∀ l, run M finish ⟨q,pre u l,pre v blank⟩ = some ⟨1,cons true (pre six l),blank⟩)
    (k : Nat) : run M (1+a*k+turn+b*k+finish) (root k) = some (root (k+1)) := by
  rw [run_add,run_add,run_add,run_add]
  unfold root
  rw [entry,Option.bind_some]
  have hL := sweep M 2 [] two six w a leftStep k blank blank
  change run M (a*k) ⟨2,rep six k blank,pre two blank⟩ = _ at hL
  rw [hL,Option.bind_some]
  change ((run M turn ⟨2,blank,pre two (rep w k blank)⟩).bind _).bind _ = _
  rw [turnStep,Option.bind_some]
  rw [sweepR M q u v w six b rightStep k blank blank,Option.bind_some,endStep]
  rfl

def m1 : Table := fun q b => match q.val, b with
  | 0, false => some ⟨true, true, 1⟩
  | 0, true => some ⟨true, false, 4⟩
  | 1, false => some ⟨true, false, 2⟩
  | 1, true => some ⟨false, true, 1⟩
  | 2, false => some ⟨false, false, 4⟩
  | 2, true => some ⟨false, false, 3⟩
  | 3, false => some ⟨true, false, 2⟩
  | 3, true => some ⟨false, false, 5⟩
  | 4, false => some ⟨true, true, 0⟩
  | 4, true => some ⟨true, true, 4⟩
  | 5, true => some ⟨true, false, 2⟩
  | _, _ => none
theorem recurrence1 (k : Nat) : run m1 (1+6*k+12+14*k+4) (root k) = some (root (k+1)) := by
  apply bounce m1 6 14 12 4 4 [true,true,true] [true,true]
  · intro l; rfl
  · intro l r; rfl
  · intro r; first | rfl | simp [m1,run,step,table,pre,two,six,w,blank]
  · intro l r; rfl
  · intro l; first | rfl | simp [m1,run,step,table,pre,two,six,w,blank]
theorem initial1 : run m1 18 init = some (root 1) := by
  first | rfl | simp [m1,run,step,table,pre,six,rep,root,init,blank]
theorem never1 : ∀ n, ∃ c, run m1 n init = some c :=
  init_forever m1 root (fun k => 1+6*k+12+14*k+4) (by intro k; omega) recurrence1 18 initial1
#print axioms never1

def m2 : Table := fun q b => match q.val, b with
  | 0, false => some ⟨true, true, 1⟩
  | 0, true => some ⟨true, false, 4⟩
  | 1, false => some ⟨true, false, 2⟩
  | 1, true => some ⟨false, true, 1⟩
  | 2, false => some ⟨false, false, 4⟩
  | 2, true => some ⟨false, false, 3⟩
  | 3, false => some ⟨true, false, 2⟩
  | 3, true => some ⟨true, false, 5⟩
  | 4, false => some ⟨true, true, 0⟩
  | 4, true => some ⟨true, true, 4⟩
  | 5, true => some ⟨false, true, 2⟩
  | _, _ => none
theorem recurrence2 (k : Nat) : run m2 (1+10*k+12+14*k+4) (root k) = some (root (k+1)) := by
  apply bounce m2 10 14 12 4 4 [true,true,true] [true,true]
  · intro l; rfl
  · intro l r; rfl
  · intro r; first | rfl | simp [m2,run,step,table,pre,two,six,w,blank]
  · intro l r; rfl
  · intro l; first | rfl | simp [m2,run,step,table,pre,two,six,w,blank]
theorem initial2 : run m2 18 init = some (root 1) := by
  first | rfl | simp [m2,run,step,table,pre,six,rep,root,init,blank]
theorem never2 : ∀ n, ∃ c, run m2 n init = some c :=
  init_forever m2 root (fun k => 1+10*k+12+14*k+4) (by intro k; omega) recurrence2 18 initial2
#print axioms never2

def m3 : Table := fun q b => match q.val, b with
  | 0, false => some ⟨true, true, 1⟩
  | 0, true => some ⟨true, true, 4⟩
  | 1, false => some ⟨true, false, 2⟩
  | 1, true => some ⟨false, true, 1⟩
  | 2, false => some ⟨false, false, 4⟩
  | 2, true => some ⟨false, false, 3⟩
  | 3, false => some ⟨true, false, 2⟩
  | 3, true => some ⟨false, false, 5⟩
  | 4, false => some ⟨true, true, 0⟩
  | 4, true => some ⟨true, true, 4⟩
  | 5, true => some ⟨true, false, 2⟩
  | _, _ => none
theorem recurrence3 (k : Nat) : run m3 (1+6*k+12+10*k+2) (root k) = some (root (k+1)) := by
  apply bounce m3 6 10 12 2 4 [true,true,true,true,true] []
  · intro l; rfl
  · intro l r; rfl
  · intro r; first | rfl | simp [m3,run,step,table,pre,two,six,w,blank]
  · intro l r; rfl
  · intro l; first | rfl | simp [m3,run,step,table,pre,two,six,w,blank]
theorem initial3 : run m3 16 init = some (root 1) := by
  first | rfl | simp [m3,run,step,table,pre,six,rep,root,init,blank]
theorem never3 : ∀ n, ∃ c, run m3 n init = some c :=
  init_forever m3 root (fun k => 1+6*k+12+10*k+2) (by intro k; omega) recurrence3 16 initial3
#print axioms never3

def m4 : Table := fun q b => match q.val, b with
  | 0, false => some ⟨true, true, 1⟩
  | 0, true => some ⟨true, true, 4⟩
  | 1, false => some ⟨true, false, 2⟩
  | 1, true => some ⟨false, true, 1⟩
  | 2, false => some ⟨false, false, 4⟩
  | 2, true => some ⟨false, false, 3⟩
  | 3, false => some ⟨true, false, 2⟩
  | 3, true => some ⟨true, false, 5⟩
  | 4, false => some ⟨true, true, 0⟩
  | 4, true => some ⟨true, true, 4⟩
  | 5, true => some ⟨false, true, 2⟩
  | _, _ => none
theorem recurrence4 (k : Nat) : run m4 (1+10*k+12+10*k+2) (root k) = some (root (k+1)) := by
  apply bounce m4 10 10 12 2 4 [true,true,true,true,true] []
  · intro l; rfl
  · intro l r; rfl
  · intro r; first | rfl | simp [m4,run,step,table,pre,two,six,w,blank]
  · intro l r; rfl
  · intro l; first | rfl | simp [m4,run,step,table,pre,two,six,w,blank]
theorem initial4 : run m4 16 init = some (root 1) := by
  first | rfl | simp [m4,run,step,table,pre,six,rep,root,init,blank]
theorem never4 : ∀ n, ∃ c, run m4 n init = some c :=
  init_forever m4 root (fun k => 1+10*k+12+10*k+2) (by intro k; omega) recurrence4 16 initial4
#print axioms never4

def m7 : Table := fun q b => match q.val, b with
  | 0, false => some ⟨true, true, 1⟩
  | 0, true => some ⟨false, true, 2⟩
  | 1, false => some ⟨true, false, 2⟩
  | 1, true => some ⟨false, true, 1⟩
  | 2, false => some ⟨false, false, 4⟩
  | 2, true => some ⟨false, false, 3⟩
  | 3, false => some ⟨true, false, 2⟩
  | 3, true => some ⟨true, false, 4⟩
  | 4, false => some ⟨true, true, 5⟩
  | 4, true => some ⟨false, true, 2⟩
  | 5, false => some ⟨true, true, 0⟩
  | _, _ => none
theorem recurrence7 (k : Nat) : run m7 (1+10*k+2+16*k+12) (root k) = some (root (k+1)) := by
  apply bounce m7 10 16 2 12 2 [false] [false,true,false,true]
  · intro l; rfl
  · intro l r; rfl
  · intro r; change run m7 2 ⟨2,blank,pre two r⟩ = some ⟨2,cons false blank,pre [false,true,false,true] r⟩; rw [blank_cons]; rfl
  · intro l r; rfl
  · intro l; first | rfl | simp [m7,run,step,table,pre,two,six,w,blank]
theorem initial7 : run m7 16 init = some (root 1) := by
  first | rfl | simp [m7,run,step,table,pre,six,rep,root,init,blank]
theorem never7 : ∀ n, ∃ c, run m7 n init = some c :=
  init_forever m7 root (fun k => 1+10*k+2+16*k+12) (by intro k; omega) recurrence7 16 initial7
#print axioms never7

def m8 : Table := fun q b => match q.val, b with
  | 0, false => some ⟨true, true, 1⟩
  | 0, true => some ⟨true, true, 2⟩
  | 1, false => some ⟨true, false, 2⟩
  | 1, true => some ⟨false, true, 1⟩
  | 2, false => some ⟨false, false, 4⟩
  | 2, true => some ⟨false, false, 3⟩
  | 3, false => some ⟨true, false, 2⟩
  | 3, true => some ⟨true, false, 4⟩
  | 4, false => some ⟨true, true, 5⟩
  | 4, true => some ⟨false, true, 2⟩
  | 5, false => some ⟨true, true, 0⟩
  | _, _ => none
theorem recurrence8 (k : Nat) : run m8 (1+10*k+2+20*k+16) (root k) = some (root (k+1)) := by
  apply bounce m8 10 20 2 16 2 [false] [false,true,false,true]
  · intro l; rfl
  · intro l r; rfl
  · intro r; change run m8 2 ⟨2,blank,pre two r⟩ = some ⟨2,cons false blank,pre [false,true,false,true] r⟩; rw [blank_cons]; rfl
  · intro l r; rfl
  · intro l; first | rfl | simp [m8,run,step,table,pre,two,six,w,blank]
theorem initial8 : run m8 20 init = some (root 1) := by
  first | rfl | simp [m8,run,step,table,pre,six,rep,root,init,blank]
theorem never8 : ∀ n, ∃ c, run m8 n init = some c :=
  init_forever m8 root (fun k => 1+10*k+2+20*k+16) (by intro k; omega) recurrence8 20 initial8
#print axioms never8

def m9 : Table := fun q b => match q.val, b with
  | 0, false => some ⟨true, true, 1⟩
  | 0, true => some ⟨true, true, 5⟩
  | 1, false => some ⟨true, false, 2⟩
  | 1, true => some ⟨false, true, 1⟩
  | 2, false => some ⟨false, false, 4⟩
  | 2, true => some ⟨false, false, 3⟩
  | 3, false => some ⟨true, false, 2⟩
  | 3, true => some ⟨true, false, 4⟩
  | 4, false => some ⟨true, true, 5⟩
  | 4, true => some ⟨false, true, 2⟩
  | 5, false => some ⟨true, true, 0⟩
  | _, _ => none
theorem recurrence9 (k : Nat) : run m9 (1+10*k+2+12*k+8) (root k) = some (root (k+1)) := by
  apply bounce m9 10 12 2 8 2 [false] [false,true,false,true]
  · intro l; rfl
  · intro l r; rfl
  · intro r; change run m9 2 ⟨2,blank,pre two r⟩ = some ⟨2,cons false blank,pre [false,true,false,true] r⟩; rw [blank_cons]; rfl
  · intro l r; rfl
  · intro l; first | rfl | simp [m9,run,step,table,pre,two,six,w,blank]
theorem initial9 : run m9 12 init = some (root 1) := by
  first | rfl | simp [m9,run,step,table,pre,six,rep,root,init,blank]
theorem never9 : ∀ n, ∃ c, run m9 n init = some c :=
  init_forever m9 root (fun k => 1+10*k+2+12*k+8) (by intro k; omega) recurrence9 12 initial9
#print axioms never9
end Box15
