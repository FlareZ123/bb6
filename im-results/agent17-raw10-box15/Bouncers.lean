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

-- Commuting finite words can pass through arbitrary repeated blocks.
theorem commute_pre_rep (u x : List Bool) (hc : u++x=x++u) (k : Nat) (r : Ray) :
    pre u (rep x k r) = rep x k (pre u r) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rep]
    rw [← pre_append,hc,pre_append,ih]
def ones (n : Nat) : List Bool := List.replicate n true
def tri : List Bool := [true,false,true]
def ww : List Bool := [true,false,true,true,false,true]
def one : List Bool := [true]
def z1 : List Bool := [false,true]
def z11 : List Bool := [false,true,true]
theorem join (M : Table) {a b : Nat} {c d e : Prim} (h : run M a c = some d) (g : run M b d = some e) :
    run M (a+b) c = some e := by rw [run_add,h]; exact g

def largeCost (a b c d e f : Nat) (k : Nat) : Nat :=
  1+6*(k+1)+a+b*k+c+3+6*(k+1)+d+b*(k+1)+4+6*(k+1)+e+b*k+f

theorem largeBounce (M : Table) (a b c d e f : Nat)
    (entry : ∀ l, run M 1 ⟨1,cons true l,blank⟩ = some ⟨2,l,pre two blank⟩)
    (leftStep : ∀ l r, run M 6 ⟨2,pre six l,pre two r⟩ = some ⟨2,l,pre two (pre ww r)⟩)
    (rightStep : ∀ l r, run M b ⟨1,l,pre one (pre ww r)⟩ = some ⟨1,pre six l,pre one r⟩)
    (turn1 : ∀ r, run M a ⟨2,blank,pre two (pre ww r)⟩ = some ⟨1,pre (ones 4) blank,pre one (pre ww r)⟩)
    (finish1 : ∀ l, run M c ⟨1,l,pre one (pre ww blank)⟩ = some ⟨1,cons false (pre six l),blank⟩)
    (entry2 : ∀ l, run M 3 ⟨1,cons false (pre two l),blank⟩ = some ⟨2,l,pre two (pre z1 blank)⟩)
    (turn2 : ∀ r, run M d ⟨2,pre two blank,pre two (pre ww r)⟩ = some ⟨1,pre (ones 5) blank,pre one (pre ww r)⟩)
    (finish2 : ∀ l, run M 4 ⟨1,pre two l,pre one (pre z1 blank)⟩ = some ⟨2,l,pre two (pre z11 blank)⟩)
    (turn3 : ∀ r, run M e ⟨2,pre (ones 3) blank,pre two (pre ww r)⟩ = some ⟨1,pre (ones 4) blank,pre one (pre ww (pre tri r))⟩)
    (finish3 : ∀ l, run M f ⟨1,l,pre one (pre ww (pre tri (pre z11 blank)))⟩ = some ⟨1,pre (ones 15) l,blank⟩)
    (k : Nat) : run M (largeCost a b c d e f k) (root (k+1)) = some (root (k+3)) := by
  have h1 := entry (rep six (k+1) blank)
  have h2 := sweep M 2 [] two six ww 6 leftStep (k+1) blank blank
  have h3 := turn1 (rep ww k blank)
  have hh3 := join M (join M h1 h2) h3
  have h4 := sweepR M 1 [] one ww six b rightStep k (pre (ones 4) blank) (pre ww blank)
  rw [rep_push] at h4
  have hh4 := join M hh3 h4
  have h5 := finish1 (rep six k (pre (ones 4) blank))
  have hh5 := join M hh4 h5
  have h6 := entry2 (pre (ones 4) (rep six k (pre (ones 4) blank)))
  have hh6 := join M hh5 h6
  have eq6 : pre (ones 4) (rep six k (pre (ones 4) blank)) = rep six (k+1) (pre two blank) := by
    rw [commute_pre_rep (ones 4) six (by decide), ← rep_push]
    rfl
  rw [eq6] at hh6
  have h7 := sweep M 2 [] two six ww 6 leftStep (k+1) (pre two blank) (pre z1 blank)
  have hh7 := join M hh6 h7
  have h8 := turn2 (rep ww k (pre z1 blank))
  have hh8 := join M hh7 h8
  have h9 := sweepR M 1 [] one ww six b rightStep (k+1) (pre (ones 5) blank) (pre z1 blank)
  have hh9 := join M hh8 h9
  have eq9 : rep six (k+1) (pre (ones 5) blank) = pre two (rep six (k+1) (pre (ones 3) blank)) := by
    rw [commute_pre_rep two six (by decide)]
    rfl
  rw [eq9] at hh9
  have h10 := finish2 (rep six (k+1) (pre (ones 3) blank))
  have hh10 := join M hh9 h10
  have h11 := sweep M 2 [] two six ww 6 leftStep (k+1) (pre (ones 3) blank) (pre z11 blank)
  have hh11 := join M hh10 h11
  have h12 := turn3 (rep ww k (pre z11 blank))
  have hh12 := join M hh11 h12
  rw [commute_pre_rep tri ww (by decide)] at hh12
  have h13 := sweepR M 1 [] one ww six b rightStep k (pre (ones 4) blank) (pre ww (pre tri (pre z11 blank)))
  rw [rep_push] at h13
  have hh13 := join M hh12 h13
  have h14 := finish3 (rep six k (pre (ones 4) blank))
  have hh14 := join M hh13 h14
  have eq14 : pre (ones 15) (rep six k (pre (ones 4) blank)) = cons true (rep six (k+3) blank) := by
    change pre one (pre (ones 14) (rep six k (pre (ones 4) blank))) = pre one (rep six (k+3) blank)
    rw [commute_pre_rep (ones 14) six (by decide)]
    rw [← rep_push,← rep_push,← rep_push]
    rfl
  rw [eq14] at hh14
  exact hh14

def m5 : Table := fun q b => match q.val, b with
  | 0, false => some ⟨true, true, 1⟩
  | 0, true => some ⟨true, true, 0⟩
  | 1, false => some ⟨true, false, 2⟩
  | 1, true => some ⟨false, true, 1⟩
  | 2, false => some ⟨false, false, 4⟩
  | 2, true => some ⟨false, false, 3⟩
  | 3, false => some ⟨true, false, 2⟩
  | 3, true => some ⟨true, false, 4⟩
  | 4, false => some ⟨true, true, 5⟩
  | 4, true => some ⟨true, false, 2⟩
  | 5, false => some ⟨true, false, 0⟩
  | _, _ => none
theorem recurrence5 (k : Nat) : run m5 (largeCost 9 12 13 11 12 33 k) (root (k+1)) = some (root (k+3)) := by
  apply largeBounce m5 9 12 13 11 12 33
  all_goals intros; rfl

def m6 : Table := fun q b => match q.val, b with
  | 0, false => some ⟨true, true, 1⟩
  | 0, true => some ⟨true, true, 0⟩
  | 1, false => some ⟨true, false, 2⟩
  | 1, true => some ⟨false, true, 1⟩
  | 2, false => some ⟨false, false, 4⟩
  | 2, true => some ⟨false, false, 3⟩
  | 3, false => some ⟨true, false, 2⟩
  | 3, true => some ⟨true, false, 4⟩
  | 4, false => some ⟨true, true, 5⟩
  | 4, true => some ⟨true, false, 2⟩
  | 5, false => some ⟨true, true, 0⟩
  | _, _ => none
theorem recurrence6 (k : Nat) : run m6 (largeCost 7 10 11 9 10 27 k) (root (k+1)) = some (root (k+3)) := by
  apply largeBounce m6 7 10 11 9 10 27
  all_goals intros; rfl

def largeRoot (k : Nat) : Prim := root (2*k+2)
theorem largeRecurrence5 (k : Nat) : run m5 (largeCost 9 12 13 11 12 33 (2*k+1)) (largeRoot k) = some (largeRoot (k+1)) := by
  simpa [largeRoot,show 2*(k+1)+2=2*k+1+3 by omega] using recurrence5 (2*k+1)
theorem initial5 : run m5 63 init = some (largeRoot 0) := by rfl
theorem never5 : ∀ n, ∃ c, run m5 n init = some c := by
  intro n
  by_cases hn : 63 ≤ n
  · obtain ⟨c,hc⟩ := forever m5 largeRoot (fun k => largeCost 9 12 13 11 12 33 (2*k+1)) (by intro k; unfold largeCost; omega) largeRecurrence5 (n-63) 0
    exact ⟨c,by rw [show n=63+(n-63) by omega,run_add,initial5]; exact hc⟩
  · have h := initial5
    rw [show 63=n+(63-n) by omega,run_add] at h
    cases hh : run m5 n init with
    | none => simp [hh] at h
    | some c => exact ⟨c,rfl⟩
#print axioms never5
theorem largeRecurrence6 (k : Nat) : run m6 (largeCost 7 10 11 9 10 27 (2*k+1)) (largeRoot k) = some (largeRoot (k+1)) := by
  simpa [largeRoot,show 2*(k+1)+2=2*k+1+3 by omega] using recurrence6 (2*k+1)
theorem initial6 : run m6 53 init = some (largeRoot 0) := by rfl
theorem never6 : ∀ n, ∃ c, run m6 n init = some c := by
  intro n
  by_cases hn : 53 ≤ n
  · obtain ⟨c,hc⟩ := forever m6 largeRoot (fun k => largeCost 7 10 11 9 10 27 (2*k+1)) (by intro k; unfold largeCost; omega) largeRecurrence6 (n-53) 0
    exact ⟨c,by rw [show n=53+(n-53) by omega,run_add,initial6]; exact hc⟩
  · have h := initial6
    rw [show 53=n+(53-n) by omega,run_add] at h
    cases hh : run m6 n init with
    | none => simp [hh] at h
    | some c => exact ⟨c,rfl⟩
#print axioms never6
end Box15
