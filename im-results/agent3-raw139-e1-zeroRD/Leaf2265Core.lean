import Std
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3Leaf2265
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev Ray := Nat → Bool
def blank : Ray := fun _ => false
def cons (b : Bool) (r : Ray) : Ray
  | 0 => b
  | n+1 => r n
def tail (r : Ray) : Ray := fun n => r (n+1)
@[simp] theorem zero_blank : cons false blank = blank := by
  funext n; cases n <;> rfl
def pre : List Bool → Ray → Ray
  | [],r => r
  | b::bs,r => cons b (pre bs r)
def rep (w : List Bool) : Nat → Ray → Ray
  | 0,r => r
  | n+1,r => pre w (rep w n r)
def P : List Bool := [false,true]
def Q : List Bool := [true,false]
def G : List Bool := [true,true,false,false]
def O : List Bool := [true]

theorem rep_add (w : List Bool) (n k : Nat) (r : Ray) :
    rep w (n+k) r = rep w n (rep w k r) := by
  induction n with
  | zero => simp [rep]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    simp only [rep,ih]
theorem rep_push (w : List Bool) (n : Nat) (r : Ray) :
    rep w n (pre w r) = rep w (n+1) r := by
  rw [rep_add]
  rfl
theorem zeroQ (n : Nat) (r : Ray) :
    cons false (rep Q n r) = rep P n (cons false r) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change cons false (cons true (cons false (rep Q n r))) =
      cons false (cons true (rep P n (cons false r)))
    rw [ih]
theorem Qblank (n : Nat) : rep Q (n+1) blank = cons true (rep P n blank) := by
  change cons true (cons false (rep Q n blank)) = _
  rw [zeroQ,zero_blank]

structure Cfg where
  q : Fin 6
  l : Ray
  r : Ray
def A (l r : Ray) : Cfg := ⟨0,l,r⟩
def C (l r : Ray) : Cfg := ⟨2,l,r⟩
def D (l r : Ray) : Cfg := ⟨3,l,r⟩
def E (l r : Ray) : Cfg := ⟨4,l,r⟩

def table (q : Fin 6) (b : Bool) : Option (Bool × Bool × Fin 6) :=
  match q.val,b with
  | 0,false => some (true,true,1)
  | 0,true => some (false,false,5)
  | 1,false => some (true,true,2)
  | 1,true => some (false,true,0)
  | 2,false => some (true,false,3)
  | 2,true => some (true,true,2)
  | 3,false => some (true,false,5)
  | 3,true => some (false,false,4)
  | 4,false => none
  | 4,true => some (false,true,3)
  | 5,false => some (true,false,0)
  | 5,true => some (false,false,3)
  | _,_ => none
def step (c : Cfg) : Option Cfg :=
  (table c.q (c.r 0)).map fun (w,d,q) =>
    if d then ⟨q,cons w c.l,tail c.r⟩
    else ⟨q,tail c.l,cons (c.l 0) (cons w (tail c.r))⟩
def run : Nat → Cfg → Option Cfg
  | 0,c => some c
  | n+1,c => (step c).bind (run n)
theorem run_add (n k : Nat) (c : Cfg) :
    run (n+k) c = (run n c).bind (run k) := by
  induction n generalizing c with
  | zero => simp [run]
  | succ n ih =>
    rw [show n+1+k=n+k+1 by omega]
    simp only [run]
    cases step c with
    | none => rfl
    | some t => exact ih t
abbrev Runs (n : Nat) (c d : Cfg) := run n c = some d
theorem chain {n m : Nat} {a b c : Cfg}
    (h : Runs n a b) (j : Runs m b c) : Runs (n+m) a c := by
  change run (n+m) a = some c
  change run n a = some b at h
  rw [run_add,h]; exact j

def S (k : Nat) (r : Ray) : Cfg := A blank (rep P k r)
theorem S_push (k : Nat) (r : Ray) : S k (pre P r) = S (k+1) r := by
  unfold S; rw [rep_push]

theorem rightP (k : Nat) (l r : Ray) :
    Runs (2*k) (A l (rep P k r)) (A (rep P k l) r) := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    have h : Runs 2 (A l (rep P (k+1) r)) (A (pre P l) (rep P k r)) := rfl
    have j := chain h (ih (pre P l))
    rw [rep_push] at j
    simp only [show 2*(k+1)=2+2*k by omega] at j
    exact j
theorem reverseP (k : Nat) (l r : Ray) :
    Runs (2*k) (A (rep P k l) (cons true r)) (A l (cons true (rep Q k r))) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    have h : Runs 2 (A (rep P (k+1) l) (cons true r))
        (A (rep P k l) (cons true (pre Q r))) := rfl
    have j := chain h (ih (pre Q r))
    rw [rep_push] at j
    simp only [show 2*(k+1)=2+2*k by omega] at j
    exact j
theorem reverseExit (k : Nat) (r : Ray) :
    Runs (2*k+2) (A (rep P k blank) (cons true r)) (S (k+1) (cons false r)) := by
  have h := reverseP k blank r
  have j : Runs 2 (A blank (cons true (rep Q k r)))
      (A blank (pre [false,true,false] (rep Q k r))) := rfl
  have h' := chain h j
  have he : pre [false,true,false] (rep Q k r) = rep P (k+1) (cons false r) := by
    change cons false (cons true (cons false (rep Q k r))) = _
    rw [zeroQ]
    rfl
  rw [he] at h'
  exact h'
theorem one (k : Nat) (r : Ray) :
    Runs (4*k+2) (S k (cons true r)) (S (k+1) (cons false r)) := by
  have h := chain (rightP k blank (cons true r)) (reverseExit k r)
  simp only [show 2*k+(2*k+2)=4*k+2 by omega] at h
  exact h

theorem cSweep (k : Nat) (l r : Ray) :
    Runs k (C l (rep O k r)) (C (rep O k l) r) := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    have h : Runs 1 (C l (rep O (k+1) r)) (C (pre O l) (rep O k r)) := rfl
    have j := chain h (ih (pre O l))
    rw [rep_push] at j
    simp only [show k+1=1+k by omega] at j
    exact j
theorem gSweep (k : Nat) (l r : Ray) :
    Runs (6*k) (A (rep O (4*k) l) (cons true r))
      (A l (cons true (rep G k r))) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    have h : Runs 6 (A (rep O (4*(k+1)) l) (cons true r))
        (A (rep O (4*k) l) (cons true (pre G r))) := by
      rw [show 4*(k+1)=4+4*k by omega,rep_add]
      rfl
    have j := chain h (ih (pre G r))
    rw [rep_push] at j
    simp only [show 6*(k+1)=6+6*k by omega] at j
    exact j
theorem dSweep (k : Nat) (l r : Ray) :
    Runs (2*k) (D (rep Q k l) (cons false r))
      (D l (cons false (rep P k r))) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    have h : Runs 2 (D (rep Q (k+1) l) (cons false r))
        (D (rep Q k l) (cons false (pre P r))) := rfl
    have j := chain h (ih (pre P r))
    rw [rep_push] at j
    simp only [show 2*(k+1)=2+2*k by omega] at j
    exact j
theorem dExit (k : Nat) (r : Ray) :
    Runs (2*k+2) (D (rep Q k blank) (cons false r))
      (S 0 (pre [false,true,true] (rep P k r))) := by
  have h := dSweep k blank r
  have j : Runs 2 (D blank (cons false (rep P k r)))
      (S 0 (pre [false,true,true] (rep P k r))) := rfl
  exact chain h j

-- Rightward scan followed by C's unary scan. The displayed ones include
-- the two written by A0,B0; no unknown right-tail cell is read.
theorem toC (k m : Nat) (r : Ray) :
    Runs (2*k+2+m) (S k (pre [false,false] (rep O m (cons false r))))
      (C (rep O (m+2) (rep P k blank)) (cons false r)) := by
  have h := rightP k blank (pre [false,false] (rep O m (cons false r)))
  have j : Runs 2 (A (rep P k blank) (pre [false,false] (rep O m (cons false r))))
      (C (rep O 2 (rep P k blank)) (rep O m (cons false r))) := rfl
  have g := chain (chain h j) (cSweep m (rep O 2 (rep P k blank)) (cons false r))
  rw [← rep_add] at g
  exact g
theorem initialPos (k d : Nat) (r : Ray) :
    Runs (2*k+d+8) (S k (pre [false,false] (rep O (d+1) (cons false r))))
      (A (rep O d (rep P k blank)) (pre [true,true,true,true] r)) := by
  have h := toC k (d+1) r
  have j : Runs 5 (C (rep O (d+1+2) (rep P k blank)) (cons false r))
      (A (rep O d (rep P k blank)) (pre [true,true,true,true] r)) := by
    rw [show d+1+2=3+d by omega,rep_add]
    rfl
  have g := chain h j
  simp only [show 2*k+2+(d+1)+5=2*k+d+8 by omega] at g
  exact g
theorem initialZero (k : Nat) (r : Ray) :
    Runs (2*(k+1)+7) (S (k+1) (pre [false,false,false] r))
      (A (cons true (rep P k blank)) (pre [false,true,true,true] r)) := by
  have h := toC (k+1) 0 r
  have j : Runs 5 (C (rep O 2 (rep P (k+1) blank)) (cons false r))
      (A (cons true (rep P k blank)) (pre [false,true,true,true] r)) := rfl
  have g := chain h j
  simp only [show 2*(k+1)+2+0+5=2*(k+1)+7 by omega] at g
  exact g
theorem initialG (k j s : Nat) (r : Ray) :
    Runs (2*k+10*j+s+8)
      (S k (pre [false,false] (rep O (4*j+s+1) (cons false r))))
      (A (rep O s (rep P k blank)) (cons true (rep G j (pre [true,true,true] r)))) := by
  have h := initialPos k (4*j+s) r
  have g := gSweep j (rep O s (rep P k blank)) (pre [true,true,true] r)
  have h' : Runs (2*k+(4*j+s)+8)
      (S k (pre [false,false] (rep O (4*j+s+1) (cons false r))))
      (A (rep O (4*j) (rep O s (rep P k blank))) (cons true (pre [true,true,true] r))) := by
    rw [← rep_add]; exact h
  have v := chain h' g
  simp only [show 2*k+(4*j+s)+8+6*j=2*k+10*j+s+8 by omega] at v
  exact v

theorem enterD (k : Nat) (r : Ray) :
    Runs 2 (A (cons true (rep P k blank)) (cons true r))
      (D (rep Q k blank) (pre [false,false,false] r)) := by
  cases k with
  | zero => rfl
  | succ k => rw [Qblank]; rfl
theorem enterDZero (k : Nat) (r : Ray) :
    Runs 6 (A (cons true (rep P k blank)) (pre [false,true,true] r))
      (D (rep Q k blank) (pre [false,false,false,true,false] r)) := by
  cases k with
  | zero => rfl
  | succ k => rw [Qblank]; rfl
theorem zeroTurn (k : Nat) (r : Ray) :
    Runs (2*k+8) (A (cons true (rep P k blank)) (pre [false,true,true] r))
      (S 0 (pre [false,true,true] (rep P k (pre [false,false,true,false] r)))) := by
  have h := enterDZero k r
  have j := dExit k (pre [false,false,true,false] r)
  have g := chain h j
  simp only [show 6+(2*k+2)=2*k+8 by omega] at g
  exact g

-- Full one-return formulas, with the suffix G=1100 kept in factored form.
theorem ret0 (k : Nat) (r : Ray) :
    Runs (4*(k+1)+13) (S (k+1) (pre [false,false,false] r))
      (S 0 (pre [false,true,true] (rep P k (pre [false,false,true,false,true] r)))) := by
  have h := initialZero k r
  have j := zeroTurn k (cons true r)
  have g := chain h j
  simp only [show 2*(k+1)+7+(2*k+8)=4*(k+1)+13 by omega] at g
  exact g
theorem ret4 (k j : Nat) (r : Ray) :
    Runs (4*(k+1)+13+10*(j+1))
      (S (k+1) (pre [false,false] (rep O (4*(j+1)) (cons false r))))
      (S 0 (pre [false,true,true] (rep P k
        (pre [false,false,true,false,false,false] (rep G j (pre [true,true,true] r)))))) := by
  have h := initialG (k+1) j 3 r
  have h' : Runs (2*(k+1)+10*j+3+8)
      (S (k+1) (pre [false,false] (rep O (4*(j+1)) (cons false r))))
      (A (pre [true,true,true,false] (cons true (rep P k blank)))
        (cons true (rep G j (pre [true,true,true] r)))) := by
    simp only [show 4*j+3+1=4*(j+1) by omega] at h
    exact h
  have turn : Runs 6 (A (pre [true,true,true,false] (cons true (rep P k blank)))
      (cons true (rep G j (pre [true,true,true] r))))
      (A (cons true (rep P k blank))
        (pre [false,true,true,false,false] (rep G j (pre [true,true,true] r)))) := rfl
  have z := zeroTurn k (pre [false,false] (rep G j (pre [true,true,true] r)))
  have g := chain (chain h' turn) z
  simp only [show 2*(k+1)+10*j+3+8+6+(2*k+8)=4*(k+1)+13+10*(j+1) by omega] at g
  exact g
theorem ret1 (k j : Nat) (r : Ray) :
    Runs (4*k+10+10*j)
      (S k (pre [false,false] (rep O (4*j+1) (cons false r))))
      (S (k+1) (cons false (rep G j (pre [true,true,true] r)))) := by
  have h := initialG k j 0 r
  have h' : Runs (2*k+10*j+8)
      (S k (pre [false,false] (rep O (4*j+1) (cons false r))))
      (A (rep P k blank) (cons true (rep G j (pre [true,true,true] r)))) := by
    simp only [Nat.add_zero] at h
    exact h
  have g := chain h' (reverseExit k (rep G j (pre [true,true,true] r)))
  simp only [show 2*k+10*j+8+(2*k+2)=4*k+10+10*j by omega] at g
  exact g
theorem ret2 (k j : Nat) (r : Ray) :
    Runs (4*k+13+10*j)
      (S k (pre [false,false] (rep O (4*j+2) (cons false r))))
      (S 0 (pre [false,true,true] (rep P k
        (pre [false,false] (rep G j (pre [true,true,true] r)))))) := by
  have h := initialG k j 1 r
  have h' : Runs (2*k+10*j+9)
      (S k (pre [false,false] (rep O (4*j+2) (cons false r))))
      (A (cons true (rep P k blank)) (cons true (rep G j (pre [true,true,true] r)))) := by
    simp only [show 4*j+1+1=4*j+2 by omega,show 2*k+10*j+1+8=2*k+10*j+9 by omega] at h
    exact h
  have g := chain (chain h' (enterD k (rep G j (pre [true,true,true] r))))
      (dExit k (pre [false,false] (rep G j (pre [true,true,true] r))))
  simp only [show 2*k+10*j+9+2+(2*k+2)=4*k+13+10*j by omega] at g
  exact g
theorem terminal3 (k j : Nat) (r : Ray) :
    Runs (2*k+13+10*j)
      (S k (pre [false,false] (rep O (4*j+3) (cons false r))))
      (E (rep Q k blank) (pre [false,false,false,false] (rep G j (pre [true,true,true] r)))) := by
  have h := initialG k j 2 r
  have h' : Runs (2*k+10*j+10)
      (S k (pre [false,false] (rep O (4*j+3) (cons false r))))
      (A (pre [true,true] (rep P k blank)) (cons true (rep G j (pre [true,true,true] r)))) := by
    simp only [show 4*j+2+1=4*j+3 by omega,show 2*k+10*j+2+8=2*k+10*j+10 by omega] at h
    exact h
  have t : Runs 3 (A (pre [true,true] (rep P k blank)) (cons true (rep G j (pre [true,true,true] r))))
      (E (rep Q k blank) (pre [false,false,false,false] (rep G j (pre [true,true,true] r)))) := by
    cases k with
    | zero => rfl
    | succ k => rw [Qblank]; rfl
  have g := chain h' t
  simp only [show 2*k+10*j+10+3=2*k+13+10*j by omega] at g
  exact g

def blankCfg : Cfg := A blank blank
theorem seed : Runs 13 blankCfg (S 3 blank) := rfl

#print axioms ret0
#print axioms ret4
#print axioms ret1
#print axioms ret2
#print axioms terminal3
#print axioms seed
end BB6.Agent3Leaf2265
