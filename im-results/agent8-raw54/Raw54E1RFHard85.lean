import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.E1RF.M85
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none

def Z : List Bool := [false,false,false,false]
def X : List Bool := [true,false,true,true]
def Y : List Bool := [false,true,true,true]
def W : List Bool := [true,true,true,true]
def T : List Bool := [true,true,true]
def U : List Bool := [false,false,false]
def sec (r : List Bool) : Z0 := ⟨0,[false],T++r⟩
def work (n : Nat) (q : Fin 6) (r : List Bool) : Z0 :=
  ⟨q,T++rep W n++[false],r⟩

theorem prep (n : Nat) (r : List Bool) :
    run0 table (5+4*n) (sec (rep W n++r)) = some (work n 5 r) := by
  have h1 (R : List Bool) : run0 table 5 (sec R) = some ⟨5,T++[false],R⟩ := by rfl
  have h2 := sweepR table 5 T [] W W 4 (fun _ _ => rfl) n [false] r
  exact join0 (h1 (rep W n++r)) (by simpa only [work,List.append_assoc,List.append_nil,List.nil_append] using h2)

theorem finish (n : Nat) (r : List Bool) :
    run0 table (4*n+13) (work n 0 r) = some (sec (rep Z n++r)) := by
  have h1 := sweepL table 0 T [] W Z 4 (fun _ _ => rfl) n [false] r
  have h2 (R : List Bool) : run0 table 13 ⟨0,T++[false],R⟩ = some (sec R) := by rfl
  exact join0 (by simpa only [work,List.append_assoc,List.append_nil,List.nil_append] using h1) (h2 (rep Z n++r))

theorem middleCarry (n k : Nat) (a b : List Bool)
    (h : ∀ L R, run0 table k ⟨5,T++L,a++R⟩ = some ⟨0,T++L,b++R⟩)
    (r : List Bool) : run0 table (8*n+k+18) (sec (rep W n++a++r)) =
      some (sec (rep Z n++b++r)) := by
  have h1 := prep n (a++r)
  have h2 := h (rep W n++[false]) r
  have h3 := finish n (b++r)
  have h12 := join0 h1 (by simpa only [work,List.append_assoc] using h2)
  have H := join0 h12 h3
  rw [show 5+4*n+k+(4*n+13)=8*n+k+18 by omega] at H
  simpa only [List.append_assoc] using H

theorem zeroCarry (n : Nat) (r : List Bool) :
    run0 table (8*n+26) (sec (rep W n++Z++r)) = some (sec (rep Z n++X++r)) := by
  simpa only [show 8*n+8+18=8*n+26 by omega] using middleCarry n 8 Z X (fun _ _ => rfl) r

theorem oneCarry (n : Nat) (r : List Bool) :
    run0 table (8*n+24) (sec (rep W n++X++r)) = some (sec (rep Z n++Y++r)) := by
  simpa only [show 8*n+6+18=8*n+24 by omega] using middleCarry n 6 X Y (fun _ _ => rfl) r

theorem twoCarry (n : Nat) (r : List Bool) :
    run0 table (8*n+22) (sec (rep W n++Y++r)) = some (sec (rep Z n++W++r)) := by
  simpa only [show 8*n+4+18=8*n+22 by omega] using middleCarry n 4 Y W (fun _ _ => rfl) r

theorem overflow (n : Nat) :
    run0 table (8*n+26) (sec (rep W n)) = some (sec (rep Z n++X)) := by
  have h1 := prep n []
  have h2 (L : List Bool) : run0 table 8 ⟨5,T++L,[]⟩ = some ⟨0,T++L,X⟩ := by rfl
  have h12 := join0 h1 (by simpa only [work,List.append_assoc] using h2 (rep W n++[false]))
  have H := join0 h12 (finish n X)
  rw [show 5+4*n+8+(4*n+13)=8*n+26 by omega] at H
  simpa only [List.append_nil] using H

inductive Digit where
  | zero | one | two | three

def digits : List Digit → List Bool
  | [] => []
  | .zero::bs => Z++digits bs
  | .one::bs => X++digits bs
  | .two::bs => Y++digits bs
  | .three::bs => W++digits bs

def increment : List Digit → List Digit
  | [] => [.one]
  | .zero::bs => .one::bs
  | .one::bs => .two::bs
  | .two::bs => .three::bs
  | .three::bs => .zero::increment bs

def cost : List Digit → Nat
  | [] => 26
  | .zero::_ => 26
  | .one::_ => 24
  | .two::_ => 22
  | .three::bs => cost bs + 8

theorem carryWord (bs : List Digit) (n : Nat) :
    run0 table (8*n+cost bs) (sec (rep W n++digits bs)) =
      some (sec (rep Z n++digits (increment bs))) := by
  induction bs generalizing n with
  | nil => simpa only [digits,cost,increment,List.append_nil] using overflow n
  | cons b bs ih =>
    cases b with
    | zero => simpa only [digits,cost,increment,List.append_assoc] using zeroCarry n (digits bs)
    | one => simpa only [digits,cost,increment,List.append_assoc] using oneCarry n (digits bs)
    | two => simpa only [digits,cost,increment,List.append_assoc] using twoCarry n (digits bs)
    | three =>
      have h := ih (n+1)
      rw [show 8*(n+1)+cost bs=8*n+(cost bs+8) by omega] at h
      simp only [rep,digits,increment,cost,List.append_assoc] at h ⊢
      simpa only [← List.append_assoc W (rep W n),← rep_snoc W n,
        ← List.append_assoc Z (rep Z n),← rep_snoc Z n,List.append_assoc] using h

def orbit : Nat → List Digit
  | 0 => []
  | n+1 => increment (orbit n)
def family (n : Nat) : Z0 := sec (digits (orbit n))
theorem positive (bs : List Digit) : 0 < cost bs := by
  cases bs with
  | nil => decide
  | cons b bs => cases b <;> simp [cost] <;> omega

theorem entry : run0 table 10 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) : run0 table (cost (orbit n)) (family n) = some (family (n+1)) := by
  simpa [family,orbit,rep] using carryWord (orbit n) 0

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 10 (fun n => cost (orbit n)) entry (fun n => positive (orbit n)) growth m hm
#print axioms carryWord
#print axioms never
end BB6.Agent8Raw54.E1RF.M85
