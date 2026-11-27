import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw49Nested261066
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none

def C (L R : List Bool) : Z0 := ⟨2,L,R⟩
def pre : List Bool := [true,true,false,false,true,true]
def p1 : List Bool := pre ++ [true,false,false,true,true,true]
def p2 : List Bool := pre ++ [true]
def b : List Bool := [false,true,true]
def u : List Bool := [true,true,true]
def rightFrame : List Bool := false :: List.replicate 10 true

theorem first (L : List Bool) : run0 table 53 (C (pre++b++L) []) = some (C (p1++L) []) := by rfl
theorem second (L : List Bool) : run0 table 84 (C (p1++b++L) []) = some (C (p2++L) rightFrame) := by rfl
theorem leftOne (L R : List Bool) : run0 table 35 ⟨2,p2++b++L,rightFrame++R⟩ = some ⟨2,p2++L,rightFrame++u++R⟩ := by rfl
theorem turn (R : List Bool) : run0 table 84 (C p2 (rightFrame++R)) = some (C pre (rep u 5++R)) := by rfl
theorem rightOne (L R : List Bool) : run0 table 13 ⟨2,pre++L,[]++u++R⟩ = some ⟨2,pre++b++L,[]++R⟩ := by rfl

theorem rep_add (P : List Bool) (a n : Nat) : rep P (a+n) = rep P a ++ rep P n := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [Nat.succ_add]; simp only [rep,ih,List.append_assoc]

def F (n : Nat) := C (pre++rep b (n+2)) []

theorem growthF (n : Nat) : run0 table (286+48*n) (F n) = some (F (n+3)) := by
  have h0 : run0 table 53 (F n) = some (C (p1++b++rep b n) []) := by
    simpa only [F,rep,List.append_assoc] using first (b++rep b n)
  have h1 := second (rep b n)
  have h2 : run0 table (35*n) (C (p2++rep b n) rightFrame) = some (C p2 (rightFrame++rep u n)) := by
    simpa only [C,List.append_nil] using sweepL table 2 p2 rightFrame b u 35 leftOne n [] []
  have h3 := turn (rep u n)
  have h4 : run0 table (13*(5+n)) (C pre (rep u 5++rep u n)) = some (C (pre++rep b (5+n)) []) := by
    rw [← rep_add]
    simpa only [C,List.append_nil,List.nil_append] using sweepR table 2 pre [] u b 13 rightOne (5+n) [] []
  have h := join0 (join0 (join0 (join0 h0 h1) h2) h3) h4
  rw [show 53+84+35*n+84+13*(5+n)=286+48*n by omega] at h
  simpa only [F,show 5+n=n+3+2 by omega] using h

def family (n : Nat) := F (3*n+1)
theorem entry : run0 table 219 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) : run0 table (334+144*n) (family n) = some (family (n+1)) := by
  have h := growthF (3*n+1)
  rw [show 286+48*(3*n+1)=334+144*n by omega,show 3*n+1+3=3*(n+1)+1 by omega] at h
  exact h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 219 (fun n => 334+144*n) entry (by intro n; omega) growth m hm
#print axioms never
end BB6.Agent7Raw49Nested261066
