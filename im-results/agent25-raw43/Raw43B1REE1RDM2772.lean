import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B1REE1RDM2772
open BB6Coverage BB6Coverage.Agent31Pump

def table (v : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => if v then none else some (some ⟨true,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,false,if v then 5 else 2⟩)
  | 4,true => some (some ⟨true,true,3⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => if v then some (some ⟨true,false,5⟩) else none
  | _,_ => none

def P : Nat → List Bool
  | 0 => []
  | n+1 => true::false::P n
def Q : Nat → List Bool
  | 0 => []
  | n+1 => false::true::Q n
def R0 : Nat → List Bool
  | 0 => [false]
  | n+1 => false::true::true::true::R0 n
def R (m : Nat) := true::true::R0 m

def A (L : List Bool) (m : Nat) : Z0 := ⟨0,L,R m⟩
def tail (b : Bool) : List Bool := if b then [true] else []
def fwd (n : Nat) (b : Bool) (m : Nat) : Z0 :=
  A (true::true::(Q (2*n+(if b then 1 else 0))++tail b)) m
def rev (n : Nat) (b : Bool) (m : Nat) : Z0 :=
  A (P (2*n+(if b then 2 else 1))++true::tail b) m

theorem forward (v : Bool) (X : List Bool) (m : Nat) :
    run0 (table v) 14 (A (true::true::X) (m+1)) = some (A (true::true::false::true::false::true::X) m) := by
  cases m <;> cases v <;> rfl

theorem empty (v : Bool) (m : Nat) : run0 (table v) 12 (A [] (m+1)) = some (fwd 0 true m) := by
  cases m <;> cases v <;> rfl

theorem backward (v : Bool) (X : List Bool) (m : Nat) :
    run0 (table v) 4 (A (true::false::true::false::X) m) = some (A X (m+1)) := by
  cases v <;> rfl

theorem turn (v : Bool) (X : List Bool) :
    run0 (table v) 11 (A (true::true::X) 0) = some (A (true::false::true::X) 0) := by
  cases v <;> rfl

theorem q_shift (n : Nat) (X : List Bool) : true::(Q n++X) = P n++true::X := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [P,Q,List.cons_append]; rw [← ih]

theorem fwd_next (v : Bool) (n : Nat) (b : Bool) (m : Nat) :
    run0 (table v) 14 (fwd n b (m+1)) = some (fwd (n+1) b m) := by
  cases b
  · change run0 (table v) 14 (A (true::true::(Q (2*n)++[])) (m+1)) = some (A (true::true::(Q (2*(n+1))++[])) m)
    rw [show 2*(n+1)=2*n+2 by omega]
    exact forward v _ m
  · change run0 (table v) 14 (A (true::true::(Q (2*n+1)++[true])) (m+1)) = some (A (true::true::(Q (2*(n+1)+1)++[true])) m)
    rw [show 2*(n+1)+1=2*n+1+2 by omega]
    exact forward v _ m

theorem fwd_turn (v : Bool) (n : Nat) (b : Bool) :
    run0 (table v) 11 (fwd n b 0) = some (rev n b 0) := by
  cases b
  · change run0 (table v) 11 (A (true::true::(Q (2*n)++[])) 0) = some (A (P (2*n+1)++[true]) 0)
    calc
      _ = some (A (true::false::true::(Q (2*n)++[])) 0) := turn v _
      _ = _ := by rw [q_shift]; rfl
  · change run0 (table v) 11 (A (true::true::(Q (2*n+1)++[true])) 0) = some (A (P (2*n+2)++[true,true]) 0)
    calc
      _ = some (A (true::false::true::(Q (2*n+1)++[true])) 0) := turn v _
      _ = _ := by rw [q_shift]; rfl

theorem rev_next (v : Bool) (n : Nat) (b : Bool) (m : Nat) :
    run0 (table v) 4 (rev (n+1) b m) = some (rev n b (m+1)) := by
  cases b
  · unfold rev; simp only [Bool.false_eq_true,if_false,tail]
    rw [show 2*(n+1)+1=(2*n+1)+2 by omega]
    exact backward v _ m
  · unfold rev; simp only [if_true,tail]
    rw [show 2*(n+1)+2=(2*n+2)+2 by omega]
    exact backward v _ m

theorem rev_odd_end (v : Bool) (m : Nat) :
    run0 (table v) 4 (rev 0 false m) = some (A [] (m+1)) := by cases v <;> rfl

theorem rev_even_end (v : Bool) (m : Nat) :
    run0 (table v) 4 (rev 0 true m) = some (fwd 0 false (m+1)) := by cases v <;> rfl

inductive Inv : Z0 → Prop
  | emp (m : Nat) : Inv (A [] (m+1))
  | fw (n : Nat) (b : Bool) (m : Nat) : Inv (fwd n b m)
  | rv (n : Nat) (b : Bool) (m : Nat) : Inv (rev n b m)

theorem stepInv (v : Bool) (z : Z0) (h : Inv z) : ∃ t z', 0<t ∧ run0 (table v) t z=some z' ∧ Inv z' := by
  cases h with
  | emp m => exact ⟨12,_,by omega,empty v m,Inv.fw 0 true m⟩
  | fw n b m => cases m with
    | zero => exact ⟨11,_,by omega,fwd_turn v n b,Inv.rv n b 0⟩
    | succ m => exact ⟨14,_,by omega,fwd_next v n b m,Inv.fw (n+1) b m⟩
  | rv n b m => cases n with
    | zero => cases b with
      | false => exact ⟨4,_,by omega,rev_odd_end v m,Inv.emp m⟩
      | true => exact ⟨4,_,by omega,rev_even_end v m,Inv.fw 0 false (m+1)⟩
    | succ n => exact ⟨4,_,by omega,rev_next v n b m,Inv.rv n b (m+1)⟩

theorem start (v : Bool) : run0 (table v) 18 ⟨0,[],[]⟩ = some (A [] 1) := by cases v <;> rfl

theorem live (v : Bool) (N : Nat) : ∃ t z, N≤t ∧ run0 (table v) t ⟨0,[],[]⟩ = some z ∧ Inv z := by
  induction N with
  | zero => exact ⟨18,_,by omega,start v,Inv.emp 0⟩
  | succ N ih =>
    obtain ⟨t,z,ht,hz,hi⟩ := ih
    obtain ⟨a,z',ha,hr,hi'⟩ := stepInv v z hi
    exact ⟨t+a,z',by omega,join0 hz hr,hi'⟩

open BB6Coverage.Agent50Zipper

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr,_⟩ := live v n
  let start : Z := ⟨0,0,[],[]⟩
  have hz : (zrun (table v) t start).map project = some z :=
    (run_project (table v) t start).trans hr
  cases hZ : zrun (table v) t start with
  | none => simp [hZ] at hz
  | some z' =>
    have H := zrun_sound (table v) m hm t start z' hZ
    have hb : embed start = blank := by
      unfold embed blank
      congr 1
      funext x
      unfold atCell start
      split <;> rfl
    rw [hb] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl
#print axioms never
end BB6.Agent25Raw43B1REE1RDM2772
