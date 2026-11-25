import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace BB6.Agent8Raw112Unary
open BB6Coverage BB6Coverage.Agent31Pump

-- Leaf 7885: 1RB0LF_1RC---_0RD1LE_1LD1RE_0RA1LC_0LA1RA
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨true,false,2⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

abbrev O (n : Nat) := List.replicate n true
abbrev E (n : Nat) (R : List Bool) : Z0 := ⟨4,O n,R⟩
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev D (n : Nat) : Z0 := ⟨3,[false,false,true,true,false,true,false,true]++O n,[]⟩
def X (k j : Nat) : Z0 := A [] (false::false::(O k ++ false::O j))
def Reach (x y : Z0) : Prop := ∃ t : Nat, run0 table t x = some y

theorem reachJoin {x y z : Z0} (h : Reach x y) (g : Reach y z) : Reach x z := by
  obtain ⟨t,h⟩ := h; obtain ⟨u,g⟩ := g
  exact ⟨t+u,join0 h g⟩

theorem oAppend (n : Nat) (R : List Bool) : O n ++ true::R = O (n+1) ++ R := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun x => true::x) ih

theorem ePair (n : Nat) (R : List Bool) : run0 table 2 (E (n+2) R) = some (E n (true::true::R)) := by rfl

theorem eFinish (n : Nat) (R : List Bool) : Reach (E n (true::true::true::R)) (A [] (false::false::(O (n+2)++R))) := by
  induction n using Nat.strongRecOn generalizing R with
  | ind n ih =>
    cases n with
    | zero => exact ⟨3,rfl⟩
    | succ n =>
      cases n with
      | zero => exact ⟨8,rfl⟩
      | succ n =>
        have h := ePair n (true::true::true::R)
        have g := ih n (by omega) (true::true::R)
        have eq : O (n+2) ++ (true::true::R) = O (n+1+1+2)++R := by
          rw [oAppend (n+2) (true::R), oAppend (n+2+1) R]
        rw [eq] at g
        exact reachJoin ⟨2,h⟩ g

theorem transfer (L R : List Bool) : run0 table 11 (A (false::L) (false::false::true::true::R)) = some (A (false::true::L) (false::false::true::R)) := by rfl

theorem transferBlank (R : List Bool) : run0 table 11 (A [] (false::false::true::true::R)) = some (A [false,true] (false::false::true::R)) := by rfl

theorem sweep (n k : Nat) (R : List Bool) : run0 table (11*n) (A (false::O k) (false::false::(O (n+1)++R))) = some (A (false::O (k+n)) (false::false::true::R)) := by
  induction n generalizing k with
  | zero => simp [run0]
  | succ n ih =>
    have h := transfer (O k) (O n++R)
    have g := join0 h (ih (k+1))
    rw [show 11+11*n=11*(n+1) by omega,show k+1+n=k+(n+1) by omega] at g
    exact g

theorem sweepBlank (n : Nat) (R : List Bool) : run0 table (11*(n+1)) (A [] (false::false::(O (n+2)++R))) = some (A (false::O (n+1)) (false::false::true::R)) := by
  have h := transferBlank (O n++R)
  have g := join0 h (sweep n 1 R)
  rw [show 11+11*n=11*(n+1) by omega,show 1+n=n+1 by omega] at g
  exact g

theorem xStep (n j : Nat) : Reach (X (n+2) (j+1)) (X (n+5) j) := by
  have h := sweepBlank n (false::O (j+1))
  have h2 : run0 table 19 (A (false::O (n+1)) (false::false::true::false::true::O j)) = some (E (n+3) (true::true::true::false::O j)) := by rfl
  have g := eFinish (n+3) (false::O j)
  have eq : n+3+2=n+5 := by omega
  rw [eq] at g
  exact reachJoin ⟨_,join0 h h2⟩ g

theorem xFinish (n : Nat) : Reach (X (n+2) 0) (D (n+2)) := by
  have h := sweepBlank n [false]
  have h2 : run0 table 8 (A (false::O (n+1)) [false,false,true,false]) = some (D (n+2)) := by rfl
  exact ⟨_,join0 h h2⟩

theorem start (n : Nat) : run0 table 25 (D (n+1)) = some (E (n+2) [true,true,true,false,true,true,true]) := by rfl

def family (n : Nat) : Z0 := D (12*n+3)
theorem entry : run0 table 46 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth (n : Nat) : ∃ t : Nat, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  let k := 12*n+2
  have h := start k
  have g1 := eFinish (k+2) [false,true,true,true]
  have g2 := xStep (k+2) 2
  have g3 := xStep (k+5) 1
  have g4 := xStep (k+8) 0
  have g5 := xFinish (k+11)
  have g := reachJoin g1 (reachJoin g2 (reachJoin g3 (reachJoin g4 g5)))
  obtain ⟨u,g⟩ := g
  have H := join0 h g
  have e1 : k+1=12*n+3 := by rfl
  have e2 : k+11+2=12*(n+1)+3 := by dsimp [k]; omega
  rw [e1,e2] at H
  exact ⟨_,by omega,H⟩

noncomputable def cost (n : Nat) : Nat := Classical.choose (growth n)
theorem cost_pos (n : Nat) : 0<cost n := (Classical.choose_spec (growth n)).1
theorem cost_run (n : Nat) : run0 table (cost n) (family n) = some (family (n+1)) := (Classical.choose_spec (growth n)).2
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 46 cost entry cost_pos cost_run m hm

#print axioms growth
#print axioms never
end BB6.Agent8Raw112Unary
