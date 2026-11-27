import PadGrowth
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6OneLFAlternating
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent6PadGrowth

/-- The three tables differ only in B1. D0 is not assigned. -/
def p (b : Move) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some b)
  | 2,false => some (some ⟨true,false,3⟩)
  | 2,true => some (some ⟨false,false,0⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none

def e : Move := ⟨false,false,4⟩
def f : Move := ⟨false,true,5⟩
def d : Move := ⟨true,false,3⟩
def x : List Bool := [true,false,true,false]
def y : List Bool := [false,true,false,true]
def X (n : Nat) := rep x n
def Y (n : Nat) := rep y n

theorem Y_snoc (n : Nat) : Y (n+1) = Y n ++ y := (rep_snoc y n).symm

def A (m : Nat) (T : List Bool) : Z0 := ⟨0,[],Y (m+1)++T⟩
def turn (m : Nat) (T : List Bool) : Z0 := ⟨0,[false,false,true]++Y m,[false,true]++T⟩
def C (m : Nat) (T : List Bool) : Z0 := ⟨2,[false,true]++Y m,T⟩

-- Each finite rule is a computation with arbitrary untouched tails.
theorem right4 (b : Move) (L R : List Bool) :
    run0 (p b) 4 ⟨0,[false]++L,[false,true,false]++R⟩ =
      some ⟨0,[false,false,true]++L,[false]++R⟩ := rfl
theorem right8 (b : Move) (L R : List Bool) :
    run0 (p b) 8 ⟨0,[false]++L,[false]++x++R⟩ =
      some ⟨0,[false]++y++L,[false]++R⟩ := rfl
theorem left4 (b : Move) (L R : List Bool) :
    run0 (p b) 4 ⟨2,[false,true]++y++L,[]++R⟩ =
      some ⟨2,[false,true]++L,[]++y++R⟩ := rfl
theorem finish4 (b : Move) (R : List Bool) :
    run0 (p b) 4 ⟨2,[false,true],R⟩ = some ⟨0,[],y++R⟩ := rfl

theorem A_right (m : Nat) (T : List Bool) :
    [false]++X m++([true,false,true]++T) = Y (m+1)++T := by
  have h := rotate false [true,false,true] m
  change [false]++X m=Y m++[false] at h
  rw [h,Y_snoc]
  simp only [y,List.append_assoc,List.cons_append,List.nil_append]

theorem rightPhase (b : Move) (m : Nat) (T : List Bool) :
    Reach (p b) (8*m+4) (A m T) (turn m T) := by
  have h := sweepR (p b) 0 [false] [false] x y 8 (right8 b) m [] ([true,false,true]++T)
  have h' : run0 (p b) (8*m) ⟨0,[false],[false]++X m++([true,false,true]++T)⟩ =
      some ⟨0,[false]++Y m,[false,true,false,true]++T⟩ := by
    simpa only [X,Y,List.append_nil,List.append_assoc,List.cons_append,List.nil_append] using h
  have H := join0 h' (right4 b (Y m) ([true]++T))
  rw [A_right] at H
  apply padRun (exactRun H) _ (eqZ_refl _)
  exact ⟨rfl,by intro i; cases i <;> rfl,fun _ => rfl⟩

theorem leftPhase (b : Move) (m : Nat) (T : List Bool) :
    run0 (p b) (4*m+4) (C m T) = some (A m T) := by
  have h := sweepL (p b) 2 [false,true] [] y y 4 (left4 b) m [] T
  have h' : run0 (p b) (4*m) (C m T) = some ⟨2,[false,true],Y m++T⟩ := by
    simpa only [C,Y,List.append_nil,List.nil_append] using h
  exact join0 h' (finish4 b (Y m++T))

theorem turn1 (b : Move) (m : Nat) :
    run0 (p b) 9 (turn m []) = some (C (m+1) [true]) := rfl
theorem turnE2 (m : Nat) :
    run0 (p e) 7 (turn m [true]) = some (C (m+1) []) := rfl
theorem turnD2 (m : Nat) :
    run0 (p d) 9 (turn m [true]) = some (C m y) := rfl
theorem turnF2 (m : Nat) :
    run0 (p f) 15 (turn m [true]) = some (C (m+1) [true,true]) := rfl
theorem turnF3 (m : Nat) :
    run0 (p f) 7 (turn m [true,true]) = some (C (m+1) [false]) := rfl

theorem block_extra (m : Nat) : A m y = A (m+1) [] := by
  simp only [A,List.append_nil,Y_snoc (m+1)]

theorem drop_zero (L : List Bool) : EqW (L++[false]) L := by
  intro i
  induction L generalizing i with
  | nil => cases i <;> rfl
  | cons b L ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem advance1 (b : Move) (m : Nat) :
    Reach (p b) (12*m+21) (A m []) (A (m+1) [true]) := by
  have h := join (join (rightPhase b m []) (exactRun (turn1 b m))) (exactRun (leftPhase b (m+1) [true]))
  rw [show 8*m+4+9+(4*(m+1)+4)=12*m+21 by omega] at h
  exact h

theorem advanceE2 (m : Nat) :
    Reach (p e) (12*m+19) (A m [true]) (A (m+1) []) := by
  have h := join (join (rightPhase e m [true]) (exactRun (turnE2 m))) (exactRun (leftPhase e (m+1) []))
  rw [show 8*m+4+7+(4*(m+1)+4)=12*m+19 by omega] at h
  exact h

theorem advanceD2 (m : Nat) :
    Reach (p d) (12*m+17) (A m [true]) (A (m+1) []) := by
  have h := join (join (rightPhase d m [true]) (exactRun (turnD2 m))) (exactRun (leftPhase d m y))
  rw [show 8*m+4+9+(4*m+4)=12*m+17 by omega,block_extra] at h
  exact h

theorem advanceF2 (m : Nat) :
    Reach (p f) (12*m+27) (A m [true]) (A (m+1) [true,true]) := by
  have h := join (join (rightPhase f m [true]) (exactRun (turnF2 m))) (exactRun (leftPhase f (m+1) [true,true]))
  rw [show 8*m+4+15+(4*(m+1)+4)=12*m+27 by omega] at h
  exact h

theorem advanceF3 (m : Nat) :
    Reach (p f) (12*m+19) (A m [true,true]) (A (m+1) []) := by
  have h := join (join (rightPhase f m [true,true]) (exactRun (turnF3 m))) (exactRun (leftPhase f (m+1) [false]))
  rw [show 8*m+4+7+(4*(m+1)+4)=12*m+19 by omega] at h
  apply padRun h (eqZ_refl _) _
  exact ⟨rfl,fun _ => rfl,by simpa only [A,List.append_nil] using drop_zero (Y (m+1+1))⟩

theorem seed (b : Move) : run0 (p b) 9 ⟨0,[],[]⟩ = some (A 0 [true]) := rfl

def familyED (k : Nat) := A (2*k) [true]
def familyF (k : Nat) := A (3*k) [true]

theorem growthE (k : Nat) :
    Reach (p e) (48*k+52) (familyED k) (familyED (k+1)) := by
  have h := join (advanceE2 (2*k)) (advance1 e (2*k+1))
  rw [show 12*(2*k)+19+(12*(2*k+1)+21)=48*k+52 by omega,
    show 2*k+1+1=2*(k+1) by omega] at h
  exact h

theorem growthD (k : Nat) :
    Reach (p d) (48*k+50) (familyED k) (familyED (k+1)) := by
  have h := join (advanceD2 (2*k)) (advance1 d (2*k+1))
  rw [show 12*(2*k)+17+(12*(2*k+1)+21)=48*k+50 by omega,
    show 2*k+1+1=2*(k+1) by omega] at h
  exact h

theorem growthF (k : Nat) :
    Reach (p f) (108*k+103) (familyF k) (familyF (k+1)) := by
  have h := join (join (advanceF2 (3*k)) (advanceF3 (3*k+1))) (advance1 f (3*k+1+1))
  rw [show 12*(3*k)+27+(12*(3*k+1)+19)+(12*(3*k+1+1)+21)=108*k+103 by omega,
    show 3*k+1+1+1=3*(k+1) by omega] at h
  exact h

theorem neverE (m : Machine) (hm : compatible (p e) m) : NeverHalts m :=
  never_of_pad_growth (p e) familyED 9 (fun k => 48*k+52) (exactRun (seed e))
    (by intro k; omega) growthE m hm
theorem neverD (m : Machine) (hm : compatible (p d) m) : NeverHalts m :=
  never_of_pad_growth (p d) familyED 9 (fun k => 48*k+50) (exactRun (seed d))
    (by intro k; omega) growthD m hm
theorem neverF (m : Machine) (hm : compatible (p f) m) : NeverHalts m :=
  never_of_pad_growth (p f) familyF 9 (fun k => 108*k+103) (exactRun (seed f))
    (by intro k; omega) growthF m hm

#print axioms neverE
#print axioms neverD
#print axioms neverF
end BB6.Agent6OneLFAlternating
