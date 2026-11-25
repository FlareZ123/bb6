import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Q32Cubic
open BB6Coverage

def table : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨false,false,1⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none

def ones (n : Nat) : List Bool := rep [true] n
@[simp] theorem ones_succ (n : Nat) : ones (n+1) = true :: ones n := rfl
@[simp] theorem ones_zero : ones 0 = [] := rfl
theorem ones_add (n k : Nat) : ones n ++ ones k = ones (n+k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ones_succ, List.cons_append, ih, show n+1+k=n+k+1 by omega, ones_succ]

theorem leftSweep (n : Nat) (L R : List Bool) :
    run0 table n ⟨1,ones n ++ L,R⟩ = some ⟨1,L,ones n ++ R⟩ := by
  simpa only [ones,Nat.one_mul,List.nil_append] using
    sweepL table 1 [] [] [true] [true] 1 (by intro L R; rfl) n L R

theorem rightSweep (n : Nat) (L R : List Bool) :
    run0 table n ⟨4,true :: L,ones n ++ R⟩ =
      some ⟨4,true :: (ones n ++ L),R⟩ := by
  simpa only [ones,Nat.one_mul,List.nil_append,List.cons_append] using
    sweepR table 4 [true] [] [true] [true] 1 (by intro L R; rfl) n L R

def inner (i n k : Nat) : Z0 :=
  ⟨1,false :: ones i,ones (2*n+2) ++ false :: ones k⟩
def family (n : Nat) : Z0 := ⟨1,[],ones (2*n+4)⟩
theorem entry : run0 table 18 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem innerStep (i n k : Nat) :
    run0 table (4*n+11) (inner i (n+1) k) = some (inner (i+1) n (k+1)) := by
  have h1 : run0 table 2 (inner i (n+1) k) =
      some ⟨4,true::false::true::ones i,ones (2*n+2) ++ false::ones k⟩ := by
    unfold inner
    rw [show 2*(n+1)+2=2*n+4 by omega]
    rfl
  have h2 := rightSweep (2*n+2) (false::true::ones i) (false::ones k)
  have h3 : run0 table 5
      ⟨4,true::(ones (2*n+2) ++ false::true::ones i),false::ones k⟩ =
      some ⟨1,ones (2*n+2) ++ false::true::ones i,false::true::ones k⟩ := by rfl
  have h4 := leftSweep (2*n+2) (false::true::ones i) (false::true::ones k)
  have H := join0 (join0 (join0 h1 h2) h3) h4
  rw [show 2+(2*n+2)+5+(2*n+2)=4*n+11 by omega] at H
  simpa only [inner,ones_succ] using H

theorem firstSweep (n : Nat) :
    run0 table (4*n+11) (family n) = some (inner 1 n 1) := by
  have h1 : run0 table 2 (family n) =
      some ⟨4,[true,false,true],ones (2*n+2)⟩ := by rfl
  have h2 : run0 table (2*n+2) ⟨4,[true,false,true],ones (2*n+2)⟩ =
      some ⟨4,true::(ones (2*n+2) ++ [false,true]),[]⟩ := by
    simpa only [List.append_nil] using rightSweep (2*n+2) [false,true] []
  have h3 : run0 table 5
      ⟨4,true::(ones (2*n+2) ++ [false,true]),[]⟩ =
      some ⟨1,ones (2*n+2) ++ [false,true],[false,true]⟩ := by rfl
  have h4 := leftSweep (2*n+2) [false,true] [false,true]
  have H := join0 (join0 (join0 h1 h2) h3) h4
  rw [show 2+(2*n+2)+5+(2*n+2)=4*n+11 by omega] at H
  exact H

theorem finishSweep (i k : Nat) :
    run0 table (i+9) (inner i 0 k) = some ⟨1,[],ones (i+k+4)⟩ := by
  have h1 : run0 table 6 (inner i 0 k) =
      some ⟨1,ones (i+3),ones (k+1)⟩ := by rfl
  have h2 := leftSweep (i+3) [] (ones (k+1))
  simp only [List.append_nil,ones_add] at h2
  have H := join0 h1 h2
  rw [show 6+(i+3)=i+9 by omega,show i+3+(k+1)=i+k+4 by omega] at H
  exact H

def innerCost : Nat → Nat
  | 0 => 0
  | n+1 => 4*n+11 + innerCost n

theorem innerIter (n i k : Nat) :
    run0 table (innerCost n) (inner i n k) = some (inner (i+n) 0 (k+n)) := by
  induction n generalizing i k with
  | zero => simp [innerCost,run0]
  | succ n ih =>
    have H := join0 (innerStep i n k) (ih (i+1) (k+1))
    simpa only [innerCost,show i+1+n=i+(n+1) by omega,
      show k+1+n=k+(n+1) by omega] using H

def cost (n : Nat) : Nat := 4*n+11 + innerCost n + (n+10)

theorem growth (n : Nat) :
    run0 table (cost n) (family n) = some (family (n+1)) := by
  have H := join0 (join0 (firstSweep n) (innerIter n 1 1)) (finishSweep (1+n) (1+n))
  simpa only [cost,family,show 1+n+9=n+10 by omega,
    show 1+n+(1+n)+4=2*(n+1)+4 by omega] using H

theorem innerCost_formula (n : Nat) : innerCost n = 2*n*n+9*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [innerCost,ih]
    simp only [Nat.mul_succ,Nat.add_mul]
    omega

theorem cost_formula (n : Nat) : cost n = 2*n*n+14*n+21 := by
  rw [cost,innerCost_formula]
  omega

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 18 cost entry (by
    intro n
    unfold cost
    omega) growth m hm

#print axioms growth
#print axioms cost_formula
#print axioms never
end BB6Coverage.Agent31Pump.Q32Cubic
