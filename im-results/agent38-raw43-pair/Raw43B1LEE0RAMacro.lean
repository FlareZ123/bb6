import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent38Raw43B1LEE0RA
open BB6Coverage BB6Coverage.Agent31Pump

/-!
Exact unbounded sweep recurrence for Raw43/B1LE/E0RA residual 192:
  1RB1LF_1RC1LE_0RD0RC_1LD0RB_0RA---_0LA1LB

The only unassigned row is E1.  The recurrence stays on E0 and never queries it.
At family index n (physical marker k=n+3), the machine returns to E on a fresh
zero after exactly 30*n+97 steps.  Six unary C1/D0 sweeps account for the
linear cost; all turnarounds are fixed finite computations.
-/

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true  => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true  => some (some ⟨true,false,1⟩)
  | _,_ => none

def zeros (n : Nat) : List Bool := rep [false] n
def ones (n : Nat) : List Bool := rep [true] n

/-- E on the fresh zero at physical marker k=n+3. -/
def family (n : Nat) : Z0 :=
  ⟨4,[false,false,false,true,true,false] ++ ones (n+1),ones (5*n+6)⟩

/-- C1=0RC sweeps right, replacing each consumed 1 behind the head by 0. -/
theorem sweepC (n : Nat) (L R : List Bool) :
    run0 table n ⟨2,[true]++L,ones n++R⟩ =
      some ⟨2,[true]++zeros n++L,R⟩ := by
  have one : ∀ L R, run0 table 1 ⟨2,[true]++L,[true]++R⟩ =
      some ⟨2,[true,false]++L,R⟩ := by
    intro L R
    rfl
  have h := sweepR table 2 [true] [] [true] [false] 1 one n L R
  simpa [zeros,ones] using h

/-- D0=1LD sweeps left, replacing each consumed 0 on the right by 1. -/
theorem sweepD (n : Nat) (L R : List Bool) :
    run0 table n ⟨3,zeros n++L,R⟩ =
      some ⟨3,L,ones n++R⟩ := by
  have one : ∀ L R, run0 table 1 ⟨3,[false]++L,R⟩ =
      some ⟨3,L,[true]++R⟩ := by
    intro L R
    rfl
  have h := sweepL table 3 [] [] [false] [true] 1 one n L R
  simpa [zeros,ones] using h

/-- The blank run reaches the first member (physical marker k=3) in 85 steps. -/
theorem first : run0 table 85 ⟨0,[],[]⟩ = some (family 0) := by
  decide +kernel

theorem growth (n : Nat) :
    run0 table (30*n+97) (family n) = some (family (n+1)) := by
  have h0 : run0 table 5 (family n) =
      some ⟨2,[true,true,true,false,true,true,false]++ones (n+1),ones (5*n+5)⟩ := by
    rfl

  have h1c : run0 table (5*n+5)
      ⟨2,[true,true,true,false,true,true,false]++ones (n+1),ones (5*n+5)⟩ =
      some ⟨2,[true]++zeros (5*n+5)++[true,true,false,true,true,false]++ones (n+1),[]⟩ := by
    simpa using sweepC (5*n+5) ([true,true,false,true,true,false]++ones (n+1)) []

  have h1turn : run0 table 2
      ⟨2,[true]++zeros (5*n+5)++[true,true,false,true,true,false]++ones (n+1),[]⟩ =
      some ⟨3,zeros (5*n+8)++[true,true,false,true,true,false]++ones (n+1),[]⟩ := by
    rfl

  have h1d : run0 table (5*n+8)
      ⟨3,zeros (5*n+8)++[true,true,false,true,true,false]++ones (n+1),[]⟩ =
      some ⟨3,[true,true,false,true,true,false]++ones (n+1),ones (5*n+8)⟩ := by
    simpa using sweepD (5*n+8) ([true,true,false,true,true,false]++ones (n+1)) []

  have h1end : run0 table 2
      ⟨3,[true,true,false,true,true,false]++ones (n+1),ones (5*n+8)⟩ =
      some ⟨4,[false,true,false,true,true,false]++ones (n+1),ones (5*n+8)⟩ := by
    rfl

  have h2pre : run0 table 13
      ⟨4,[false,true,false,true,true,false]++ones (n+1),ones (5*n+8)⟩ =
      some ⟨2,[true,true]++zeros 4++ones (n+2),ones (5*n+7)⟩ := by
    rfl

  have h2c : run0 table (5*n+7)
      ⟨2,[true,true]++zeros 4++ones (n+2),ones (5*n+7)⟩ =
      some ⟨2,[true]++zeros (5*n+7)++[true]++zeros 4++ones (n+2),[]⟩ := by
    simpa using sweepC (5*n+7) ([true]++zeros 4++ones (n+2)) []

  have h2turn : run0 table 2
      ⟨2,[true]++zeros (5*n+7)++[true]++zeros 4++ones (n+2),[]⟩ =
      some ⟨3,zeros (5*n+10)++[true]++zeros 4++ones (n+2),[]⟩ := by
    rfl

  have h2d : run0 table (5*n+10)
      ⟨3,zeros (5*n+10)++[true]++zeros 4++ones (n+2),[]⟩ =
      some ⟨3,[true]++zeros 4++ones (n+2),ones (5*n+10)⟩ := by
    simpa using sweepD (5*n+10) ([true]++zeros 4++ones (n+2)) []

  have h2end : run0 table 2
      ⟨3,[true]++zeros 4++ones (n+2),ones (5*n+10)⟩ =
      some ⟨4,zeros 5++ones (n+2),ones (5*n+10)⟩ := by
    rfl

  have h3pre : run0 table 5
      ⟨4,zeros 5++ones (n+2),ones (5*n+10)⟩ =
      some ⟨2,[true,true,true]++zeros 3++ones (n+2),ones (5*n+9)⟩ := by
    rfl

  have h3c : run0 table (5*n+9)
      ⟨2,[true,true,true]++zeros 3++ones (n+2),ones (5*n+9)⟩ =
      some ⟨2,[true]++zeros (5*n+9)++[true,true]++zeros 3++ones (n+2),[]⟩ := by
    simpa using sweepC (5*n+9) ([true,true]++zeros 3++ones (n+2)) []

  have h3turn : run0 table 2
      ⟨2,[true]++zeros (5*n+9)++[true,true]++zeros 3++ones (n+2),[]⟩ =
      some ⟨3,zeros (5*n+12)++[true,true]++zeros 3++ones (n+2),[]⟩ := by
    rfl

  have h3d : run0 table (5*n+12)
      ⟨3,zeros (5*n+12)++[true,true]++zeros 3++ones (n+2),[]⟩ =
      some ⟨3,[true,true]++zeros 3++ones (n+2),ones (5*n+12)⟩ := by
    simpa using sweepD (5*n+12) ([true,true]++zeros 3++ones (n+2)) []

  have h3end : run0 table 2
      ⟨3,[true,true]++zeros 3++ones (n+2),ones (5*n+12)⟩ =
      some ⟨4,[false,true]++zeros 3++ones (n+2),ones (5*n+12)⟩ := by
    rfl

  have h4 : run0 table 11
      ⟨4,[false,true]++zeros 3++ones (n+2),ones (5*n+12)⟩ =
      some (family (n+1)) := by
    rfl

  have hA := join0 h0 (join0 h1c (join0 h1turn (join0 h1d h1end)))
  have hcA : 5 + ((5*n+5) + (2 + ((5*n+8) + 2))) = 10*n+22 := by omega
  have hA' : run0 table (10*n+22) (family n) =
      some ⟨4,[false,true,false,true,true,false]++ones (n+1),ones (5*n+8)⟩ := by
    simpa only [hcA] using hA

  have hB := join0 h2pre (join0 h2c (join0 h2turn (join0 h2d h2end)))
  have hcB : 13 + ((5*n+7) + (2 + ((5*n+10) + 2))) = 10*n+34 := by omega
  have hB' : run0 table (10*n+34)
      ⟨4,[false,true,false,true,true,false]++ones (n+1),ones (5*n+8)⟩ =
      some ⟨4,zeros 5++ones (n+2),ones (5*n+10)⟩ := by
    simpa only [hcB] using hB

  have hC := join0 h3pre (join0 h3c (join0 h3turn (join0 h3d h3end)))
  have hcC : 5 + ((5*n+9) + (2 + ((5*n+12) + 2))) = 10*n+30 := by omega
  have hC' : run0 table (10*n+30)
      ⟨4,zeros 5++ones (n+2),ones (5*n+10)⟩ =
      some ⟨4,[false,true]++zeros 3++ones (n+2),ones (5*n+12)⟩ := by
    simpa only [hcC] using hC

  have H := join0 hA' (join0 hB' (join0 hC' h4))
  have hc : (10*n+22) + ((10*n+34) + ((10*n+30) + 11)) = 30*n+97 := by omega
  simpa only [hc] using H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply never_of_growth table family 85 (fun n => 30*n+97) first
  · intro n
    omega
  · exact growth
  · exact hm

#print axioms first
#print axioms sweepC
#print axioms sweepD
#print axioms growth
#print axioms never
end BB6.Agent38Raw43B1LEE0RA
