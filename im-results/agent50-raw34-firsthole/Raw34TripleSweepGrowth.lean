import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw34TripleSweep
open BB6Coverage BB6Coverage.Agent31Pump

/-!
Two long-running Raw34 depth-three holdouts have precisely the same unary
tape geometry. Their only difference is the intermediate right-turning state
on C1: A for case false, E for case true. The bridge state always reads a 1
and executes 1LD, while D0=1LC, D1=1RD. The finite *three-step* left sweep
C1 -> bridge1 -> D0 shifts one marked cell from left to right, and ordinary
D1 sweeps right. The kth fresh right-frontier state recurs in 4*k+3 steps.
No unspecified transition is ever queried.
-/

def pA : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨true,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨true,true,3⟩)
  | _,_ => none

def pE : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨true,true,3⟩)
  | 4,true  => some (some ⟨true,false,3⟩)
  | _,_ => none

def p (useE : Bool) : PartialMachine :=
  if useE then pE else pA

def bits (n : Nat) : List Bool := rep [true] n

def family (n : Nat) : Z0 :=
  ⟨3,[false]++bits n++[false,true,true],[]⟩

theorem first (useE : Bool) :
    run0 (p useE) 3 ⟨0,[],[]⟩ = some (family 0) := by
  cases useE <;> decide

/- The leftward step consumes one C1-marked cell with three moves:
   C1=0Rbridge, bridge1=1LD, D0=1LC. -/
theorem left_three (useE : Bool) :
    ∀ L R, run0 (p useE) 3 ⟨2,[true]++L,[true]++R⟩ =
      some ⟨2,L,[true,true]++R⟩ := by
  intro L R
  cases useE <;> rfl

theorem right_one (useE : Bool) :
    ∀ L R, run0 (p useE) 1 ⟨3,[true]++L,[true]++R⟩ =
      some ⟨3,[true]++[true]++L,R⟩ := by
  intro L R
  cases useE <;> rfl

theorem growth (useE : Bool) (n : Nat) :
    run0 (p useE) (4*n+3) (family n) = some (family (n+1)) := by
  have h0 : run0 (p useE) 1 (family n) =
      some ⟨2,bits n++[false,true,true],[true]⟩ := by
    cases useE <;> rfl
  have hL : run0 (p useE) (3*n)
      ⟨2,bits n++[false,true,true],[true]⟩ =
      some ⟨2,[false,true,true],[true]++bits n⟩ := by
    have h := sweepL (p useE) 2 [] [true] [true] [true] 3
      (left_three useE) n [false,true,true] []
    simpa [bits] using h
  have hC : run0 (p useE) 1
      ⟨2,[false,true,true],[true]++bits n⟩ =
      some ⟨3,[true,false,true,true],bits n⟩ := by
    cases useE <;> rfl
  have hR : run0 (p useE) n
      ⟨3,[true,false,true,true],bits n⟩ =
      some ⟨3,[true]++bits n++[false,true,true],[]⟩ := by
    have h := sweepR (p useE) 3 [true] [] [true] [true] 1
      (right_one useE) n [false,true,true] []
    simpa [bits] using h
  have hEnd : run0 (p useE) 1
      ⟨3,[true]++bits n++[false,true,true],[]⟩ =
      some (family (n+1)) := by
    cases useE <;> rfl
  have h := join0 h0 (join0 hL (join0 hC (join0 hR hEnd)))
  have hc : 1+(3*n+(1+(n+1))) = 4*n+3 := by omega
  simpa only [hc] using h

theorem never (useE : Bool) (m : Machine)
    (hm : compatible (p useE) m) : NeverHalts m := by
  apply never_of_growth (p useE) family 3 (fun n => 4*n+3) (first useE)
  · intro n; omega
  · exact growth useE
  · exact hm

theorem A_never (m : Machine)
    (hm : compatible pA m) : NeverHalts m :=
  never false m hm

theorem E_never (m : Machine)
    (hm : compatible pE m) : NeverHalts m :=
  never true m hm

#print axioms first
#print axioms left_three
#print axioms right_one
#print axioms growth
#print axioms never
#print axioms A_never
#print axioms E_never
end BB6.Agent50Raw34TripleSweep
