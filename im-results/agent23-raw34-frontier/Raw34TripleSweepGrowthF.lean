import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent23Raw34TripleSweepF
open BB6Coverage BB6Coverage.Agent31Pump

/-!
Additional Raw34 descendant (D1=1RD, C1=0RF, F1=1LD):
  1RB---_1RC---_0RD0RF_1LC1RD_------_---1LD
The F-bridge three-move left sweep C1 -> F1 -> D0 is conjugate
to the previously accepted A/E-bridge sweep, but this distinct physical
cylinder was not contained in the previous Raw34 nonhalt union. The
normal form has D scanning fresh right zero, left tape
  0 1^n 0 1 1
and makes the recurrence family(n)->family(n+1) in 4n+3 steps.
No wildcard instruction is ever queried.
-/

def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨true,true,3⟩)
  | 5,true  => some (some ⟨true,false,3⟩)
  | _,_ => none

def bits (n : Nat) : List Bool := rep [true] n
def family (n : Nat) : Z0 :=
  ⟨3,[false]++bits n++[false,true,true],[]⟩

theorem first : run0 p 3 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem left_three :
    ∀ L R, run0 p 3 ⟨2,[true]++L,[true]++R⟩ =
      some ⟨2,L,[true,true]++R⟩ := by
  intro L R
  rfl

theorem right_one :
    ∀ L R, run0 p 1 ⟨3,[true]++L,[true]++R⟩ =
      some ⟨3,[true]++[true]++L,R⟩ := by
  intro L R
  rfl

theorem growth (n : Nat) :
    run0 p (4*n+3) (family n) = some (family (n+1)) := by
  have h0 : run0 p 1 (family n) =
      some ⟨2,bits n++[false,true,true],[true]⟩ := by rfl
  have hL : run0 p (3*n)
      ⟨2,bits n++[false,true,true],[true]⟩ =
      some ⟨2,[false,true,true],[true]++bits n⟩ := by
    have h := sweepL p 2 [] [true] [true] [true] 3
      left_three n [false,true,true] []
    simpa [bits] using h
  have hC : run0 p 1
      ⟨2,[false,true,true],[true]++bits n⟩ =
      some ⟨3,[true,false,true,true],bits n⟩ := by rfl
  have hR : run0 p n
      ⟨3,[true,false,true,true],bits n⟩ =
      some ⟨3,[true]++bits n++[false,true,true],[]⟩ := by
    have h := sweepR p 3 [true] [] [true] [true] 1
      right_one n [false,true,true] []
    simpa [bits] using h
  have hEnd : run0 p 1
      ⟨3,[true]++bits n++[false,true,true],[]⟩ =
      some (family (n+1)) := by rfl
  have h := join0 h0 (join0 hL (join0 hC (join0 hR hEnd)))
  have hc : 1+(3*n+(1+(n+1))) = 4*n+3 := by omega
  simpa only [hc] using h

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p family 3 (fun n => 4*n+3) first
  · intro n; omega
  · exact growth
  · exact hm

#print axioms first
#print axioms left_three
#print axioms right_one
#print axioms growth
#print axioms never
end BB6.Agent23Raw34TripleSweepF
