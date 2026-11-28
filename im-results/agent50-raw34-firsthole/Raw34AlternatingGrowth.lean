import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw34Alternating
open BB6Coverage BB6Coverage.Agent31Pump

/-!
Raw34 depth-three open cylinder
  1RB---_1RC---_0RD0LD_1LC0RE_1RD---_------
has alternating 10-block growth. At the nth marked odd frontier, state D
scans a fresh 0, its left tape is (10)^n followed by 011, and its right tape
is blank. A two-step C1/D0 left sweep transfers 10 -> 01 across the block,
while a two-step D1/E0 right sweep transfers 01 -> 10 back. The composite
takes exactly 4n+4 steps and advances by two cells, with no undefined read.
-/

def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | _,_ => none

def leftBits (n : Nat) : List Bool := rep [true,false] n

def rightBits (n : Nat) : List Bool := rep [false,true] n

def family (n : Nat) : Z0 :=
  ⟨3,[false]++leftBits n++[false,true,true],[]⟩

theorem first :
    run0 p 3 ⟨0,[],[]⟩ = some (family 0) := by decide

theorem left_two :
    ∀ L R, run0 p 2 ⟨2,[true,false]++L,[true]++R⟩ =
      some ⟨2,L,[true,false,true]++R⟩ := by
  intro L R
  rfl

theorem right_two :
    ∀ L R, run0 p 2 ⟨3,[true]++L,[false,true]++R⟩ =
      some ⟨3,[true,true,false]++L,R⟩ := by
  intro L R
  rfl

theorem growth (n : Nat) :
    run0 p (4*n+4) (family n) = some (family (n+1)) := by
  have h0 : run0 p 1 (family n) =
      some ⟨2,leftBits n++[false,true,true],[true]⟩ := by
    rfl
  have hL : run0 p (2*n)
      ⟨2,leftBits n++[false,true,true],[true]⟩ =
      some ⟨2,[false,true,true],[true]++rightBits n⟩ := by
    have h := sweepL p 2 [] [true] [true,false] [false,true] 2
      left_two n [false,true,true] []
    simpa [leftBits,rightBits] using h
  have hC : run0 p 1
      ⟨2,[false,true,true],[true]++rightBits n⟩ =
      some ⟨3,[true,false,true,true],rightBits n⟩ := by
    rfl
  have hR : run0 p (2*n)
      ⟨3,[true,false,true,true],rightBits n⟩ =
      some ⟨3,[true]++leftBits n++[false,true,true],[]⟩ := by
    have h := sweepR p 3 [true] [] [false,true] [true,false] 2
      right_two n [false,true,true] []
    simpa [leftBits,rightBits] using h
  have hEnd : run0 p 2
      ⟨3,[true]++leftBits n++[false,true,true],[]⟩ =
      some (family (n+1)) := by
    rfl
  have h := join0 h0 (join0 hL (join0 hC (join0 hR hEnd)))
  have hc : 1+(2*n+(1+(2*n+2))) = 4*n+4 := by omega
  simpa only [hc] using h

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p family 3 (fun n => 4*n+4) first
  · intro n; omega
  · exact growth
  · exact hm

#print axioms first
#print axioms left_two
#print axioms right_two
#print axioms growth
#print axioms never
end BB6.Agent50Raw34Alternating
