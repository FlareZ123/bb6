import Raw14042MixedFront
import Raw14042MixedExitLocal
import Raw14042DExitTail
import Raw14042CGeneral
namespace Raw14042MixedExitOdd
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140VariantTransfer Raw140Double
open Raw14042MixedExitLocal Raw14042MixedFront
open Raw14042DExitTail (absorb A)
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [local irreducible] run boundary
abbrev RR := Reach base
private theorem rr {k : Nat} {c d : Prim} (h : run base k c = some d) : RR c d := ⟨k,h⟩

-- Odd number of four-blocks: arbitrary suffix is preserved exactly.
theorem cExit (k : Nat) (Y : List Sym) :
    RR (boundary 3 false [S 4] (U 4 (2*k+4) ++ S 0::S 5::(U 1 (2*k+2) ++ S 5::Y)))
      (A (8*k+18) Y) := by
  let Z := S 0::S 5::(U 1 (2*k+2) ++ S 5::Y)
  have h0 := dEndE (2*k+3) Z
  have h1 := eIter (k+1) 1 1 Z
  have h2 := rr (cMarker (4*k+5) (U 1 (2*k+1) ++ S 5::Y))
  have h3 := absorb k (4*k+13) (S 1::S 5::Y)
  have h4 := rr (Raw14042DExitAffine.oddFinish (8*k+13) Y)
  have h01 : RR (boundary 3 false [S 4] (U 4 (2*k+4) ++ Z)) (E (4*k+5) 1 Z) := by
    simpa only [show 2*(k+1)+1=2*k+3 by omega,show 1+4*(k+1)=4*k+5 by omega] using Reach.trans h0 h1
  have h2' : RR (E (4*k+5) 1 Z) (A (4*k+13) (S 0::(U 1 (2*k+1) ++ S 5::Y))) := by
    simpa only [E,Z,A,Raw140VariantTransfer.Mbase,U,List.replicate_succ,List.cons_append,List.replicate_zero,List.nil_append,
      show 4*k+5+8=4*k+13 by omega] using h2
  have h3' : RR (A (4*k+13) (S 0::(U 1 (2*k+1) ++ S 5::Y))) (A (8*k+13) (S 0::S 1::S 5::Y)) := by
    have e : U 1 (2*k+1) ++ S 5::Y = U 1 (2*k) ++ S 1::S 5::Y := by
      simp only [U,List.replicate_succ',List.append_assoc,List.singleton_append]
    simpa only [e,show 4*k+13+4*k=8*k+13 by omega] using h3
  have h4' : RR (A (8*k+13) (S 0::S 1::S 5::Y)) (A (8*k+18) Y) := by
    simpa only [A,show 8*k+13+5=8*k+18 by omega] using h4
  exact Reach.trans (Reach.trans (Reach.trans h01 h2') h3') h4'

-- Odd number of surviving ones: one boundary conversion and a pure two bank.
theorem bExit (k : Nat) (Y : List Sym) :
    RR (boundary 1 true [S 5] (S 2::S 2::(U 1 (2*k+4) ++ S 2::S 3::(U 2 (2*k+2) ++ Y))))
      (A (8*k+16) (S 2::Y)) := by
  let Z := S 2::S 3::(U 2 (2*k+2) ++ Y)
  have h0 := rr (bInit (U 1 (2*k+3) ++ Z))
  have h1 := absorb (k+1) 3 (S 1::Z)
  have h2 := rr (bOddFinish (4*k+7) (U 2 (2*k+2) ++ Y))
  have h3 := Raw14042CGeneral.twoPumpAll (4*k+12) (k+1) 0 Y
  have h0' : RR (boundary 1 true [S 5] (S 2::S 2::(U 1 (2*k+4) ++ Z)))
      (A 3 (S 0::(U 1 (2*k+3) ++ Z))) := by
    simpa only [A,U,List.replicate_succ,List.cons_append,List.replicate_zero,List.nil_append] using h0
  have h1' : RR (A 3 (S 0::(U 1 (2*k+3) ++ Z))) (A (4*k+7) (S 0::S 1::Z)) := by
    have e : U 1 (2*k+3) ++ Z = U 1 (2*(k+1)) ++ S 1::Z := by
      simp only [U,show 2*k+3=2*(k+1)+1 by omega,List.replicate_succ',List.append_assoc,List.singleton_append]
    simpa only [e,show 3+4*(k+1)=4*k+7 by omega] using h1
  have h2' : RR (A (4*k+7) (S 0::S 1::Z)) (A (4*k+12) (U 2 (2*k+3) ++ Y)) := by
    simpa only [A,Z,U,List.replicate_succ,List.cons_append,List.replicate_zero,List.nil_append,show 4*k+7+5=4*k+12 by omega] using h2
  have h3' : RR (A (4*k+12) (U 2 (2*k+3) ++ Y)) (A (8*k+16) (S 2::Y)) := by
    simpa only [A,Nat.add_zero,show 2*(k+1)+1=2*k+3 by omega,
      show 4*k+12+4*(k+1)=8*k+16 by omega,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append] using h3
  exact Reach.trans (Reach.trans (Reach.trans h0' h1') h2') h3'

#print axioms cExit
#print axioms bExit
end Raw14042MixedExitOdd
