import Raw14042MixedFrontLocal
import Raw14042DMixed
import Raw14042BMixedEnd
namespace Raw14042MixedFront
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140VariantTransfer Raw140Double
open Raw14042MixedFrontLocal
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [local irreducible] run boundary
private theorem rr {k : Nat} {c d : Prim} (h : run base k c = some d) : Reach base c d := ⟨k,h⟩

-- First four passes of the mixed D bank, preserving the arbitrary left frame.
theorem cSeed (X : List Sym) :
    Reach base (boundary 3 false (S 6::S 6::S 6::S 6::X) [S 4,S 2,S 1,S 5,S 5,S 4,S 2])
      (Raw14042DMixed.P 2 2 X [] .t1121) := by
  have h0 := rr (cSeed1 (S 6::S 6::S 6::X))
  have h1 := rr (cSeed2 (S 6::S 6::X))
  have h2 := rr (cSeed3 (S 6::X))
  have h3 := rr (cSeed4 X)
  exact Reach.trans (Reach.trans (Reach.trans h0 h1) h2) h3

-- The raw seed of B62542 after the first M42-dependent entry.
theorem bSeedReach (X : List Sym) :
    Reach base (boundary 4 true (S 1::S 3::S 5::X) [S 1,S 1,S 2,S 3,S 3,S 1,S 5])
      (Raw14042BMixed.Q 2 3 0 X .c325) := rr (bSeed X)

-- All mixed D iterations plus the last unpaired six. The exponent j is
-- (p-4)/2, so this is exactly the even p branch of C35221.
theorem cDeplete (j : Nat) :
    Reach base (boundary 3 false (U 6 (2*j+5) ++ [S 4]) [S 4,S 2,S 1,S 5,S 5,S 4,S 2])
      (boundary 3 false [S 4]
        (U 4 (j+4) ++ S 0::S 5::(U 1 (j+2) ++ S 5::
          (Raw14042AWord.TA (Raw14042DMixed.turn j .t1121).1 ++ Raw14042DMixed.aw (Raw14042DMixed.turn j .t1121).2)))) := by
  let X := U 6 (2*j) ++ [S 6,S 4]
  have h0 := cSeed X
  have h1 := Raw14042DMixed.pairs j 2 2 [S 6,S 4] [] .t1121
  have h2 := Raw14042DMixed.phase1 (2+j) (2+j) [S 4]
    (S 5::(Raw14042AWord.TA (Raw14042DMixed.turn j .t1121).1 ++ Raw14042DMixed.aw (Raw14042DMixed.turn j .t1121).2))
  have h01 := Reach.trans h0 h1
  have h2' : Reach base
      (Raw14042DMixed.P (2+j) (2+j) [S 6,S 4] ([] ++ Raw14042AWord.tr15 (Raw14042DMixed.turn j .t1121).1) (Raw14042DMixed.turn j .t1121).2)
      (boundary 3 false [S 4]
        (U 4 (j+4) ++ S 0::S 5::(U 1 (j+2) ++ S 5::
          (Raw14042AWord.TA (Raw14042DMixed.turn j .t1121).1 ++ Raw14042DMixed.aw (Raw14042DMixed.turn j .t1121).2)))) := by
    simpa only [Raw14042DMixed.P,List.nil_append,Raw14042AWord.w15_tr,
      show 2+j+2=j+4 by omega,show 2+j=j+2 by omega] using h2
  have h := Reach.trans h01 h2'
  have e : U 6 (2*j+5) ++ [S 4] = S 6::S 6::S 6::S 6::X := by
    change List.replicate (2*j+5) (S 6) ++ [S 4] = List.replicate 4 (S 6) ++ (List.replicate (2*j) (S 6) ++ [S 6,S 4])
    change _ = List.replicate 4 (S 6) ++ (List.replicate (2*j) (S 6) ++ (List.replicate 1 (S 6) ++ [S 4]))
    simp only [← List.append_assoc,List.replicate_append_replicate,show 4+(2*j+1)=2*j+5 by omega]
  rw [e]
  exact h

-- All mixed B iterations plus the empty-left exit. Here j=(p-4)/2.
theorem bDeplete (j : Nat) :
    Reach base (boundary 4 true (S 1::S 3::(U 5 (2*j+1))) [S 1,S 1,S 2,S 3,S 3,S 1,S 5])
      (boundary 1 true [S 5] (S 2::S 2::(U 1 (j+3) ++ S 2::S 3::(U 2 (j+1) ++
        Raw14042Counter.T (Raw14042Counter.turn j .c325).1 ++ Raw14042Counter.cword (Raw14042Counter.turn j .c325).2)))) := by
  have h0 := bSeedReach (U 5 (2*j))
  have h1 := Raw14042BMixed.pairs j 2 1 0 [] .c325
  have h2 := Raw14042BMixedEnd.emptyEven (2+j) (1+j)
    (Raw14042Counter.T (Raw14042Counter.turn j .c325).1 ++ Raw14042Counter.cword (Raw14042Counter.turn j .c325).2)
  have h01 : Reach base _ _ := Reach.trans h0 (by simpa only [List.append_nil] using h1)
  have h2' : Reach base
      (Raw14042BMixed.Q (2+j) (1+2+j) (0+(Raw14042Counter.turn j .c325).1) [] (Raw14042Counter.turn j .c325).2)
      (boundary 1 true [S 5] (S 2::S 2::(U 1 (j+3) ++ S 2::S 3::(U 2 (j+1) ++
        Raw14042Counter.T (Raw14042Counter.turn j .c325).1 ++ Raw14042Counter.cword (Raw14042Counter.turn j .c325).2)))) := by
    simpa only [Raw14042BMixed.Q,Nat.zero_add,U,List.replicate_succ,List.cons_append,
      show 1+2+j=1+j+2 by omega,show 2+j+1=j+3 by omega,show 1+j=j+1 by omega,
      List.append_assoc] using h2
  simpa only [U,List.replicate_succ,List.cons_append] using Reach.trans h01 h2'

#print axioms cSeed
#print axioms bSeedReach
#print axioms cDeplete
#print axioms bDeplete
end Raw14042MixedFront
