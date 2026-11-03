import Lean.Elab.Tactic.Omega
import EThirdSource
import ETripleLadderIndex

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.ERegularLadderSource
open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent31SecondSource BB6.EThirdSource
open BB6.ETripleLadderIndex BB6.ETripleLadderSource

/-- Source E exceptional 3-checkpoint output is exactly a synthetic
    arbitrary-depth ladder input whenever the unary and packet sizes match. -/
theorem third_E_section (v h m u : Nat)
    (hn : 512*v+257 = 3^(m+1)*(u+1)+1)
    (hp : 2*h = 3*m+3) :
    thirdFinish v h =
      physicalSection (3^(m+1)*(u+1)+1) 4 m (List.replicate 6 true) := by
  simp [thirdFinish,physicalSection,hn,hp,oppairs,pairs,
    List.append_assoc]

/-- Source B exceptional 3-checkpoint output has the analogous single-pair
    exact E-ladder input under the even-depth size condition. -/
theorem third_B_section (v h m u : Nat)
    (hn : 512*v+434 = 3^(m+1)*(u+1)+1)
    (hp : 2*h+3 = 3*m+3) :
    thirdBFinish v h =
      physicalSection (3^(m+1)*(u+1)+1) 1 m (List.replicate 6 true) := by
  simp [thirdBFinish,physicalSection,hn,hp,oppairs,pairs,
    List.append_assoc]

/-- EXACT source-machine endpoint of a 3+ m checkpoint chain for the
    t≡1 mod 3 exceptional E class. The first 3 sections use physical
    observational equality, the ladder uses exact source configuration. -/
theorem original_E_then_ladder (v h m u : Nat)
    (hn : 512*v+257 = 3^(m+1)*(u+1)+1)
    (hp : 2*h = 3*m+3) :
    ObsEq
      (run ((firstCost (3*v+1) h + secondCost (3*v+1) + thirdCost v) +
        totalCost m u 4) (start (3*v+1) h))
      (physicalSection (3*8^m*(u+1)+1) (4+2*m) 0
        (List.replicate 6 true)) := by
  have hs := three_returns_source v h
  rw [third_E_section v h m u hn hp] at hs
  have ht : ObsEq
      (run (totalCost m u 4)
        (physicalSection (3^(m+1)*(u+1)+1) 4 m
          (List.replicate 6 true)))
      (physicalSection (3*8^m*(u+1)+1) (4+2*m) 0
        (List.replicate 6 true)) := by
    rw [power_ladder_source]
    exact cfgEq_refl _
  exact source_chain
    (firstCost (3*v+1) h + secondCost (3*v+1) + thirdCost v)
    (totalCost m u 4)
    (start (3*v+1) h)
    (physicalSection (3^(m+1)*(u+1)+1) 4 m (List.replicate 6 true))
    (physicalSection (3*8^m*(u+1)+1) (4+2*m) 0
       (List.replicate 6 true)) hs ht

/-- EXACT source-machine endpoint of a 3+ m checkpoint chain for the
    t≡2 mod 3 exceptional B class, with one alternating pair. -/
theorem original_B_then_ladder (v h m u : Nat)
    (hn : 512*v+434 = 3^(m+1)*(u+1)+1)
    (hp : 2*h+3 = 3*m+3) :
    ObsEq
      (run ((firstCost (3*v+2) h + secondCost (3*v+2) + thirdBCost v) +
        totalCost m u 1) (start (3*v+2) h))
      (physicalSection (3*8^m*(u+1)+1) (1+2*m) 0
        (List.replicate 6 true)) := by
  have hs := three_returns_B_source v h
  rw [third_B_section v h m u hn hp] at hs
  have ht : ObsEq
      (run (totalCost m u 1)
        (physicalSection (3^(m+1)*(u+1)+1) 1 m
          (List.replicate 6 true)))
      (physicalSection (3*8^m*(u+1)+1) (1+2*m) 0
        (List.replicate 6 true)) := by
    rw [power_ladder_source]
    exact cfgEq_refl _
  exact source_chain
    (firstCost (3*v+2) h + secondCost (3*v+2) + thirdBCost v)
    (totalCost m u 1)
    (start (3*v+2) h)
    (physicalSection (3^(m+1)*(u+1)+1) 1 m (List.replicate 6 true))
    (physicalSection (3*8^m*(u+1)+1) (1+2*m) 0
       (List.replicate 6 true)) hs ht

#print axioms third_E_section
#print axioms third_B_section
#print axioms original_E_then_ladder
#print axioms original_B_then_ladder
end BB6.ERegularLadderSource
