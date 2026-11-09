import S4PrefixNinthBase
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 500000
set_option maxHeartbeats 0

namespace S4PrefixNinth
open S4PrefixEighthCycle

/-- Exact 1024-return checkpoints, checked separately by the kernel. -/
private def block0 : List Nat := cycle8PeriodicStart ++ [171049]
private def block1 : List Nat := [283, 906, 982, 3490, 3734, 5935, 13577, 30994, 69779]
private def block2 : List Nat := [283, 906, 982, 3490, 3734, 5935, 13579, 58387, 80732]
private def block3 : List Nat := [283, 906, 982, 3490, 3734, 5935, 13576, 21466, 32333]
private def block4 : List Nat := [283, 906, 982, 3490, 3734, 5935, 13578, 66005, 50693]
private def block5 : List Nat := [283, 906, 982, 3490, 3734, 5935, 13580, 109208, 117513]
private def block6 : List Nat := [283, 906, 982, 3490, 3734, 5935, 13577, 30997, 112528]
private def block7 : List Nat := [283, 906, 982, 3490, 3734, 5935, 13579, 58389, 159947]
private def block8 : List Nat := [283, 906, 982, 3490, 3734, 5935, 13576, 21467, 45309]
private def block9 : List Nat := [283, 906, 982, 3490, 3734, 5935, 13578, 66007, 85437]
private def block10 : List Nat := [283, 906, 982, 3490, 3734, 5935, 13580, 109209, 165781]
private def block11 : List Nat := [283, 906, 982, 3490, 3734, 5935, 13577, 30993, 34108]
private def block12 : List Nat := [283, 906, 982, 3490, 3734, 5935, 13579, 58388, 103303]
private def block13 : List Nat := [283, 906, 982, 3490, 3734, 5935, 13576, 21469, 82039]
private def block14 : List Nat := [283, 906, 982, 3490, 3734, 5935, 13578, 66006, 67526]
private def block15 : List Nat := [283, 906, 982, 3490, 3734, 5935, 13580, 109206, 56243]
private def block16 : List Nat := [283, 906, 982, 3490, 3734, 5935, 13577, 30995, 78070]
private def block17 : List Nat := [283, 906, 982, 3490, 3734, 5935, 13579, 58386, 82048]
private def block18 : List Nat := [283, 906, 982, 3490, 3734, 5935, 13576, 21468, 96487]
private def block19 : List Nat := [283, 906, 982, 3490, 3734, 5935, 13578, 66009, 124938]
private def block20 : List Nat := [283, 906, 982, 3490, 3734, 5935, 13580, 109210, 171050]

private theorem piece0 : prefixRunFast 1024 block0 = block1 := by decide
private theorem piece1 : prefixRunFast 1024 block1 = block2 := by decide
private theorem piece2 : prefixRunFast 1024 block2 = block3 := by decide
private theorem piece3 : prefixRunFast 1024 block3 = block4 := by decide
private theorem piece4 : prefixRunFast 1024 block4 = block5 := by decide
private theorem piece5 : prefixRunFast 1024 block5 = block6 := by decide
private theorem piece6 : prefixRunFast 1024 block6 = block7 := by decide
private theorem piece7 : prefixRunFast 1024 block7 = block8 := by decide
private theorem piece8 : prefixRunFast 1024 block8 = block9 := by decide
private theorem piece9 : prefixRunFast 1024 block9 = block10 := by decide
private theorem piece10 : prefixRunFast 1024 block10 = block11 := by decide
private theorem piece11 : prefixRunFast 1024 block11 = block12 := by decide
private theorem piece12 : prefixRunFast 1024 block12 = block13 := by decide
private theorem piece13 : prefixRunFast 1024 block13 = block14 := by decide
private theorem piece14 : prefixRunFast 1024 block14 = block15 := by decide
private theorem piece15 : prefixRunFast 1024 block15 = block16 := by decide
private theorem piece16 : prefixRunFast 1024 block16 = block17 := by decide
private theorem piece17 : prefixRunFast 1024 block17 = block18 := by decide
private theorem piece18 : prefixRunFast 1024 block18 = block19 := by decide
private theorem piece19 : prefixRunFast 1024 block19 = block20 := by decide

theorem r171049 : return9Fast 171049 = 171050 := by
  have h1 : prefixRunFast (1024*1) block0 = block1 := by simpa using piece0
  have h2 : prefixRunFast (1024*2) block0 = block2 := by
    calc
      prefixRunFast (1024*2) block0 = prefixRunFast (1024*1+1024) block0 := by rfl
      _ = prefixRunFast 1024 (prefixRunFast (1024*1) block0) := prefixRunFast_add (1024*1) 1024 block0
      _ = block2 := by rw [h1, piece1]
  have h3 : prefixRunFast (1024*3) block0 = block3 := by
    calc
      prefixRunFast (1024*3) block0 = prefixRunFast (1024*2+1024) block0 := by rfl
      _ = prefixRunFast 1024 (prefixRunFast (1024*2) block0) := prefixRunFast_add (1024*2) 1024 block0
      _ = block3 := by rw [h2, piece2]
  have h4 : prefixRunFast (1024*4) block0 = block4 := by
    calc
      prefixRunFast (1024*4) block0 = prefixRunFast (1024*3+1024) block0 := by rfl
      _ = prefixRunFast 1024 (prefixRunFast (1024*3) block0) := prefixRunFast_add (1024*3) 1024 block0
      _ = block4 := by rw [h3, piece3]
  have h5 : prefixRunFast (1024*5) block0 = block5 := by
    calc
      prefixRunFast (1024*5) block0 = prefixRunFast (1024*4+1024) block0 := by rfl
      _ = prefixRunFast 1024 (prefixRunFast (1024*4) block0) := prefixRunFast_add (1024*4) 1024 block0
      _ = block5 := by rw [h4, piece4]
  have h6 : prefixRunFast (1024*6) block0 = block6 := by
    calc
      prefixRunFast (1024*6) block0 = prefixRunFast (1024*5+1024) block0 := by rfl
      _ = prefixRunFast 1024 (prefixRunFast (1024*5) block0) := prefixRunFast_add (1024*5) 1024 block0
      _ = block6 := by rw [h5, piece5]
  have h7 : prefixRunFast (1024*7) block0 = block7 := by
    calc
      prefixRunFast (1024*7) block0 = prefixRunFast (1024*6+1024) block0 := by rfl
      _ = prefixRunFast 1024 (prefixRunFast (1024*6) block0) := prefixRunFast_add (1024*6) 1024 block0
      _ = block7 := by rw [h6, piece6]
  have h8 : prefixRunFast (1024*8) block0 = block8 := by
    calc
      prefixRunFast (1024*8) block0 = prefixRunFast (1024*7+1024) block0 := by rfl
      _ = prefixRunFast 1024 (prefixRunFast (1024*7) block0) := prefixRunFast_add (1024*7) 1024 block0
      _ = block8 := by rw [h7, piece7]
  have h9 : prefixRunFast (1024*9) block0 = block9 := by
    calc
      prefixRunFast (1024*9) block0 = prefixRunFast (1024*8+1024) block0 := by rfl
      _ = prefixRunFast 1024 (prefixRunFast (1024*8) block0) := prefixRunFast_add (1024*8) 1024 block0
      _ = block9 := by rw [h8, piece8]
  have h10 : prefixRunFast (1024*10) block0 = block10 := by
    calc
      prefixRunFast (1024*10) block0 = prefixRunFast (1024*9+1024) block0 := by rfl
      _ = prefixRunFast 1024 (prefixRunFast (1024*9) block0) := prefixRunFast_add (1024*9) 1024 block0
      _ = block10 := by rw [h9, piece9]
  have h11 : prefixRunFast (1024*11) block0 = block11 := by
    calc
      prefixRunFast (1024*11) block0 = prefixRunFast (1024*10+1024) block0 := by rfl
      _ = prefixRunFast 1024 (prefixRunFast (1024*10) block0) := prefixRunFast_add (1024*10) 1024 block0
      _ = block11 := by rw [h10, piece10]
  have h12 : prefixRunFast (1024*12) block0 = block12 := by
    calc
      prefixRunFast (1024*12) block0 = prefixRunFast (1024*11+1024) block0 := by rfl
      _ = prefixRunFast 1024 (prefixRunFast (1024*11) block0) := prefixRunFast_add (1024*11) 1024 block0
      _ = block12 := by rw [h11, piece11]
  have h13 : prefixRunFast (1024*13) block0 = block13 := by
    calc
      prefixRunFast (1024*13) block0 = prefixRunFast (1024*12+1024) block0 := by rfl
      _ = prefixRunFast 1024 (prefixRunFast (1024*12) block0) := prefixRunFast_add (1024*12) 1024 block0
      _ = block13 := by rw [h12, piece12]
  have h14 : prefixRunFast (1024*14) block0 = block14 := by
    calc
      prefixRunFast (1024*14) block0 = prefixRunFast (1024*13+1024) block0 := by rfl
      _ = prefixRunFast 1024 (prefixRunFast (1024*13) block0) := prefixRunFast_add (1024*13) 1024 block0
      _ = block14 := by rw [h13, piece13]
  have h15 : prefixRunFast (1024*15) block0 = block15 := by
    calc
      prefixRunFast (1024*15) block0 = prefixRunFast (1024*14+1024) block0 := by rfl
      _ = prefixRunFast 1024 (prefixRunFast (1024*14) block0) := prefixRunFast_add (1024*14) 1024 block0
      _ = block15 := by rw [h14, piece14]
  have h16 : prefixRunFast (1024*16) block0 = block16 := by
    calc
      prefixRunFast (1024*16) block0 = prefixRunFast (1024*15+1024) block0 := by rfl
      _ = prefixRunFast 1024 (prefixRunFast (1024*15) block0) := prefixRunFast_add (1024*15) 1024 block0
      _ = block16 := by rw [h15, piece15]
  have h17 : prefixRunFast (1024*17) block0 = block17 := by
    calc
      prefixRunFast (1024*17) block0 = prefixRunFast (1024*16+1024) block0 := by rfl
      _ = prefixRunFast 1024 (prefixRunFast (1024*16) block0) := prefixRunFast_add (1024*16) 1024 block0
      _ = block17 := by rw [h16, piece16]
  have h18 : prefixRunFast (1024*18) block0 = block18 := by
    calc
      prefixRunFast (1024*18) block0 = prefixRunFast (1024*17+1024) block0 := by rfl
      _ = prefixRunFast 1024 (prefixRunFast (1024*17) block0) := prefixRunFast_add (1024*17) 1024 block0
      _ = block18 := by rw [h17, piece17]
  have h19 : prefixRunFast (1024*19) block0 = block19 := by
    calc
      prefixRunFast (1024*19) block0 = prefixRunFast (1024*18+1024) block0 := by rfl
      _ = prefixRunFast 1024 (prefixRunFast (1024*18) block0) := prefixRunFast_add (1024*18) 1024 block0
      _ = block19 := by rw [h18, piece18]
  have h20 : prefixRunFast (1024*20) block0 = block20 := by
    calc
      prefixRunFast (1024*20) block0 = prefixRunFast (1024*19+1024) block0 := by rfl
      _ = prefixRunFast 1024 (prefixRunFast (1024*19) block0) := prefixRunFast_add (1024*19) 1024 block0
      _ = block20 := by rw [h19, piece19]
  have heq : prefixRunFast 20480 (cycle8PeriodicStart ++ [171049]) =
      cycle8PeriodicStart ++ [171050] := by
    simpa [block0, block20, cycle8PeriodicStart, S4PrefixSeven.cycle7] using h20
  simp [return9Fast, heq]

#print axioms r171049

end S4PrefixNinth
