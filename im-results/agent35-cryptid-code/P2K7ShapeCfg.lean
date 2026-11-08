import Lean.Elab.Tactic.Omega
import PacketSource
import P2K7Shapes

namespace BB6.Agent35K7
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent35K4Shapes (marker)
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

private theorem initial_shape (ka p : Nat) :
  packet (3*ka+3) 1 p marker =
    init (List.replicate (3*ka+1) true ++ false ::
      ([true,false] ++ (List.replicate p true ++ marker))) := by
  have hn : 3*ka+3 = 2+(3*ka+1) := by omega
  simp only [packet,word,init]
  rw [hn, ←List.replicate_append_replicate]
  simp [oppairs,List.append_assoc]

theorem shape_zero (t u : Nat) :
  packet (3*(512*t+485)+3) 1 (2*(3*u)+3) marker =
    init (List.replicate (3*(512*t+485)+1) true ++
      false :: (CryptidA.wordCode (BB6.Agent35K7Shapes.code u) ++
        (false :: [true,false,true,false,true,true,true]))) := by
  rw [initial_shape]
  rw [BB6.Agent35K7Shapes.word0]

theorem shape_one (t u : Nat) :
  packet (3*(512*t+485)+3) 1 (2*(3*u+1)+3) marker =
    init (List.replicate (3*(512*t+485)+1) true ++
      false :: (CryptidA.wordCode (BB6.Agent35K7Shapes.code u) ++
        [true,true,false,true,false,true,false,true,true,true])) := by
  rw [initial_shape]
  rw [BB6.Agent35K7Shapes.word1]

theorem shape_two (t u : Nat) :
  packet (3*(512*t+485)+3) 1 (2*(3*u+2)+3) marker =
    init (List.replicate (3*(512*t+485)+1) true ++
      false :: CryptidA.wordCode (BB6.Agent35K7Shapes.codeTail u)) := by
  rw [initial_shape]
  rw [BB6.Agent35K7Shapes.word2]

#print axioms shape_zero
#print axioms shape_one
#print axioms shape_two
end BB6.Agent35K7
