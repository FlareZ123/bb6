import Lean.Elab.Tactic.Omega
import PacketSource
import P2K4Shapes

namespace BB6.Agent35K4
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent35K4Shapes
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

private theorem initial_shape (ka p : Nat) :
  packet (3*ka+3) 4 p marker =
    init (List.replicate (3*ka+1) true ++ false ::
      ([true,false,true,false,true,false,true,false] ++
        (List.replicate p true ++ marker))) := by
  have hn : 3*ka+3 = 2+(3*ka+1) := by omega
  simp only [packet,word,init]
  rw [hn, ←List.replicate_append_replicate]
  simp [oppairs,List.append_assoc]

theorem shape_zero (t u : Nat) :
  packet (3*(512*t+426)+3) 4 (2*(3*u)) marker =
    init (List.replicate (3*(512*t+426)+1) true ++
      false :: (CryptidA.wordCode (code u) ++
        (false :: [true,false,true,false,true,true,true]))) := by
  rw [initial_shape]
  rw [word0]

theorem shape_one (t u : Nat) :
  packet (3*(512*t+426)+3) 4 (2*(3*u+1)) marker =
    init (List.replicate (3*(512*t+426)+1) true ++
      false :: (CryptidA.wordCode (code u) ++
        [true,true,false,true,false,true,false,true,true,true])) := by
  rw [initial_shape, word1]

theorem shape_two (t u : Nat) :
  packet (3*(512*t+426)+3) 4 (2*(3*u+2)) marker =
    init (List.replicate (3*(512*t+426)+1) true ++
      false :: CryptidA.wordCode (codeTail u)) := by
  rw [initial_shape, word2]

#print axioms shape_zero
#print axioms shape_one
#print axioms shape_two
end BB6.Agent35K4
