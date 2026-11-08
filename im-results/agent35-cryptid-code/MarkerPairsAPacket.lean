import Lean.Elab.Tactic.Omega
import PacketSource
import P2MarkerA
import MarkerPairsTerminal

namespace BB6.Agent35MarkerPairPacket
open CryptidBoundary BB6.Agent31PacketSource
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def marker (j : Nat) : List Bool :=
  oppairs (j+1) ++ [true,true]

private theorem oppairs_false (q : Nat) :
    oppairs q ++ [false] = false :: pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs,pairs,List.append_assoc] using
      congrArg (fun zs : List Bool => false :: true :: zs) ih

private theorem shape (ka q r j : Nat) :
    packet (3*ka+3) q (3*r+2) (marker j) =
      init (List.replicate (3*ka+1) true ++ false ::
        (CryptidA.wordCode (BB6.Agent35MarkerA.code q r) ++
          ([true,true] ++ marker j))) := by
  have hn : 3*ka+3 = 2+(3*ka+1) := by omega
  have hp : List.replicate (3*r+2) true =
      List.replicate (3*r) true ++ [true,true] := by
    rw [show 3*r+2=3*r+2 by rfl, ←List.replicate_append_replicate]
    rfl
  have htail :
      oppairs q ++ (false :: (List.replicate (3*r+2) true ++ marker j)) =
        false :: (pairs q ++ (List.replicate (3*r) true ++
          ([true,true] ++ marker j))) := by
    rw [hp]
    calc
      _ = (oppairs q ++ [false]) ++
        (List.replicate (3*r) true ++
          ([true,true] ++ marker j)) := by simp [List.append_assoc]
      _ = _ := by rw [oppairs_false]; simp [List.append_assoc]
  simp only [packet,word,init]
  rw [hn,←List.replicate_append_replicate]
  rw [htail,BB6.Agent35MarkerA.code_word]

/-- One unbounded terminal-pair theorem, source-connected through prefix_A and
arbitrary code words, handles all prepared A packets p≡2 modulo 3 and markers
(01)^J11 with J≥1. Exact original-machine time is given in primitive steps. -/
theorem all_A_pair_terminal (ka q r j : Nat) :
    let ws := BB6.Agent35MarkerA.code q r
    let m := 4*ka+3+CryptidA.wordInc ws
    let t := (12*ka*ka+41*ka+32)+
       (CryptidA.wordCost (4*ka+3) ws+(2*m+6*j+24))
    run t (packet (3*ka+3) q (3*r+2) (marker j)) =
      (⟨[],false,List.replicate (2*m+5) true ++
        (false :: pairs (j+2)),5⟩ : Cfg) := by
  dsimp only
  rw [shape]
  rw [run_add, prefix_A]
  change run (CryptidA.wordCost (4*ka+3) (BB6.Agent35MarkerA.code q r) +
      (2*(4*ka+3+CryptidA.wordInc (BB6.Agent35MarkerA.code q r))+6*j+24))
      (BB6.Agent35.aBoundary (4*ka+3)
        (CryptidA.wordCode (BB6.Agent35MarkerA.code q r) ++
          ([true,true] ++ marker j))) = _
  rw [run_add, BB6.Agent35.a_code_return]
  change run (2*(4*ka+3+CryptidA.wordInc (BB6.Agent35MarkerA.code q r))+6*j+24)
    (aBoundary (4*ka+3+CryptidA.wordInc (BB6.Agent35MarkerA.code q r))
       ([true,true] ++ (oppairs (j+1) ++ ([true,true] ++ [])))) = _
  simpa only [List.append_nil] using
    (BB6.Agent35PairTerminal.a_many_pairs_return
      (4*ka+3+CryptidA.wordInc (BB6.Agent35MarkerA.code q r)) j [])

#print axioms shape
#print axioms all_A_pair_terminal
end BB6.Agent35MarkerPairPacket
