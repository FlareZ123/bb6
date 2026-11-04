import Lean.Elab.Tactic.Omega
import APacketGeneral

namespace BB6.Agent35PacketAZero
open CryptidBoundary BB6.Agent31PacketSource CryptidA
open BB6.Agent35APacketGeneral
set_option maxHeartbeats 10000000

def duration (k q r : Nat) : Nat :=
  (12*k*k+41*k+32) +
    (wordCost (4*k+3) (ws q r) +
      (2*(4*k+3+q+4*r)+6))

private theorem code_ones (r : Nat) :
    wordCode (List.replicate r true) = List.replicate (3*r) true := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change [true,true,true] ++ wordCode (List.replicate r true) =
      List.replicate (3*(r+1)) true
    rw [ih]
    have h : 3*(r+1)=3+3*r := by omega
    rw [h,(List.replicate_append_replicate).symm]
    rfl

private theorem right_word (q r : Nat) :
    word q (3*r) ys =
      false :: (wordCode (ws q r) ++ ys) := by
  calc
    word q (3*r) ys =
        (oppairs q ++ [false]) ++
          (List.replicate (3*r) true ++ ys) := by
      simp [word,List.append_assoc]
    _ = (false :: wordCode (List.replicate q false)) ++
          (wordCode (List.replicate r true) ++ ys) := by
      rw [oppairs_false,code_ones]
    _ = false :: (wordCode (ws q r) ++ ys) := by
      simp [ws,code_append,List.append_assoc]

private theorem start (k q r : Nat) :
    packet (3*k+3) q (3*r) ys =
    init (List.replicate (3*k+1) true ++
      false :: (wordCode (ws q r) ++ ys)) := by
  have hn : List.replicate (3*k+3) true =
      true :: true :: List.replicate (3*k+1) true := by
    have h : 3*k+3=2+(3*k+1) := by omega
    calc
      _ = List.replicate (2+(3*k+1)) true :=
        congrArg (fun n : Nat => List.replicate n true) h
      _ = List.replicate 2 true ++ List.replicate (3*k+1) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  unfold packet
  rw [hn,right_word]
  simp [init,List.append_assoc]

/-- Exact original-source A boundary output for every p=3r packet. -/
theorem source_a_packet_zero_raw (k q r : Nat) :
    run (duration k q r) (packet (3*k+3) q (3*r) ys) =
    (⟨[],false,List.replicate (2*(4*k+3+q+4*r)+5) true ++
      List.replicate 6 true,5⟩ : CryptidBoundary.Cfg) := by
  have hc : duration k q r =
      (12*k*k+41*k+32) +
        (wordCost (4*k+3) (ws q r) +
          (2*(4*k+3+wordInc (ws q r))+6)) := by
    rw [inc_ws q r]
    simp [duration,Nat.add_assoc]
  rw [start,hc]
  have h := BB6.Agent35.full_A_code k (ws q r) (List.replicate 6 true)
  rw [inc_ws q r] at h
  exact h

#print axioms source_a_packet_zero_raw
end BB6.Agent35PacketAZero
