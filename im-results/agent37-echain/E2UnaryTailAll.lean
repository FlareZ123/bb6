import Lean.Elab.Tactic.Omega
import EGenericTurn
import PacketSource

set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

namespace BB6.Agent37E2UnaryTail
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2EGenericTurn

/-- E,p=2 frontier when the packet tail starts with 0,111 and a bit. -/
private def front (b : Bool) : List Bool :=
  [true,true,false,true,true,true,b]

/-- The complete 20-step A/0-to-C/1 turn, before a universal C-pair pump. -/
private def turned (b : Bool) : List Bool :=
  if b then [true,false,true,false,true,false,true]
       else [true,false,true,false,true,false]

/-- The corresponding packet suffix after converting one more leading
    one into the unary block. -/
private def tail (b : Bool) : List Bool :=
  if b then [false,true,false,true,false,true]
       else [false,true,false,true,false]

/-- The input's arbitrary left tape is untouched; the binary fourth
    marker bit changes only the end of the output word. -/
theorem local_turn (L ys : List Bool) (b : Bool) :
    run 20 (⟨L,false,front b ++ ys,0⟩ : Cfg) =
      ⟨L,true,turned b ++ ys,2⟩ := by
  cases b <;>
    simp [front,turned,run,step,goL,goR,List.append_assoc]

private theorem oppairsFalse (q : Nat) :
    oppairs q ++ [false] = false :: pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
      simpa [oppairs,pairs,List.append_assoc] using
        congrArg (fun xs : List Bool => false :: true :: xs) ih

private theorem prefixOnes (k : Nat) :
    List.replicate (3*k+4) true =
      [true,true] ++ List.replicate (3*k+2) true := by
  rw [show 3*k+4=2+(3*k+2) by omega,
      ← List.replicate_append_replicate]
  rfl

private theorem outputOnes (k : Nat) :
    List.replicate (8*k+5) true =
      List.replicate (8*k+3) true ++ [true,true] := by
  rw [show 8*k+5=(8*k+3)+2 by omega,
      ← List.replicate_append_replicate]
  rfl

private theorem inputShape (k q : Nat) (b : Bool) (ys : List Bool) :
    packet (3*k+4) q 2 (false :: true :: true :: true :: b :: ys) =
      init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ (front b ++ ys))) := by
  have hw :
      oppairs q ++ (false :: (List.replicate 2 true ++
          (false :: true :: true :: true :: b :: ys))) =
        false :: (pairs q ++ (front b ++ ys)) := by
    calc
      _ = (oppairs q ++ [false]) ++ (List.replicate 2 true ++
            (false :: true :: true :: true :: b :: ys)) := by
              simp [List.append_assoc]
      _ = _ := by
        rw [oppairsFalse]
        simp [front,List.replicate,List.append_assoc]
  simp only [packet,word,init]
  rw [prefixOnes, hw]
  simp [List.append_assoc]

private theorem turned_eq (b : Bool) :
    turned b = true :: tail b := by
  cases b <;> rfl

private theorem ones_q (q : Nat) :
    [true,true,true] ++ (List.replicate (2*(q+1)) true ++ [true]) =
      List.replicate (2*q+6) true := by
  calc
    _ = List.replicate 3 true ++
          (List.replicate (2*(q+1)) true ++ List.replicate 1 true) := rfl
    _ = (List.replicate 3 true ++ List.replicate (2*(q+1)) true) ++
          List.replicate 1 true := by rw [List.append_assoc]
    _ = List.replicate (3+2*(q+1)) true ++ List.replicate 1 true := by
          rw [List.replicate_append_replicate]
    _ = List.replicate (3+2*(q+1)+1) true := by
          rw [List.replicate_append_replicate]
    _ = _ := by congr 1; omega

private theorem outputShape (k q : Nat) (b : Bool) (ys : List Bool) :
    (⟨[],false,List.replicate (8*k+3) true ++
      outPacket q (turned b) ys,5⟩ : Cfg) =
      packet (8*k+5) 0 (2*q+6) (tail b ++ ys) := by
  have hword :
      List.replicate (8*k+3) true ++ outPacket q (turned b) ys =
      List.replicate (8*k+5) true ++
        (false :: (List.replicate (2*q+6) true ++ (tail b ++ ys))) := by
    calc
      _ = List.replicate (8*k+3) true ++
          ([true,true] ++
             (false :: (([true,true,true] ++
                 (List.replicate (2*(q+1)) true ++ [true])) ++
                 (tail b ++ ys)))) := by
              cases b <;>
                simp [outPacket,turned,tail,List.append_assoc]
      _ = List.replicate (8*k+3) true ++
          ([true,true] ++
             (false :: (List.replicate (2*q+6) true ++
                 (tail b ++ ys)))) := by rw [ones_q]
      _ = _ := by rw [outputOnes]; simp [List.append_assoc]
  simpa [packet,word,oppairs] using
    congrArg (fun rs : List Bool => (⟨[],false,rs,5⟩ : Cfg)) hword

/-- Original D-machine all-q E-two rule when the right packet starts
    0,111,b: source-accurate primitive count, arbitrary k and q, all
    binary suffixes, and an explicit branch on the next bit. -/
theorem e_two_111_all (k q : Nat) (b : Bool) (ys : List Bool) :
    run (12*k*k+49*k+68+4*q)
      (packet (3*k+4) q 2
        (false :: true :: true :: true :: b :: ys)) =
      packet (8*k+5) 0 (2*q+6) (tail b ++ ys) := by
  rw [inputShape]
  have ht : 12*k*k+49*k+68+4*q =
      12*k*k+49*k+20+48+4*q := by omega
  rw [ht]
  rw [BB6.Agent2EGenericTurn.full_E_from_turn k q 20
      (front b) (turned b) ys
      (fun L => local_turn L ys b)]
  exact outputShape k q b ys

/-- Bit-zero branch without any restriction on the alternating depth. -/
theorem e_two_1110 (k q : Nat) (ys : List Bool) :
    run (12*k*k+49*k+68+4*q)
      (packet (3*k+4) q 2
        (false :: true :: true :: true :: false :: ys)) =
      packet (8*k+5) 0 (2*q+6)
        ([false,true,false,true,false] ++ ys) :=
  e_two_111_all k q false ys

/-- Bit-one branch without any restriction on the alternating depth. -/
theorem e_two_1111 (k q : Nat) (ys : List Bool) :
    run (12*k*k+49*k+68+4*q)
      (packet (3*k+4) q 2
        (false :: true :: true :: true :: true :: ys)) =
      packet (8*k+5) 0 (2*q+6)
        ([false,true,false,true,false,true] ++ ys) :=
  e_two_111_all k q true ys

#print axioms local_turn
#print axioms e_two_111_all
#print axioms e_two_1110
#print axioms e_two_1111

end BB6.Agent37E2UnaryTail
