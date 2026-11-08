import Lean.Elab.Tactic.Omega
import PacketAUniformShapes
import PacketSource
import A1101010111Code
import BoundaryPadding

set_option maxHeartbeats 15000000
set_option maxRecDepth 8192

namespace BB6.Agent37PacketAUniformSource
open CryptidBoundary BB6.Agent31PacketSource

private theorem sourceCode (ws : List Bool) :
    CryptidA.wordCode ws = BB6.Agent37PacketAUniformShapes.wordCode ws := by
  induction ws with
  | nil => rfl
  | cons b ws ih => cases b <;> simp [CryptidA.wordCode,BB6.Agent37PacketAUniformShapes.wordCode,ih]

private theorem sourcePairs (q : Nat) :
    CryptidBoundary.pairs q = BB6.Agent37PacketAUniformShapes.pairs q := by
  induction q with
  | zero => rfl
  | succ q ih => simp [CryptidBoundary.pairs,BB6.Agent37PacketAUniformShapes.pairs,ih]

private theorem swap (q : Nat) (ys : List Bool) :
    oppairs q ++ false :: ys = false :: (pairs q ++ ys) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs,pairs,List.append_assoc] using
      congrArg (fun xs : List Bool => false :: true :: xs) ih

private theorem source_word_zero (q r : Nat) :
    pairs q ++ (List.replicate (3*r) true ++ BB6.Agent37PacketAUniformShapes.marker) =
    CryptidA.wordCode (BB6.Agent37PacketAUniformShapes.code q r) ++
      (false :: [true,false,true,false,true,true,true]) := by
  rw [sourcePairs, sourceCode]
  exact BB6.Agent37PacketAUniformShapes.residue_zero_word q r

private theorem source_word_one (q r : Nat) :
    pairs q ++ (List.replicate (3*r+1) true ++ BB6.Agent37PacketAUniformShapes.marker) =
    CryptidA.wordCode (BB6.Agent37PacketAUniformShapes.codeTail q r) := by
  rw [sourcePairs,sourceCode]
  exact BB6.Agent37PacketAUniformShapes.residue_one_word q r

private theorem source_word_two (q r : Nat) :
    pairs q ++ (List.replicate (3*r+2) true ++ BB6.Agent37PacketAUniformShapes.marker) =
    CryptidA.wordCode (BB6.Agent37PacketAUniformShapes.code q r) ++
      [true,true,false,true,false,true,false,true,true,true] := by
  rw [sourcePairs, sourceCode]
  exact BB6.Agent37PacketAUniformShapes.residue_two_word q r

private theorem packetAsInit (k q p : Nat) (ys : List Bool) :
    packet (3*k+3) q p ys =
    init (List.replicate (3*k+1) true ++ false ::
       (pairs q ++ (List.replicate p true ++ ys))) := by
  have hn : 3*k+3 = 2+(3*k+1) := by omega
  simp only [packet,word,init]
  rw [hn, ←List.replicate_append_replicate]
  simp only [List.replicate]
  rw [swap]
  simp [List.append_assoc]

private theorem shape_zero (k q r : Nat) :
    packet (3*k+3) q (3*r) BB6.Agent37PacketAUniformShapes.marker =
    init (List.replicate (3*k+1) true ++ false ::
      (CryptidA.wordCode (BB6.Agent37PacketAUniformShapes.code q r) ++
       (false :: [true,false,true,false,true,true,true]))) := by
  rw [packetAsInit,source_word_zero]

private theorem shape_one (k q r : Nat) :
    packet (3*k+3) q (3*r+1) BB6.Agent37PacketAUniformShapes.marker =
    init (List.replicate (3*k+1) true ++ false ::
       CryptidA.wordCode (BB6.Agent37PacketAUniformShapes.codeTail q r)) := by
  rw [packetAsInit,source_word_one]

private theorem shape_two (k q r : Nat) :
    packet (3*k+3) q (3*r+2) BB6.Agent37PacketAUniformShapes.marker =
    init (List.replicate (3*k+1) true ++ false ::
       (CryptidA.wordCode (BB6.Agent37PacketAUniformShapes.code q r) ++
        [true,true,false,true,false,true,false,true,true,true])) := by
  rw [packetAsInit,source_word_two]

/-- Every A-state fixed-marker packet with p divisible by three reaches a
    regular alternating F/0 section. Both q and r are arbitrary. -/
theorem packet_a_zero (k q r : Nat) :
    let ws := BB6.Agent37PacketAUniformShapes.code q r
    let m := 4*k+3+CryptidA.wordInc ws
    let elapsed := (12*k*k+41*k+32)+
      (CryptidA.wordCost (4*k+3) ws + (2*m+6))
    run elapsed (packet (3*k+3) q (3*r) BB6.Agent37PacketAUniformShapes.marker) =
      ⟨[],false,List.replicate (2*m+5) true ++
        [true,false,true,false,true,true,true],5⟩ := by
  dsimp only
  rw [shape_zero]
  exact BB6.Agent35.full_A_code k (BB6.Agent37PacketAUniformShapes.code q r)
    [true,false,true,false,true,true,true]

/-- The residue-two packet reaches a regular alternating right suffix after
    applying the original arbitrary codeword 1101010111 completion. -/
theorem packet_a_two (k q r : Nat) :
    let ws := BB6.Agent37PacketAUniformShapes.code q r
    let m := 4*k+3+CryptidA.wordInc ws
    let elapsed := (12*k*k+41*k+32)+
      (CryptidA.wordCost (4*k+3) ws + (2*m+36))
    run elapsed (packet (3*k+3) q (3*r+2) BB6.Agent37PacketAUniformShapes.marker) =
      ⟨[],false,List.replicate (2*m+5) true ++ BB6.Agent26ACode.tail [],5⟩ := by
  dsimp only
  rw [shape_two]
  simpa only [BB6.Agent26ACode.packet,List.append_nil] using
    (BB6.Agent26ACode.full_A_code_1101010111 k
      (BB6.Agent37PacketAUniformShapes.code q r) [])

/-- The residue-one packet consumes an implicit physical blank with a final
    source A code token. Result is pure unary up to padding equivalence. -/
theorem packet_a_one_physical (k q r : Nat) :
    let ws := BB6.Agent37PacketAUniformShapes.codeTail q r
    let xs := List.replicate (3*k+1) true ++ false :: CryptidA.wordCode ws
    let m := 4*k+3+CryptidA.wordInc ws
    let elapsed := (12*k*k+41*k+32)+
      (CryptidA.wordCost (4*k+3) ws + (2*m+6))
    BB6.BoundaryPadding.ObsEq
      (run elapsed (packet (3*k+3) q (3*r+1) BB6.Agent37PacketAUniformShapes.marker))
      ⟨[],false,List.replicate (2*m+5) true,5⟩ := by
  dsimp only
  rw [shape_one]
  let ws : List Bool := BB6.Agent37PacketAUniformShapes.codeTail q r
  let xs : List Bool := List.replicate (3*k+1) true ++ false :: CryptidA.wordCode ws
  let elapsed : Nat := (12*k*k+41*k+32)+
    (CryptidA.wordCost (4*k+3) ws+
       (2*(4*k+3+CryptidA.wordInc ws)+6))
  have hpad := BB6.BoundaryPadding.source_init_pad elapsed 1 xs
  have hpadded :
      run elapsed (init (xs ++ List.replicate 1 false)) =
        ⟨[],false,List.replicate (2*(4*k+3+CryptidA.wordInc ws)+5) true,5⟩ := by
    have hshape : xs ++ List.replicate 1 false =
        List.replicate (3*k+1) true ++ false ::
          (CryptidA.wordCode ws ++ (false::[])) := by
      simp [xs,List.append_assoc]
    rw [hshape]
    exact BB6.Agent35.full_A_code k ws []
  rw [hpadded] at hpad
  exact hpad

#print axioms packet_a_zero
#print axioms packet_a_two
#print axioms packet_a_one_physical

end BB6.Agent37PacketAUniformSource
