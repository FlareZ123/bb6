import Lean.Elab.Tactic.Omega
import P2K2Source
import APacketMarkerShapes

set_option maxHeartbeats 15000000
set_option maxRecDepth 8192

namespace BB6.Agent31APacketMarkerSource
open CryptidBoundary BB6.Agent31PacketSource BB6.BoundaryPadding
open BB6.Agent31APacketMarker

private theorem sourceCode (ws : List Bool) :
    CryptidA.wordCode ws = BB6.Agent31P2K2.wordCode ws := by
  induction ws with
  | nil => rfl
  | cons b ws ih => cases b <;> simp [CryptidA.wordCode,BB6.Agent31P2K2.wordCode,ih]

private theorem sourceInc (ws : List Bool) :
    CryptidA.wordInc ws = BB6.Agent31P2K2.wordInc ws := by
  induction ws with
  | nil => rfl
  | cons b ws ih => cases b <;> simp [CryptidA.wordInc,BB6.Agent31P2K2.wordInc,ih]

private theorem sourceCost (m : Nat) (ws : List Bool) :
    CryptidA.wordCost m ws = BB6.Agent31P2K2.wordCost m ws := by
  induction ws generalizing m with
  | nil => rfl
  | cons b ws ih =>
    cases b
    · change 2+CryptidA.wordCost (m+1) ws = 2+BB6.Agent31P2K2.wordCost (m+1) ws
      rw [ih]
    · change 6*m+41+CryptidA.wordCost (m+4) ws = 6*m+41+BB6.Agent31P2K2.wordCost (m+4) ws
      rw [ih]

private theorem shifted_pairs (q : Nat) (ys : List Bool) :
    oppairs q ++ false :: ys = false :: (alt q ++ ys) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs,alt,List.append_assoc] using
      congrArg (List.cons false ∘ List.cons true) ih

private theorem packet_to_init (k q p : Nat) (ys : List Bool) :
    packet (3*k+3) q p ys =
      init (List.replicate (3*k+1) true ++ false ::
        (alt q ++ (List.replicate p true ++ ys))) := by
  have hn : List.replicate (3*k+3) true =
    true :: true :: List.replicate (3*k+1) true := by
    rw [show 3*k+3=2+(3*k+1) by omega,←List.replicate_append_replicate]
    rfl
  have hs := shifted_pairs q (List.replicate p true ++ ys)
  change (⟨[],false,List.replicate (3*k+3) true ++
     (oppairs q ++ (false :: (List.replicate p true ++ ys))),5⟩ : Cfg) = _
  rw [hn,hs]
  rfl

private theorem input_zero (k q r : Nat) :
    packet (3*k+3) q (3*r) BB6.Agent2PacketP2Reset.marker =
      init (List.replicate (3*k+1) true ++ false ::
        (CryptidA.wordCode (code q r) ++
        (false :: [true,false,true,false,true,true,true]))) := by
  rw [packet_to_init]
  have hw := split_zero q r
  rw [←sourceCode] at hw
  rw [show BB6.Agent2PacketP2Reset.marker = BB6.Agent31P2K2.marker by rfl]
  rw [hw]

private theorem input_two (k q r : Nat) :
    packet (3*k+3) q (3*r+2) BB6.Agent2PacketP2Reset.marker =
      init (List.replicate (3*k+1) true ++ false ::
        (CryptidA.wordCode (code q r) ++
         BB6.Agent26ACode.packet [])) := by
  rw [packet_to_init]
  have hw := split_two q r
  rw [←sourceCode] at hw
  rw [show BB6.Agent2PacketP2Reset.marker = BB6.Agent31P2K2.marker by rfl]
  rw [hw]
  rfl

private theorem input_one (k q r : Nat) :
    packet (3*k+3) q (3*r+1) BB6.Agent2PacketP2Reset.marker =
      init (List.replicate (3*k+1) true ++ false ::
        CryptidA.wordCode (codeTail q r)) := by
  rw [packet_to_init]
  have hw := split_one q r
  rw [←sourceCode] at hw
  rw [show BB6.Agent2PacketP2Reset.marker = BB6.Agent31P2K2.marker by rfl]
  rw [hw]

private theorem time_zero_source (k q r : Nat) :
    (12*k*k+41*k+32) +
      (CryptidA.wordCost (4*k+3) (code q r) +
       (2*(4*k+3+CryptidA.wordInc (code q r))+6)) =
      12*k*k+49*k+44+4*q+55*r+24*k*r+6*q*r+12*r*r := by
  have h := time_zero k q r
  dsimp only at h
  rw [←sourceCost,←sourceInc] at h
  exact h

private theorem time_two_source (k q r : Nat) :
    (12*k*k+41*k+32) +
      (CryptidA.wordCost (4*k+3) (code q r) +
       (2*(4*k+3+CryptidA.wordInc (code q r))+36)) =
      12*k*k+49*k+74+4*q+55*r+24*k*r+6*q*r+12*r*r := by
  have h := time_two k q r
  dsimp only at h
  rw [←sourceCost,←sourceInc] at h
  exact h

private theorem time_one_source (k q r : Nat) :
    (12*k*k+41*k+32) +
      (CryptidA.wordCost (4*k+3) (codeTail q r) +
       (2*(4*k+3+CryptidA.wordInc (codeTail q r))+6)) =
      12*k*k+73*k+141+10*q+79*r+24*k*r+6*q*r+12*r*r := by
  have h := time_one k q r
  dsimp only at h
  rw [←sourceCost,←sourceInc] at h
  exact h

/-- All-parameter original A packet marker p≡0, exact source step count. -/
theorem A_zero (k q r : Nat) :
    run (12*k*k+49*k+44+4*q+55*r+24*k*r+6*q*r+12*r*r)
      (packet (3*k+3) q (3*r) BB6.Agent2PacketP2Reset.marker) =
      ⟨[],false,List.replicate (8*k+2*q+8*r+11) true ++
       [true,false,true,false,true,true,true],5⟩ := by
  rw [←time_zero_source, input_zero]
  rw [BB6.Agent35.full_A_code]
  rw [show 2*(4*k+3+CryptidA.wordInc (code q r))+5 =
       8*k+2*q+8*r+11 by
    have h := out_zero k q r
    rw [←sourceInc] at h
    omega]

/-- All-parameter original A packet marker p≡2, exact source step count. -/
theorem A_two (k q r : Nat) :
    run (12*k*k+49*k+74+4*q+55*r+24*k*r+6*q*r+12*r*r)
      (packet (3*k+3) q (3*r+2) BB6.Agent2PacketP2Reset.marker) =
      ⟨[],false,List.replicate (8*k+2*q+8*r+11) true ++
       BB6.Agent26ACode.tail [],5⟩ := by
  rw [←time_two_source, input_two]
  rw [BB6.Agent26ACode.full_A_code_1101010111]
  rw [show 2*(4*k+3+CryptidA.wordInc (code q r))+5 =
       8*k+2*q+8*r+11 by
    have h := out_two k q r
    rw [←sourceInc] at h
    exact h]

/-- p≡1 requires one implicit physically blank trailing zero. -/
theorem A_one_physical (k q r : Nat) :
    ObsEq (run (12*k*k+73*k+141+10*q+79*r+24*k*r+6*q*r+12*r*r)
       (packet (3*k+3) q (3*r+1) BB6.Agent2PacketP2Reset.marker))
      ⟨[],false,List.replicate (8*k+2*q+8*r+25) true,5⟩ := by
  rw [←time_one_source, input_one]
  let ws : List Bool := codeTail q r
  let xs : List Bool := List.replicate (3*k+1) true ++ false :: CryptidA.wordCode ws
  have hpad := source_init_pad
    ((12*k*k+41*k+32)+
     (CryptidA.wordCost (4*k+3) ws +
        (2*(4*k+3+CryptidA.wordInc ws)+6))) 1 xs
  have hpadded :
    run ((12*k*k+41*k+32)+
     (CryptidA.wordCost (4*k+3) ws +
        (2*(4*k+3+CryptidA.wordInc ws)+6)))
      (init (xs ++ List.replicate 1 false)) =
      ⟨[],false,List.replicate (8*k+2*q+8*r+25) true,5⟩ := by
    have hshape : xs ++ List.replicate 1 false =
       List.replicate (3*k+1) true ++ false ::
         (CryptidA.wordCode ws ++ (false::[])) := by
      simp [xs,List.append_assoc]
    rw [hshape]
    have hh := BB6.Agent35.full_A_code k ws []
    rw [show 2*(4*k+3+CryptidA.wordInc ws)+5 =
        8*k+2*q+8*r+25 by
      have h := out_one k q r
      rw [←sourceInc] at h
      exact h] at hh
    simpa only [List.append_nil] using hh
  rw [hpadded] at hpad
  exact hpad

#print axioms A_zero
#print axioms A_two
#print axioms A_one_physical
end BB6.Agent31APacketMarkerSource
