import Lean.Elab.Tactic.Omega
import PacketPaths
import ATurnFamily

set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

namespace BB6.Agent2EAltPacket
open CryptidBoundary BB6.Agent31PacketSource BB6.Agent31PacketPaths

/-- The complete alternating-tail family, including two known special cases. -/
def initialTail (r : Nat) (ys : List Bool) : List Bool :=
  oppairs (r+1) ++ ([true,true] ++ ys)

/-- One more alternating pair, followed by the new zero delimiter. -/
def finalTail (r : Nat) (ys : List Bool) : List Bool :=
  oppairs (r+2) ++ (false :: ys)

private theorem swap (q : Nat) (ys : List Bool) :
    oppairs q ++ false :: ys = false :: (pairs q ++ ys) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs, pairs, List.append_assoc] using
      congrArg (List.cons false ∘ List.cons true) ih

private theorem pair_to_oppairs (n : Nat) (ys : List Bool) :
    pairs (n+1) ++ ys = true :: (oppairs n ++ (false::ys)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pairs,oppairs,List.cons_append]
    exact congrArg (fun x : List Bool => true::false::x) ih

private theorem input_word (k q r : Nat) (ys : List Bool) :
    List.replicate (3*k+4) true ++
      (oppairs q ++ false :: (List.replicate 2 true ++ initialTail r ys)) =
    [true,true] ++
      (List.replicate (3*k+2) true ++
        (false :: (pairs q ++ (BB6.Agent2ATurnFamily.front (r+1) ++ ys)))) := by
  have hn : List.replicate (3*k+4) true =
      true :: true :: List.replicate (3*k+2) true := by
    rw [show 3*k+4=2+(3*k+2) by omega,
        ←List.replicate_append_replicate]
    rfl
  simp [initialTail, BB6.Agent2ATurnFamily.front, hn]
  rw [swap q]

private theorem input_shape (k q r : Nat) (ys : List Bool) :
    physical (⟨3*k+4,q,2⟩ : State) (initialTail r ys) =
      init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ (BB6.Agent2ATurnFamily.front (r+1) ++ ys))) := by
  change (⟨[],false,
      List.replicate (3*k+4) true ++
        (oppairs q ++ false :: (List.replicate 2 true ++ initialTail r ys)),5⟩ : Cfg) =
    ⟨[],false,
      [true,true] ++
        (List.replicate (3*k+2) true ++
          (false :: (pairs q ++ (BB6.Agent2ATurnFamily.front (r+1) ++ ys)))),5⟩
  exact congrArg (fun w : List Bool => (⟨[],false,w,5⟩ : Cfg)) (input_word k q r ys)

private theorem output_word (k q r : Nat) (ys : List Bool) :
    List.replicate (8*k+3) true ++
      BB6.Agent2EGenericTurn.outPacket q (pairs (r+3)) ys =
    List.replicate (8*k+5) true ++
      (false :: (List.replicate (2*q+6) true ++ finalTail r ys)) := by
  rw [show r+3 = (r+2)+1 by omega]
  simp only [BB6.Agent2EGenericTurn.outPacket, finalTail,
    List.append_assoc, pair_to_oppairs]
  have h5 : List.replicate (8*k+5) true =
      List.replicate (8*k+3) true ++ [true,true] := by
    rw [show 8*k+5 = (8*k+3)+2 by omega]
    rw [← List.replicate_append_replicate]
    rfl
  have hq : List.replicate (2*q+6) true =
      [true,true,true] ++ List.replicate (2*(q+1)) true ++ [true] := by
    change List.replicate (2*q+6) true =
      (List.replicate 3 true ++ List.replicate (2*(q+1)) true) ++
        List.replicate 1 true
    rw [List.replicate_append_replicate,List.replicate_append_replicate]
    congr 1
    omega
  rw [h5,hq]
  simp [List.append_assoc]

private theorem output_shape (k q r : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*k+3) true ++
      BB6.Agent2EGenericTurn.outPacket q (pairs (r+3)) ys,5⟩ : Cfg) =
    physical (⟨8*k+5,0,2*q+6⟩ : State) (finalTail r ys) := by
  change (⟨[],false,List.replicate (8*k+3) true ++
    BB6.Agent2EGenericTurn.outPacket q (pairs (r+3)) ys,5⟩ : Cfg) =
    ⟨[],false,List.replicate (8*k+5) true ++
      (false :: (List.replicate (2*q+6) true ++ finalTail r ys)),5⟩
  exact congrArg (fun w : List Bool => (⟨[],false,w,5⟩ : Cfg)) (output_word k q r ys)

/-- An infinite family of literal original-machine E low-p packet exits.
    Input tail (01)^(r+1) 11 Y becomes (01)^(r+2) 0 Y.
    All k,q,r and arbitrary Y are quantified; no blank-root assumption. -/
theorem e_alternating_source (k q r : Nat) (ys : List Bool) :
    run (12*k*k+49*k+6*(r+1)+62+4*q)
      (physical (⟨3*k+4,q,2⟩ : State) (initialTail r ys)) =
    physical (⟨8*k+5,0,2*q+6⟩ : State) (finalTail r ys) := by
  rw [input_shape]
  rw [BB6.Agent2ATurnFamily.full_E_alternating_family]
  exact output_shape k q r ys

#print axioms e_alternating_source
end BB6.Agent2EAltPacket
