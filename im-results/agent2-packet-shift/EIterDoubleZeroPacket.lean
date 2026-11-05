import Lean.Elab.Tactic.Omega
import EIterDoubleZeroFullFirst

set_option maxHeartbeats 15000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.Agent2EIterDoubleZeroPacket
open CryptidBoundary
open BB6.Agent2EGenericTurn
open BB6.Agent2EAltBoundaryFirst

def source (k q v r : Nat) (ys : List Bool) : Cfg :=
  init (List.replicate (3*k+2) true ++
    false :: (pairs (q+v+2) ++
      ([true,true,false] ++ (pairs r ++ (false::ys)))))

def target (k q v r : Nat) (ys : List Bool) : Cfg :=
  ⟨[],false,List.replicate (8*k+5) true ++
    (false :: (List.replicate (2*(q+v+2)+2) true ++
      (false :: (List.replicate (2*r+6) true ++ ys)))),5⟩

def duration (k q v r : Nat) : Nat :=
  12*k*k+49*k+4*q+4*v+4*r+68

private theorem pairs_add (m n : Nat) :
    pairs (m+n) = pairs m ++ pairs n := by
  induction m with
  | zero => simp [pairs]
  | succ m ih =>
    simp [Nat.succ_add,pairs,ih,List.append_assoc]

private theorem input_shape (k q v r : Nat) (ys : List Bool) :
    init (List.replicate (3*k+2) true ++
      false :: (pairs q ++
        (BB6.Agent2AIterDoubleZero.front v r ++ ys))) =
    source k q v r ys := by
  apply congrArg init
  simp only [source,BB6.Agent2AIterDoubleZero.front]
  rw [show q+v+2=q+(v+2) by omega]
  rw [pairs_add q (v+2)]
  simp [List.append_assoc]

private theorem output_shape (k q v r : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*k+3) true ++
      outPacket q (BB6.Agent2AIterDoubleZero.out v r) ys,5⟩ : Cfg) =
    target k q v r ys := by
  change (⟨[],false,List.replicate (8*k+3) true ++
      outPacket q (BB6.Agent2AIterDoubleZero.out v r) ys,5⟩ : Cfg) =
    ⟨[],false,List.replicate (8*k+5) true ++
      (false :: (List.replicate (2*(q+v+2)+2) true ++
        (false :: (List.replicate (2*r+6) true ++ ys)))),5⟩
  apply congrArg (fun zs : List Bool => (⟨[],false,zs,5⟩ : Cfg))
  have h8 : List.replicate (8*k+5) true =
      List.replicate (8*k+3) true ++ [true,true] := by
    rw [show 8*k+5=(8*k+3)+2 by omega,
        ← List.replicate_append_replicate]
    rfl
  have h2 : List.replicate (2*(q+v+2)+2) true =
      [true,true,true] ++
        (List.replicate (2*(q+1)) true ++
          List.replicate (2*v+1) true) := by
    rw [show 2*(q+v+2)+2=3+(2*(q+1)+(2*v+1)) by omega,
        ←List.replicate_append_replicate,
        ←List.replicate_append_replicate]
    rfl
  rw [h8,h2]
  simp [outPacket,BB6.Agent2AIterDoubleZero.out,List.append_assoc]
  rw [← List.append_assoc,List.replicate_append_replicate]

/-- Canonically normalized strict-first physical F/0 E return for every
    k,q,v,r and arbitrary tail Y. Input suffix starts
    (10)^(q+v+2) 110 (10)^r 0 Y, output starts
    0 1^(2(q+v+2)+2) 0 1^(2r+6) Y.
    The original six-state machine transition table is unchanged. -/
theorem first_physical_packet (k q v r : Nat) (ys : List Bool) :
    run (duration k q v r) (source k q v r ys) =
      target k q v r ys ∧
    ∀ t, 0<t → t<duration k q v r →
      ¬ Physical (run t (source k q v r ys)) := by
  have hs := input_shape k q v r ys
  have he := output_shape k q v r ys
  have ht : 12*k*k+49*k+(4*v+4*r+20)+48+4*q =
      duration k q v r := by
    dsimp [duration]
    omega
  have h := BB6.Agent2EIterDoubleZeroFullFirst.full_E_double_zero_first_physical
    k q v r ys
  dsimp at h
  rw [hs,he,ht] at h
  exact h

#print axioms first_physical_packet
end BB6.Agent2EIterDoubleZeroPacket
