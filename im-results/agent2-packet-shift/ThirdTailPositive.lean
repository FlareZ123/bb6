import Lean.Elab.Tactic.Omega
import ThirdTailFirst

namespace BB6.Agent2ThirdTailPositive
open CryptidBoundary BB6.BoundaryPadding
open BB6.Agent2ThirdTailPhysical BB6.Agent2ThirdTailFirst
open BB6.Agent2EAltBoundaryFirst

/-- The common positive-q packet reached from the third E reset tail. -/
def packetTarget (k q : Nat) : Cfg :=
  ⟨[],false,List.replicate (8*k+5) true ++
    (false :: (List.replicate (2*q+2) true ++
      (false :: List.replicate 14 true))),5⟩

private theorem q1_shape (k : Nat) :
    (⟨[],false,List.replicate (8*k+3) true ++
      ([true,true,false,true,true,true,true,false] ++
        List.replicate 14 true),5⟩ : Cfg) = packetTarget k 1 := by
  dsimp [packetTarget]
  have h : List.replicate (8*k+5) true =
      List.replicate (8*k+3) true ++ [true,true] := by
    rw [show 8*k+5=(8*k+3)+2 by omega,
      ← List.replicate_append_replicate]
    rfl
  rw [h]
  simp [List.append_assoc]

private theorem qplus_shape (k q : Nat) :
    BB6.Agent2EIterDoubleZeroPacket.target k 0 q 4 [] =
      packetTarget k (q+2) := by
  simp [BB6.Agent2EIterDoubleZeroPacket.target,packetTarget]

/-- Uniform all-natural positive-q original physical first-event statement:
    original F/0 start W(k,q) with q>=1, next source F/0 endpoint
    I_(8k+5)(0 1^(2q+2) 0 1^14) in 12k²+49k+76+4q raw steps.
    Proof imports the strictly first implicit-padding branches. -/
theorem positive_first (k q : Nat) :
    let t := 12*k*k+49*k+76+4*(q+1)
    ObsEq (run t (init (thirdWord k (q+1))))
      (packetTarget k (q+1)) ∧
    ∀ u, 0<u → u<t →
      ¬ Physical (run u (init (thirdWord k (q+1)))) := by
  dsimp
  cases q with
  | zero =>
    have h := third_first_q1 k
    simpa only [Nat.zero_add, Nat.add_zero, Nat.mul_one, q1_shape,
      show 12*k*k+49*k+76+4*1=12*k*k+49*k+80 by omega] using h
  | succ q =>
    have h := third_first_qge2 k q
    have hh : q.succ+1=q+2 := by omega
    rw [hh]
    simpa only [qplus_shape,
      show 12*k*k+49*k+76+4*(q+2)=12*k*k+49*k+84+4*q by omega]
      using h

#print axioms positive_first
end BB6.Agent2ThirdTailPositive
