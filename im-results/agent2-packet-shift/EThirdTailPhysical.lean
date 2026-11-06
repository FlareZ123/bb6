import Lean.Elab.Tactic.Omega
import BoundaryPadding
import EZeroPump
import EOneZero
import EIterDoubleZeroPacket

set_option maxHeartbeats 15000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.Agent2ThirdTailPhysical
open CryptidBoundary
open BB6.BoundaryPadding

/-- The boundary word after the second alternating-tail E reset. -/
def thirdTail : List Bool :=
  [false,true,false,true,false,true,false,true,false]

private theorem tail_decomp :
    [true,true] ++ thirdTail =
      [true,true,false] ++ pairs 4 := by rfl

/-- Original F/0 input, with its terminal zero physically implicit. -/
def thirdWord (k q : Nat) : List Bool :=
  List.replicate (3*k+2) true ++
    (false :: (pairs q ++ ([true,true] ++ thirdTail)))

private theorem padded_shape (k q : Nat) :
    init (thirdWord k q ++ [false]) =
      init (List.replicate (3*k+2) true ++
        (false :: (pairs q ++ ([true,true,false] ++
          (pairs 4 ++ [false]))))) := by
  apply congrArg init
  simp [thirdWord,thirdTail,pairs,List.append_assoc]

/-- Convert an explicit exact original-machine endpoint into a true physical
    section theorem for the omitted final blank, using source bisimulation. -/
private theorem source_implicit (t : Nat) (xs : List Bool) (target : Cfg)
    (h : run t (init (xs ++ [false])) = target) :
    ObsEq (run t (init xs)) target := by
  have hp := source_init_pad t 1 xs
  simpa only [List.replicate_one, h] using hp

/-- q=0 third-tail exceptional E return with no artificial terminal
    right-hand zero in the physical starting tape. -/
theorem third_q0 (k : Nat) :
    ObsEq
      (run (12*k*k+49*k+112) (init (thirdWord k 0)))
      (⟨[],false,List.replicate (8*k+3) true ++
        (BB6.Agent32EZero.packetZero ++
          List.replicate 8 true),5⟩ : Cfg) := by
  apply source_implicit
  rw [padded_shape]
  simpa [pairs,List.append_assoc] using
    (BB6.Agent2EZeroPump.full_exceptional_pump k 4 [])

/-- q=1 third-tail E return. Its source route differs from q=0 and q≥2. -/
theorem third_q1 (k : Nat) :
    ObsEq
      (run (12*k*k+49*k+80) (init (thirdWord k 1)))
      (⟨[],false,List.replicate (8*k+3) true ++
        ([true,true,false,true,true,true,true,false] ++
          List.replicate 14 true),5⟩ : Cfg) := by
  apply source_implicit
  rw [padded_shape]
  simpa [pairs,List.append_assoc] using
    (BB6.Agent2EOneZero.full_one_zero k 4 [])

/-- Every q≥2 third-tail E boundary has the exact original-machine
    physical right tape claimed by the previously proved q≥2 family. -/
theorem third_qge2 (k q : Nat) :
    ObsEq
      (run (12*k*k+49*k+84+4*q)
        (init (thirdWord k (q+2))))
      (BB6.Agent2EIterDoubleZeroPacket.target k 0 q 4 []) := by
  apply source_implicit
  rw [padded_shape]
  have h :=
    (BB6.Agent2EIterDoubleZeroPacket.first_physical_packet k 0 q 4 []).1
  have ht : 12*k*k+49*k+84+4*q =
      BB6.Agent2EIterDoubleZeroPacket.duration k 0 q 4 := by
    dsimp [BB6.Agent2EIterDoubleZeroPacket.duration]
    omega
  rw [ht]
  have hsource :
      init (List.replicate (3*k+2) true ++
        (false :: (pairs (q+2) ++ ([true,true,false] ++
          (pairs 4 ++ [false]))))) =
      BB6.Agent2EIterDoubleZeroPacket.source k 0 q 4 [] := by
    simp [BB6.Agent2EIterDoubleZeroPacket.source]
  rw [hsource]
  exact h

#print axioms third_q0
#print axioms third_q1
#print axioms third_qge2
end BB6.Agent2ThirdTailPhysical
