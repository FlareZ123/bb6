import Box15HardProof
import MirrorTransport4
import BlockFARBridge4
import Box15Source
import WeightedTNF
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent17Box15Hard
open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent17Raw10BoxFar
open BB6BlockFAR4
def machine : Table := mirrorTable Box15Hard.machine
def row : PartialMachine := fun s =>
  let v := [8,21,11,6,17,13,11,19,3,2,15,0][2*s.1.val+s.2.toNat]!
  if v=0 then none else some (decodeCode (Fin.ofNat 25 v))
theorem table_exact (s : Slot) : partialTable machine s = row s := by
  rcases s with ⟨q,b⟩
  revert q b
  decide
theorem local_never : ∀ n, ∃ c, BB6BlockFAR4.run machine n primBlank = some c :=
  never_of_mirror machine (by simpa only [machine,mirrorTable_involutive] using Box15Hard.never)
theorem source_never (m : Machine) (hm : compatible row m) : NeverHalts m := by
  apply transfer_never machine m
  · intro s t ht
    exact hm s t (by rwa [table_exact] at ht)
  · exact local_never
theorem weighted (B : Nat) (m : Machine) (hm : compatible row m) : WeightedBound B m :=
  weighted_never B m (source_never m hm)
#print axioms local_never
#print axioms table_exact
#print axioms source_never
#print axioms weighted
end BB6.Agent17Box15Hard
