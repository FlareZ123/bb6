import LongCycle
import TripleSweep
import Sweep9135
import Sweep14327
import OLFWidth5952
import OLFWidth17162
import OLFSparseWidth1352
set_option maxHeartbeats 0
namespace BB6.Agent6OneLFExceptional
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent31ThreeHole
private theorem liftNever (p q : PartialMachine) (h : tableOK p q = true)
    (never : ∀ m, compatible q m → NeverHalts m) : Cover (WeightedBound 90794) p := by
  rw [tableOK_sound p q h]
  exact .leaf q (fun m hm => weighted_never 90794 m (never m hm))
def pH1352 : PartialMachine := fromCodes [7, 3, 11, 5, 14, 23, 24, 16, 22, 11, 0, 13]
theorem cH1352 : Cover (WeightedBound 90794) pH1352 :=
  liftNever pH1352 BB6.Agent6OneLFSparseWidth5.H1352.ctr (by decide +kernel) BB6.Agent6OneLFSparseWidth5.H1352.never
#print axioms cH1352
def pH4231 : PartialMachine := fromCodes [7, 2, 11, 1, 14, 19, 24, 16, 22, 11, 1, 8]
theorem cH4231 : Cover (WeightedBound 90794) pH4231 :=
  liftNever pH4231 (BB6.Agent6OneLFTriple.p .a) (by decide +kernel) (BB6.Agent6OneLFTriple.never .a)
#print axioms cH4231
def pH5952 : PartialMachine := fromCodes [7, 5, 11, 3, 14, 13, 24, 16, 22, 11, 5, 18]
theorem cH5952 : Cover (WeightedBound 90794) pH5952 :=
  liftNever pH5952 BB6.Agent6OneLFWidth5.H5952.ctr (by decide +kernel) BB6.Agent6OneLFWidth5.H5952.never
#print axioms cH5952
def pH9135 : PartialMachine := fromCodes [7, 21, 11, 5, 14, 3, 24, 16, 22, 11, 2, 15]
theorem cH9135 : Cover (WeightedBound 90794) pH9135 :=
  liftNever pH9135 BB6.Agent6OneLF9135.p (by decide +kernel) BB6.Agent6OneLF9135.never
#print axioms cH9135
def pH14327 : PartialMachine := fromCodes [7, 21, 11, 13, 14, 24, 23, 16, 22, 11, 3, 12]
theorem cH14327 : Cover (WeightedBound 90794) pH14327 :=
  liftNever pH14327 BB6.Agent6OneLF14327.p (by decide +kernel) BB6.Agent6OneLF14327.never
#print axioms cH14327
def pH15496 : PartialMachine := fromCodes [7, 2, 11, 1, 14, 19, 24, 16, 22, 11, 7, 8]
theorem cH15496 : Cover (WeightedBound 90794) pH15496 :=
  liftNever pH15496 (BB6.Agent6OneLFTriple.p .b) (by decide +kernel) (BB6.Agent6OneLFTriple.never .b)
#print axioms cH15496
def pH15542 : PartialMachine := fromCodes [7, 22, 11, 1, 14, 19, 24, 16, 22, 11, 7, 8]
theorem cH15542 : Cover (WeightedBound 90794) pH15542 :=
  liftNever pH15542 (BB6.Agent6OneLFTriple.p .c) (by decide +kernel) (BB6.Agent6OneLFTriple.never .c)
#print axioms cH15542
def pH17162 : PartialMachine := fromCodes [7, 24, 11, 21, 14, 7, 1, 16, 22, 11, 11, 13]
theorem cH17162 : Cover (WeightedBound 90794) pH17162 :=
  liftNever pH17162 BB6.Agent6OneLFWidth5.H17162.ctr (by decide +kernel) BB6.Agent6OneLFWidth5.H17162.never
#print axioms cH17162
def pH10068 : PartialMachine := fromCodes [7, 7, 11, 7, 14, 17, 24, 16, 22, 11, 2, 10]
theorem cH10068 : Cover (WeightedBound 90794) pH10068 := by
  rw [tableOK_sound pH10068 BB6.Agent6OneLFLongCycle.pH10068 (by decide +kernel)]
  exact BB6.Agent6OneLFLongCycle.cH10068
#print axioms cH10068
def pH10708 : PartialMachine := fromCodes [7, 24, 11, 7, 14, 17, 2, 16, 22, 11, 6, 10]
theorem cH10708 : Cover (WeightedBound 90794) pH10708 := by
  rw [tableOK_sound pH10708 BB6.Agent6OneLFLongCycle.pH10708 (by decide +kernel)]
  exact BB6.Agent6OneLFLongCycle.cH10708
#print axioms cH10708
def pH12373 : PartialMachine := fromCodes [7, 2, 11, 13, 14, 24, 1, 16, 22, 11, 14, 20]
theorem cH12373 : Cover (WeightedBound 90794) pH12373 := by
  rw [tableOK_sound pH12373 BB6.Agent6OneLFLongCycle.pH12373 (by decide +kernel)]
  exact BB6.Agent6OneLFLongCycle.cH12373
#print axioms cH12373
def pH14336_8 : PartialMachine := fromCodes [7, 21, 11, 3, 14, 8, 24, 16, 22, 11, 3, 20]
theorem cH14336_8 : Cover (WeightedBound 90794) pH14336_8 := by
  rw [tableOK_sound pH14336_8 BB6.Agent6OneLFLongCycle.pH14336_8 (by decide +kernel)]
  exact BB6.Agent6OneLFLongCycle.cH14336_8
#print axioms cH14336_8
def pH14336_13 : PartialMachine := fromCodes [7, 21, 11, 3, 14, 13, 24, 16, 22, 11, 3, 20]
theorem cH14336_13 : Cover (WeightedBound 90794) pH14336_13 := by
  rw [tableOK_sound pH14336_13 BB6.Agent6OneLFLongCycle.pH14336_13 (by decide +kernel)]
  exact BB6.Agent6OneLFLongCycle.cH14336_13
#print axioms cH14336_13
def pH14336_10 : PartialMachine := fromCodes [7, 21, 11, 3, 14, 10, 24, 16, 22, 11, 3, 20]
theorem cH14336_10 : Cover (WeightedBound 90794) pH14336_10 := by
  rw [tableOK_sound pH14336_10 BB6.Agent6OneLFLongCycle.pH14336_10 (by decide +kernel)]
  exact BB6.Agent6OneLFLongCycle.cH14336_10
#print axioms cH14336_10
def pH14875 : PartialMachine := fromCodes [7, 3, 11, 10, 14, 17, 24, 16, 22, 11, 3, 10]
theorem cH14875 : Cover (WeightedBound 90794) pH14875 := by
  rw [tableOK_sound pH14875 BB6.Agent6OneLFLongCycle.pH14875 (by decide +kernel)]
  exact BB6.Agent6OneLFLongCycle.cH14875
#print axioms cH14875
def pH14896 : PartialMachine := fromCodes [7, 3, 11, 11, 14, 17, 24, 16, 22, 11, 3, 10]
theorem cH14896 : Cover (WeightedBound 90794) pH14896 := by
  rw [tableOK_sound pH14896 BB6.Agent6OneLFLongCycle.pH14896 (by decide +kernel)]
  exact BB6.Agent6OneLFLongCycle.cH14896
#print axioms cH14896
def pH15196 : PartialMachine := fromCodes [7, 23, 11, 1, 14, 4, 24, 16, 22, 11, 3, 8]
theorem cH15196 : Cover (WeightedBound 90794) pH15196 := by
  rw [tableOK_sound pH15196 BB6.Agent6OneLFLongCycle.pH15196 (by decide +kernel)]
  exact BB6.Agent6OneLFLongCycle.cH15196
#print axioms cH15196
def pH16306 : PartialMachine := fromCodes [7, 24, 11, 7, 14, 17, 0, 16, 22, 11, 7, 10]
theorem cH16306 : Cover (WeightedBound 90794) pH16306 := by
  rw [tableOK_sound pH16306 BB6.Agent6OneLFLongCycle.pH16306 (by decide +kernel)]
  exact BB6.Agent6OneLFLongCycle.cH16306
#print axioms cH16306
end BB6.Agent6OneLFExceptional
