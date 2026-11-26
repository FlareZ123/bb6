import ZipAuditCore
import Hybrid
open BB6Coverage BB6Coverage.FAR BB6Coverage.Agent10ZipAudit BB6.Agent13BlankDelay
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent4E0OneLC
def p12481 : PartialMachine := fromCodes [7, 12, 11, 7, 14, 9, 22, 16, 10, 11, 2, 24]
theorem check12481 : zipCycle p12481 2464 1056 true (26 : Int) = true := by decide +kernel
theorem never12481 (m : Machine) (hm : compatible p12481 m) : NeverHalts m :=
  zipCycle_sound p12481 2464 1056 true (26 : Int) (by decide) check12481 m hm
theorem cover12481 (B : Nat) : Cover (WeightedBound B) p12481 :=
  Cover.leaf p12481 (fun m hm => weighted_never B m (never12481 m hm))
#print axioms cover12481
def p12482 : PartialMachine := fromCodes [7, 16, 11, 7, 14, 9, 22, 16, 10, 11, 2, 24]
theorem check12482 : zipCycle p12482 480 422 true (-8 : Int) = true := by decide +kernel
theorem never12482 (m : Machine) (hm : compatible p12482 m) : NeverHalts m :=
  zipCycle_sound p12482 480 422 true (-8 : Int) (by decide) check12482 m hm
theorem cover12482 (B : Nat) : Cover (WeightedBound B) p12482 :=
  Cover.leaf p12482 (fun m hm => weighted_never B m (never12482 m hm))
#print axioms cover12482
def p12487 : PartialMachine := fromCodes [7, 14, 11, 7, 14, 9, 22, 16, 10, 11, 2, 24]
theorem check12487 : zipCycle p12487 476 420 true (-8 : Int) = true := by decide +kernel
theorem never12487 (m : Machine) (hm : compatible p12487 m) : NeverHalts m :=
  zipCycle_sound p12487 476 420 true (-8 : Int) (by decide) check12487 m hm
theorem cover12487 (B : Nat) : Cover (WeightedBound B) p12487 :=
  Cover.leaf p12487 (fun m hm => weighted_never B m (never12487 m hm))
#print axioms cover12487
def p12490 : PartialMachine := fromCodes [7, 15, 11, 7, 14, 9, 22, 16, 10, 11, 2, 24]
theorem check12490 : zipCycle p12490 488 426 true (-8 : Int) = true := by decide +kernel
theorem never12490 (m : Machine) (hm : compatible p12490 m) : NeverHalts m :=
  zipCycle_sound p12490 488 426 true (-8 : Int) (by decide) check12490 m hm
theorem cover12490 (B : Nat) : Cover (WeightedBound B) p12490 :=
  Cover.leaf p12490 (fun m hm => weighted_never B m (never12490 m hm))
#print axioms cover12490
def p13444 : PartialMachine := fromCodes [7, 1, 11, 21, 14, 13, 3, 16, 10, 11, 24, 17]
theorem check13444 : zipCycle p13444 3960 3037 true (2 : Int) = true := by decide +kernel
theorem never13444 (m : Machine) (hm : compatible p13444 m) : NeverHalts m :=
  zipCycle_sound p13444 3960 3037 true (2 : Int) (by decide) check13444 m hm
theorem cover13444 (B : Nat) : Cover (WeightedBound B) p13444 :=
  Cover.leaf p13444 (fun m hm => weighted_never B m (never13444 m hm))
#print axioms cover13444
def p13445 : PartialMachine := fromCodes [7, 1, 11, 21, 14, 17, 3, 16, 10, 11, 24, 17]
theorem check13445 : zipCycle p13445 3187 583 true (65 : Int) = true := by decide +kernel
theorem never13445 (m : Machine) (hm : compatible p13445 m) : NeverHalts m :=
  zipCycle_sound p13445 3187 583 true (65 : Int) (by decide) check13445 m hm
theorem cover13445 (B : Nat) : Cover (WeightedBound B) p13445 :=
  Cover.leaf p13445 (fun m hm => weighted_never B m (never13445 m hm))
#print axioms cover13445
def p13447 : PartialMachine := fromCodes [7, 1, 11, 21, 14, 6, 3, 16, 10, 11, 24, 17]
theorem check13447 : zipCycle p13447 3735 2079 true (29 : Int) = true := by decide +kernel
theorem never13447 (m : Machine) (hm : compatible p13447 m) : NeverHalts m :=
  zipCycle_sound p13447 3735 2079 true (29 : Int) (by decide) check13447 m hm
theorem cover13447 (B : Nat) : Cover (WeightedBound B) p13447 :=
  Cover.leaf p13447 (fun m hm => weighted_never B m (never13447 m hm))
#print axioms cover13447
def p18563 : PartialMachine := fromCodes [7, 14, 11, 24, 14, 8, 23, 16, 10, 11, 1, 13]
theorem check18563 : zipCycle p18563 210 366 false (10 : Int) = true := by decide +kernel
theorem never18563 (m : Machine) (hm : compatible p18563 m) : NeverHalts m :=
  zipCycle_sound p18563 210 366 false (10 : Int) (by decide) check18563 m hm
theorem cover18563 (B : Nat) : Cover (WeightedBound B) p18563 :=
  Cover.leaf p18563 (fun m hm => weighted_never B m (never18563 m hm))
#print axioms cover18563
def p18570 : PartialMachine := fromCodes [7, 13, 11, 24, 14, 8, 23, 16, 10, 11, 3, 13]
theorem check18570 : zipCycle p18570 874 346 false (-6 : Int) = true := by decide +kernel
theorem never18570 (m : Machine) (hm : compatible p18570 m) : NeverHalts m :=
  zipCycle_sound p18570 874 346 false (-6 : Int) (by decide) check18570 m hm
theorem cover18570 (B : Nat) : Cover (WeightedBound B) p18570 :=
  Cover.leaf p18570 (fun m hm => weighted_never B m (never18570 m hm))
#print axioms cover18570
end BB6.Agent4E0OneLC
