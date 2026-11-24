import DepthEightFAR

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent7FAR.DepthEightBatch
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent7FAR.DepthEight

/-- tree114 path [[8,6],[10,9]]; 1RB---_1RC1LF_0RD0RC_1LD1RE_1LB0LB_0RC0LA. -/
def p0 : PartialMachine := fromCodes [7,24,11,22,13,9,14,19,6,4,9,0]
def c0 : Data 1 := ⟨0,[0,0],[1,32,8,8,2,8,64],[64,32,8,32,2,1,64],64⟩
theorem p0_valid : c0.fastValid (reflectPartial p0) = true := by decide
theorem p0_root : p0 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p0_never (m : Machine) (hm : compatible p0 m) : NeverHalts m :=
  reflectNever m (c0.sound (reflectPartial p0) (c0.fastValid_sound _ p0_valid) (reflectTable m) (reflectCompatible p0 m hm))
def leaf0 (B : Nat) : WeightedTNFCertificate B p0 6 :=
  WeightedTNFCertificate.nonhalt p0_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p0_never m hm)
#print axioms p0_never
#print axioms leaf0

/-- tree114 path [[8,8],[10,9]]; 1RB---_1RC1LF_0RD0RC_1LD1RE_0LC0LB_0RC0LA. -/
def p1 : PartialMachine := fromCodes [7,24,11,22,13,9,14,19,8,4,9,0]
def c1 : Data 1 := ⟨0,[0,0],[41,40,8,8,4,8,64],[64,32,8,40,2,1,64],64⟩
theorem p1_valid : c1.fastValid (reflectPartial p1) = true := by decide
theorem p1_root : p1 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p1_never (m : Machine) (hm : compatible p1 m) : NeverHalts m :=
  reflectNever m (c1.sound (reflectPartial p1) (c1.fastValid_sound _ p1_valid) (reflectTable m) (reflectCompatible p1 m hm))
def leaf1 (B : Nat) : WeightedTNFCertificate B p1 6 :=
  WeightedTNFCertificate.nonhalt p1_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p1_never m hm)
#print axioms p1_never
#print axioms leaf1

/-- tree114 path [[8,8],[10,13]]; 1RB---_1RC1LF_0RD0RC_1LD1RE_0LC0LB_0RD0LA. -/
def p2 : PartialMachine := fromCodes [7,24,11,22,13,9,14,19,8,4,13,0]
def c2 : Data 1 := ⟨0,[0,0],[41,40,8,8,4,8,64],[64,32,8,40,2,1,64],64⟩
theorem p2_valid : c2.fastValid (reflectPartial p2) = true := by decide
theorem p2_root : p2 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p2_never (m : Machine) (hm : compatible p2 m) : NeverHalts m :=
  reflectNever m (c2.sound (reflectPartial p2) (c2.fastValid_sound _ p2_valid) (reflectTable m) (reflectCompatible p2 m hm))
def leaf2 (B : Nat) : WeightedTNFCertificate B p2 6 :=
  WeightedTNFCertificate.nonhalt p2_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p2_never m hm)
#print axioms p2_never
#print axioms leaf2

/-- tree114 path [[8,9],[10,9]]; 1RB---_1RC1LF_0RD0RC_1LD1RE_0RC0LB_0RC0LA. -/
def p3 : PartialMachine := fromCodes [7,24,11,22,13,9,14,19,9,4,9,0]
def c3 : Data 1 := ⟨0,[0,0],[1,32,8,8,8,8,64],[64,32,8,32,2,1,64],64⟩
theorem p3_valid : c3.fastValid (reflectPartial p3) = true := by decide
theorem p3_root : p3 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p3_never (m : Machine) (hm : compatible p3 m) : NeverHalts m :=
  reflectNever m (c3.sound (reflectPartial p3) (c3.fastValid_sound _ p3_valid) (reflectTable m) (reflectCompatible p3 m hm))
def leaf3 (B : Nat) : WeightedTNFCertificate B p3 6 :=
  WeightedTNFCertificate.nonhalt p3_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p3_never m hm)
#print axioms p3_never
#print axioms leaf3

/-- tree114 path [[8,9],[10,13]]; 1RB---_1RC1LF_0RD0RC_1LD1RE_0RC0LB_0RD0LA. -/
def p4 : PartialMachine := fromCodes [7,24,11,22,13,9,14,19,9,4,13,0]
def c4 : Data 1 := ⟨0,[0,0],[1,32,8,8,8,8,64],[64,32,8,32,2,1,64],64⟩
theorem p4_valid : c4.fastValid (reflectPartial p4) = true := by decide
theorem p4_root : p4 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p4_never (m : Machine) (hm : compatible p4 m) : NeverHalts m :=
  reflectNever m (c4.sound (reflectPartial p4) (c4.fastValid_sound _ p4_valid) (reflectTable m) (reflectCompatible p4 m hm))
def leaf4 (B : Nat) : WeightedTNFCertificate B p4 6 :=
  WeightedTNFCertificate.nonhalt p4_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p4_never m hm)
#print axioms p4_never
#print axioms leaf4

/-- tree114 path [[8,9],[10,16]]; 1RB---_1RC1LF_0RD0RC_1LD1RE_0RC0LB_0LE0LA. -/
def p5 : PartialMachine := fromCodes [7,24,11,22,13,9,14,19,9,4,16,0]
def c5 : Data 1 := ⟨0,[0,0],[33,34,24,8,8,16,64],[64,32,8,32,2,1,64],64⟩
theorem p5_valid : c5.fastValid (reflectPartial p5) = true := by decide
theorem p5_root : p5 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p5_never (m : Machine) (hm : compatible p5 m) : NeverHalts m :=
  reflectNever m (c5.sound (reflectPartial p5) (c5.fastValid_sound _ p5_valid) (reflectTable m) (reflectCompatible p5 m hm))
def leaf5 (B : Nat) : WeightedTNFCertificate B p5 6 :=
  WeightedTNFCertificate.nonhalt p5_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p5_never m hm)
#print axioms p5_never
#print axioms leaf5

/-- tree114 path [[8,9],[10,18]]; 1RB---_1RC1LF_0RD0RC_1LD1RE_0RC0LB_1LE0LA. -/
def p6 : PartialMachine := fromCodes [7,24,11,22,13,9,14,19,9,4,18,0]
def c6 : Data 1 := ⟨0,[0,0],[33,34,24,8,8,16,64],[64,32,8,32,2,1,64],64⟩
theorem p6_valid : c6.fastValid (reflectPartial p6) = true := by decide
theorem p6_root : p6 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p6_never (m : Machine) (hm : compatible p6 m) : NeverHalts m :=
  reflectNever m (c6.sound (reflectPartial p6) (c6.fastValid_sound _ p6_valid) (reflectTable m) (reflectCompatible p6 m hm))
def leaf6 (B : Nat) : WeightedTNFCertificate B p6 6 :=
  WeightedTNFCertificate.nonhalt p6_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p6_never m hm)
#print axioms p6_never
#print axioms leaf6

/-- tree114 path [[8,10],[10,9]]; 1RB---_1RC1LF_0RD0RC_1LD1RE_1LC0LB_0RC0LA. -/
def p7 : PartialMachine := fromCodes [7,24,11,22,13,9,14,19,10,4,9,0]
def c7 : Data 1 := ⟨0,[0,0],[41,40,8,8,4,8,64],[64,32,8,40,2,1,64],64⟩
theorem p7_valid : c7.fastValid (reflectPartial p7) = true := by decide
theorem p7_root : p7 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p7_never (m : Machine) (hm : compatible p7 m) : NeverHalts m :=
  reflectNever m (c7.sound (reflectPartial p7) (c7.fastValid_sound _ p7_valid) (reflectTable m) (reflectCompatible p7 m hm))
def leaf7 (B : Nat) : WeightedTNFCertificate B p7 6 :=
  WeightedTNFCertificate.nonhalt p7_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p7_never m hm)
#print axioms p7_never
#print axioms leaf7

/-- tree114 path [[8,10],[10,13]]; 1RB---_1RC1LF_0RD0RC_1LD1RE_1LC0LB_0RD0LA. -/
def p8 : PartialMachine := fromCodes [7,24,11,22,13,9,14,19,10,4,13,0]
def c8 : Data 1 := ⟨0,[0,0],[41,40,8,8,4,8,64],[64,32,8,40,2,1,64],64⟩
theorem p8_valid : c8.fastValid (reflectPartial p8) = true := by decide
theorem p8_root : p8 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p8_never (m : Machine) (hm : compatible p8 m) : NeverHalts m :=
  reflectNever m (c8.sound (reflectPartial p8) (c8.fastValid_sound _ p8_valid) (reflectTable m) (reflectCompatible p8 m hm))
def leaf8 (B : Nat) : WeightedTNFCertificate B p8 6 :=
  WeightedTNFCertificate.nonhalt p8_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p8_never m hm)
#print axioms p8_never
#print axioms leaf8

/-- tree114 path [[8,14],[10,9]]; 1RB---_1RC1LF_0RD0RC_1LD1RE_1LD0LB_0RC0LA. -/
def p9 : PartialMachine := fromCodes [7,24,11,22,13,9,14,19,14,4,9,0]
def c9 : Data 1 := ⟨0,[0,0],[1,32,8,8,8,8,64],[64,32,8,32,2,1,64],64⟩
theorem p9_valid : c9.fastValid (reflectPartial p9) = true := by decide
theorem p9_root : p9 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p9_never (m : Machine) (hm : compatible p9 m) : NeverHalts m :=
  reflectNever m (c9.sound (reflectPartial p9) (c9.fastValid_sound _ p9_valid) (reflectTable m) (reflectCompatible p9 m hm))
def leaf9 (B : Nat) : WeightedTNFCertificate B p9 6 :=
  WeightedTNFCertificate.nonhalt p9_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p9_never m hm)
#print axioms p9_never
#print axioms leaf9

/-- tree115 path [[10,4],[8,13]]; 1RB---_1RC1LF_0RD1LC_1LD1RE_0RD0LB_0LB0LA. -/
def p10 : PartialMachine := fromCodes [7,24,11,22,13,10,14,19,13,4,4,0]
def c10 : Data 1 := ⟨0,[0,0],[5,36,10,8,10,2,64],[64,32,4,32,2,1,64],64⟩
theorem p10_valid : c10.fastValid (reflectPartial p10) = true := by decide
theorem p10_root : p10 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p10_never (m : Machine) (hm : compatible p10 m) : NeverHalts m :=
  reflectNever m (c10.sound (reflectPartial p10) (c10.fastValid_sound _ p10_valid) (reflectTable m) (reflectCompatible p10 m hm))
def leaf10 (B : Nat) : WeightedTNFCertificate B p10 6 :=
  WeightedTNFCertificate.nonhalt p10_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p10_never m hm)
#print axioms p10_never
#print axioms leaf10

/-- tree117 path [[8,5],[10,4]]; 1RB---_1RC1LF_0RD0LD_1LD1RE_0RB0LB_0LB0LA. -/
def p11 : PartialMachine := fromCodes [7,24,11,22,13,12,14,19,5,4,4,0]
def c11 : Data 1 := ⟨0,[0,0],[1,32,10,8,2,2,64],[64,32,8,32,2,1,64],64⟩
theorem p11_valid : c11.fastValid (reflectPartial p11) = true := by decide
theorem p11_root : p11 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p11_never (m : Machine) (hm : compatible p11 m) : NeverHalts m :=
  reflectNever m (c11.sound (reflectPartial p11) (c11.fastValid_sound _ p11_valid) (reflectTable m) (reflectCompatible p11 m hm))
def leaf11 (B : Nat) : WeightedTNFCertificate B p11 6 :=
  WeightedTNFCertificate.nonhalt p11_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p11_never m hm)
#print axioms p11_never
#print axioms leaf11

/-- tree117 path [[8,5],[10,14]]; 1RB---_1RC1LF_0RD0LD_1LD1RE_0RB0LB_1LD0LA. -/
def p12 : PartialMachine := fromCodes [7,24,11,22,13,12,14,19,5,4,14,0]
def c12 : Data 1 := ⟨0,[0,0],[1,32,8,8,8,8,64],[64,32,8,32,2,1,64],64⟩
theorem p12_valid : c12.fastValid (reflectPartial p12) = true := by decide
theorem p12_root : p12 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p12_never (m : Machine) (hm : compatible p12 m) : NeverHalts m :=
  reflectNever m (c12.sound (reflectPartial p12) (c12.fastValid_sound _ p12_valid) (reflectTable m) (reflectCompatible p12 m hm))
def leaf12 (B : Nat) : WeightedTNFCertificate B p12 6 :=
  WeightedTNFCertificate.nonhalt p12_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p12_never m hm)
#print axioms p12_never
#print axioms leaf12

/-- tree117 path [[8,9],[10,9]]; 1RB---_1RC1LF_0RD0LD_1LD1RE_0RC0LB_0RC0LA. -/
def p13 : PartialMachine := fromCodes [7,24,11,22,13,12,14,19,9,4,9,0]
def c13 : Data 1 := ⟨0,[0,0],[1,32,8,8,8,8,64],[64,32,8,32,2,1,64],64⟩
theorem p13_valid : c13.fastValid (reflectPartial p13) = true := by decide
theorem p13_root : p13 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p13_never (m : Machine) (hm : compatible p13 m) : NeverHalts m :=
  reflectNever m (c13.sound (reflectPartial p13) (c13.fastValid_sound _ p13_valid) (reflectTable m) (reflectCompatible p13 m hm))
def leaf13 (B : Nat) : WeightedTNFCertificate B p13 6 :=
  WeightedTNFCertificate.nonhalt p13_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p13_never m hm)
#print axioms p13_never
#print axioms leaf13

/-- tree121 path [[10,4],[8,13]]; 1RB---_1RC1LF_0RD0LE_1LD1RE_0RD0LB_0LB0LA. -/
def p14 : PartialMachine := fromCodes [7,24,11,22,13,16,14,19,13,4,4,0]
def c14 : Data 1 := ⟨0,[0,0],[33,34,10,8,10,2,64],[64,32,16,32,2,1,64],64⟩
theorem p14_valid : c14.fastValid (reflectPartial p14) = true := by decide
theorem p14_root : p14 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p14_never (m : Machine) (hm : compatible p14 m) : NeverHalts m :=
  reflectNever m (c14.sound (reflectPartial p14) (c14.fastValid_sound _ p14_valid) (reflectTable m) (reflectCompatible p14 m hm))
def leaf14 (B : Nat) : WeightedTNFCertificate B p14 6 :=
  WeightedTNFCertificate.nonhalt p14_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p14_never m hm)
#print axioms p14_never
#print axioms leaf14

/-- tree123 path [[10,4],[8,13]]; 1RB---_1RC1LF_0RD1LE_1LD1RE_0RD0LB_0LB0LA. -/
def p15 : PartialMachine := fromCodes [7,24,11,22,13,18,14,19,13,4,4,0]
def c15 : Data 1 := ⟨0,[0,0],[33,34,10,8,10,2,64],[64,32,16,32,2,1,64],64⟩
theorem p15_valid : c15.fastValid (reflectPartial p15) = true := by decide
theorem p15_root : p15 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p15_never (m : Machine) (hm : compatible p15 m) : NeverHalts m :=
  reflectNever m (c15.sound (reflectPartial p15) (c15.fastValid_sound _ p15_valid) (reflectTable m) (reflectCompatible p15 m hm))
def leaf15 (B : Nat) : WeightedTNFCertificate B p15 6 :=
  WeightedTNFCertificate.nonhalt p15_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p15_never m hm)
#print axioms p15_never
#print axioms leaf15

/-- tree112 path [[1,23],[10,14]]; 1RB1RF_1RC1LF_0RD1RB_1LD1RE_---0LB_1LD0LA. -/
def p16 : PartialMachine := fromCodes [7,23,11,22,13,7,14,19,24,4,14,0]
def c16 : Data 2 := ⟨0,[0,1,0,1],[128,256,8,128,4096,128,128,256,8,256,4096,256,4096],[2048,128,128,1024,8,256,2048,128,128,1024,256,256,4096],5136⟩
theorem p16_valid : c16.fastValid p16 = true := by decide
theorem p16_root : p16 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p16_never (m : Machine) (hm : compatible p16 m) : NeverHalts m :=
  c16.sound p16 (c16.fastValid_sound _ p16_valid) m hm
def leaf16 (B : Nat) : WeightedTNFCertificate B p16 6 :=
  WeightedTNFCertificate.nonhalt p16_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p16_never m hm)
#print axioms p16_never
#print axioms leaf16

/-- tree123 path [[10,11],[8,13]]; 1RB---_1RC1LF_0RD1LE_1LD1RE_0RD0LB_1RC0LA. -/
def p17 : PartialMachine := fromCodes [7,24,11,22,13,18,14,19,13,4,11,0]
def c17 : Data 2 := ⟨0,[0,1,0,0],[2049,2050,522,512,522,2050,1,2,2,8,2,2,4096],[4096,2048,1024,2048,2,1,4096,32,16,2048,2,1,4096],4096⟩
theorem p17_valid : c17.fastValid (reflectPartial p17) = true := by decide
theorem p17_root : p17 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p17_never (m : Machine) (hm : compatible p17 m) : NeverHalts m :=
  reflectNever m (c17.sound (reflectPartial p17) (c17.fastValid_sound _ p17_valid) (reflectTable m) (reflectCompatible p17 m hm))
def leaf17 (B : Nat) : WeightedTNFCertificate B p17 6 :=
  WeightedTNFCertificate.nonhalt p17_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p17_never m hm)
#print axioms p17_never
#print axioms leaf17

/-- tree126 path [[10,0],[1,15]]; 1RB1RD_1RC1LF_0RD0RF_1LD1RE_---0LB_0LA0LA. -/
def p18 : PartialMachine := fromCodes [7,15,11,22,13,21,14,19,24,4,0,0]
def c18 : Data 2 := ⟨0,[0,1,0,1],[128,256,8,288,4096,256,128,256,8,256,4096,256,4096],[512,32,32,1024,8,256,512,32,32,1024,256,256,4096],5136⟩
theorem p18_valid : c18.fastValid p18 = true := by decide
theorem p18_root : p18 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p18_never (m : Machine) (hm : compatible p18 m) : NeverHalts m :=
  c18.sound p18 (c18.fastValid_sound _ p18_valid) m hm
def leaf18 (B : Nat) : WeightedTNFCertificate B p18 6 :=
  WeightedTNFCertificate.nonhalt p18_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p18_never m hm)
#print axioms p18_never
#print axioms leaf18

/-- tree126 path [[10,0],[1,22]]; 1RB1LF_1RC1LF_0RD0RF_1LD1RE_---0LB_0LA0LA. -/
def p19 : PartialMachine := fromCodes [7,22,11,22,13,21,14,19,24,4,0,0]
def c19 : Data 2 := ⟨0,[0,1,0,1],[128,256,8,288,4096,256,128,256,8,256,4096,256,4096],[32,32,32,1024,8,256,32,32,32,1024,256,256,4096],5136⟩
theorem p19_valid : c19.fastValid p19 = true := by decide
theorem p19_root : p19 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p19_never (m : Machine) (hm : compatible p19 m) : NeverHalts m :=
  c19.sound p19 (c19.fastValid_sound _ p19_valid) m hm
def leaf19 (B : Nat) : WeightedTNFCertificate B p19 6 :=
  WeightedTNFCertificate.nonhalt p19_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p19_never m hm)
#print axioms p19_never
#print axioms leaf19

/-- tree126 path [[10,3],[1,22]]; 1RB1LF_1RC1LF_0RD0RF_1LD1RE_---0LB_1RA0LA. -/
def p20 : PartialMachine := fromCodes [7,22,11,22,13,21,14,19,24,4,3,0]
def c20 : Data 2 := ⟨0,[0,1,0,1],[128,256,8,288,4096,64,128,256,8,64,4096,64,4096],[32,32,32,1024,8,256,32,32,32,1024,64,64,4096],5136⟩
theorem p20_valid : c20.fastValid p20 = true := by decide
theorem p20_root : p20 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p20_never (m : Machine) (hm : compatible p20 m) : NeverHalts m :=
  c20.sound p20 (c20.fastValid_sound _ p20_valid) m hm
def leaf20 (B : Nat) : WeightedTNFCertificate B p20 6 :=
  WeightedTNFCertificate.nonhalt p20_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p20_never m hm)
#print axioms p20_never
#print axioms leaf20

/-- tree128 path [[10,9],[1,21]]; 1RB0RF_1RC1LF_0RD1RF_1LD1RE_---0LB_0RC0LA. -/
def p21 : PartialMachine := fromCodes [7,21,11,22,13,23,14,19,24,4,9,0]
def c21 : Data 2 := ⟨0,[0,1,0,1],[128,256,8,2052,4096,4,128,256,8,4,4096,4,4096],[32,2048,2048,1024,8,256,32,2048,2048,1024,4,4,4096],5136⟩
theorem p21_valid : c21.fastValid p21 = true := by decide
theorem p21_root : p21 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p21_never (m : Machine) (hm : compatible p21 m) : NeverHalts m :=
  c21.sound p21 (c21.fastValid_sound _ p21_valid) m hm
def leaf21 (B : Nat) : WeightedTNFCertificate B p21 6 :=
  WeightedTNFCertificate.nonhalt p21_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p21_never m hm)
#print axioms p21_never
#print axioms leaf21

/-- tree128 path [[10,11],[1,15]]; 1RB1RD_1RC1LF_0RD1RF_1LD1RE_---0LB_1RC0LA. -/
def p22 : PartialMachine := fromCodes [7,15,11,22,13,23,14,19,24,4,11,0]
def c22 : Data 2 := ⟨0,[0,1,0,1],[128,256,8,2304,4096,256,128,256,8,256,4096,256,4096],[512,2048,2048,1024,8,256,512,2048,2048,1024,256,256,4096],5136⟩
theorem p22_valid : c22.fastValid p22 = true := by decide
theorem p22_root : p22 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p22_never (m : Machine) (hm : compatible p22 m) : NeverHalts m :=
  c22.sound p22 (c22.fastValid_sound _ p22_valid) m hm
def leaf22 (B : Nat) : WeightedTNFCertificate B p22 6 :=
  WeightedTNFCertificate.nonhalt p22_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p22_never m hm)
#print axioms p22_never
#print axioms leaf22

/-- tree128 path [[10,11],[1,22]]; 1RB1LF_1RC1LF_0RD1RF_1LD1RE_---0LB_1RC0LA. -/
def p23 : PartialMachine := fromCodes [7,22,11,22,13,23,14,19,24,4,11,0]
def c23 : Data 2 := ⟨0,[0,1,0,1],[128,256,8,2304,4096,256,128,256,8,256,4096,256,4096],[2048,2048,2048,1024,8,256,2048,2048,2048,1024,256,256,4096],5136⟩
theorem p23_valid : c23.fastValid p23 = true := by decide
theorem p23_root : p23 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p23_never (m : Machine) (hm : compatible p23 m) : NeverHalts m :=
  c23.sound p23 (c23.fastValid_sound _ p23_valid) m hm
def leaf23 (B : Nat) : WeightedTNFCertificate B p23 6 :=
  WeightedTNFCertificate.nonhalt p23_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p23_never m hm)
#print axioms p23_never
#print axioms leaf23

/-- tree115 path [[10,4],[8,9]]; 1RB---_1RC1LF_0RD1LC_1LD1RE_0RC0LB_0LB0LA. -/
def p24 : PartialMachine := fromCodes [7,24,11,22,13,10,14,19,9,4,4,0]
def c24 : Data 3 := ⟨0,[0,1,2,1,0,1],[4352,2048,512,512,512,2,4096,256,8448,512,8448,8192,256,2304,512,512,10496,2,262144],[262144,2048,256,6400,2,1,262144,2048,256,2048,8192,4096,262144,2048,256,2304,2,1,262144],262144⟩
theorem p24_valid : c24.fastValid (reflectPartial p24) = true := by decide
theorem p24_root : p24 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p24_never (m : Machine) (hm : compatible p24 m) : NeverHalts m :=
  reflectNever m (c24.sound (reflectPartial p24) (c24.fastValid_sound _ p24_valid) (reflectTable m) (reflectCompatible p24 m hm))
def leaf24 (B : Nat) : WeightedTNFCertificate B p24 6 :=
  WeightedTNFCertificate.nonhalt p24_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p24_never m hm)
#print axioms p24_never
#print axioms leaf24

/-- tree123 path [[10,1],[1,23]]; 1RB1RF_1RC1LF_0RD1LE_1LD1RE_---0LB_0RA0LA. -/
def p25 : PartialMachine := fromCodes [7,23,11,22,13,18,14,19,24,4,1,0]
def c25 : Data 3 := ⟨0,[0,1,0,2,0,2],[128,256,8,2049,262144,1,8192,16384,8,1,262144,1,8192,16384,8,1,262144,1,262144],[2048,2048,262144,1024,8,16384,131072,2048,1024,65536,1,1,131072,2048,2048,65536,1,1,262144],328720⟩
theorem p25_valid : c25.fastValid p25 = true := by decide
theorem p25_root : p25 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p25_never (m : Machine) (hm : compatible p25 m) : NeverHalts m :=
  c25.sound p25 (c25.fastValid_sound _ p25_valid) m hm
def leaf25 (B : Nat) : WeightedTNFCertificate B p25 6 :=
  WeightedTNFCertificate.nonhalt p25_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p25_never m hm)
#print axioms p25_never
#print axioms leaf25

/-- tree126 path [[10,3],[1,8]]; 1RB0LC_1RC1LF_0RD0RF_1LD1RE_---0LB_1RA0LA. -/
def p26 : PartialMachine := fromCodes [7,8,11,22,13,21,14,19,24,4,3,0]
def c26 : Data 3 := ⟨0,[0,1,0,2,0,1],[128,256,8,64,262144,64,8192,16384,8,8192,262144,4096,128,256,8,64,262144,64,262144],[64,64,32,1024,8,16640,64,32,32,65536,8192,8192,64,0,32,1024,64,8192,262144],328720⟩
theorem p26_valid : c26.fastValid p26 = true := by decide
theorem p26_root : p26 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p26_never (m : Machine) (hm : compatible p26 m) : NeverHalts m :=
  c26.sound p26 (c26.fastValid_sound _ p26_valid) m hm
def leaf26 (B : Nat) : WeightedTNFCertificate B p26 6 :=
  WeightedTNFCertificate.nonhalt p26_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p26_never m hm)
#print axioms p26_never
#print axioms leaf26

/-- tree126 path [[10,3],[1,15]]; 1RB1RD_1RC1LF_0RD0RF_1LD1RE_---0LB_1RA0LA. -/
def p27 : PartialMachine := fromCodes [7,15,11,22,13,21,14,19,24,4,3,0]
def c27 : Data 3 := ⟨0,[0,1,2,1,0,1],[128,256,8,1600,262144,64,128,256,32768,64,262144,64,128,256,8,512,262144,64,262144],[512,512,32,1024,32768,256,512,131584,131072,1024,64,64,512,512,32,1024,32768,256,262144],345116⟩
theorem p27_valid : c27.fastValid p27 = true := by decide
theorem p27_root : p27 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p27_never (m : Machine) (hm : compatible p27 m) : NeverHalts m :=
  c27.sound p27 (c27.fastValid_sound _ p27_valid) m hm
def leaf27 (B : Nat) : WeightedTNFCertificate B p27 6 :=
  WeightedTNFCertificate.nonhalt p27_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p27_never m hm)
#print axioms p27_never
#print axioms leaf27

/-- tree86 path [[1,21],[10,12]]; 1RB0RF_1RC1LF_0RD1RA_1LD1RE_---0LB_0LD0LA. -/
def p28 : PartialMachine := fromCodes [7,21,11,22,13,3,14,19,24,4,12,0]
def c28 : Data 4 := ⟨0,[0,1,2,1,3,3,3,3],[128,256,8,0,16777216,0,128,256,32768,128,16777216,16777216,524288,1048576,2097152,64,16777216,256,524288,1048576,2097152,33456576,16777216,33456576,16777216],[32,0,64,1024,32768,256,131072,64,64,1024,128,256,8388608,16777216,262144,4194304,32768,256,8388608,33456576,262144,4194304,33456576,33456576,16777216],33389584⟩
theorem p28_valid : c28.fastValid p28 = true := by decide
theorem p28_root : p28 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p28_never (m : Machine) (hm : compatible p28 m) : NeverHalts m :=
  c28.sound p28 (c28.fastValid_sound _ p28_valid) m hm
def leaf28 (B : Nat) : WeightedTNFCertificate B p28 6 :=
  WeightedTNFCertificate.nonhalt p28_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p28_never m hm)
#print axioms p28_never
#print axioms leaf28

/-- tree112 path [[1,12],[8,10]]; 1RB0LD_1RC1LF_0RD1RB_1LD1RE_1LC0LB_---0LA. -/
def p29 : PartialMachine := fromCodes [7,12,11,22,13,7,14,19,10,4,24,0]
def c29 : Data 4 := ⟨0,[0,1,2,3,2,2,0,1],[128,256,8,128,1024,16777216,524288,1048576,32768,17825920,128,16777216,8192,16384,32768,18474376,18474376,16777216,128,256,8,1048576,1152,16777216,16777216],[1048584,16777216,128,1024,32768,1048576,128,128,524288,4194304,17825920,1048712,18474376,18474376,8192,65536,18474376,18474376,1152,1152,128,1024,1048576,1048576,16777216],25951074⟩
theorem p29_valid : c29.fastValid p29 = true := by decide
theorem p29_root : p29 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p29_never (m : Machine) (hm : compatible p29 m) : NeverHalts m :=
  c29.sound p29 (c29.fastValid_sound _ p29_valid) m hm
def leaf29 (B : Nat) : WeightedTNFCertificate B p29 6 :=
  WeightedTNFCertificate.nonhalt p29_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p29_never m hm)
#print axioms p29_never
#print axioms leaf29

/-- tree112 path [[1,12],[8,15]]; 1RB0LD_1RC1LF_0RD1RB_1LD1RE_1RD0LB_---0LA. -/
def p30 : PartialMachine := fromCodes [7,12,11,22,13,7,14,19,15,4,24,0]
def c30 : Data 4 := ⟨0,[0,1,2,3,2,2,0,1],[128,256,8,128,512,16777216,524288,1048576,32768,19922944,2097152,16777216,8192,16384,32768,20571528,32768,16777216,128,256,8,1048576,512,16777216,16777216],[1048584,16777216,128,1024,32768,1048576,2097152,128,524288,4194304,19922944,19923080,20571528,20571528,8192,65536,20571528,20571528,512,16778368,128,1024,1048576,1048576,16777216],30145394⟩
theorem p30_valid : c30.fastValid p30 = true := by decide
theorem p30_root : p30 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p30_never (m : Machine) (hm : compatible p30 m) : NeverHalts m :=
  c30.sound p30 (c30.fastValid_sound _ p30_valid) m hm
def leaf30 (B : Nat) : WeightedTNFCertificate B p30 6 :=
  WeightedTNFCertificate.nonhalt p30_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p30_never m hm)
#print axioms p30_never
#print axioms leaf30

/-- tree112 path [[1,12],[8,22]]; 1RB0LD_1RC1LF_0RD1RB_1LD1RE_1LF0LB_---0LA. -/
def p31 : PartialMachine := fromCodes [7,12,11,22,13,7,14,19,22,4,24,0]
def c31 : Data 4 := ⟨0,[0,1,2,3,2,2,0,1],[128,256,8,128,16777216,16777216,524288,1048576,32768,17825920,128,16777216,8192,16384,32768,18474376,18474376,16777216,128,256,8,1048576,1152,16777216,16777216],[1048584,16777216,128,1024,32768,1048576,128,128,524288,4194304,17825920,1048712,18474376,18474376,8192,65536,18474376,18474376,1152,1152,128,1024,1048576,1048576,16777216],25951090⟩
theorem p31_valid : c31.fastValid p31 = true := by decide
theorem p31_root : p31 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p31_never (m : Machine) (hm : compatible p31 m) : NeverHalts m :=
  c31.sound p31 (c31.fastValid_sound _ p31_valid) m hm
def leaf31 (B : Nat) : WeightedTNFCertificate B p31 6 :=
  WeightedTNFCertificate.nonhalt p31_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p31_never m hm)
#print axioms p31_never
#print axioms leaf31

/-- tree112 path [[1,19],[8,2]]; 1RB1RE_1RC1LF_0RD1RB_1LD1RE_1LA0LB_---0LA. -/
def p32 : PartialMachine := fromCodes [7,19,11,22,13,7,14,19,2,4,24,0]
def c32 : Data 4 := ⟨0,[0,1,2,3,2,2,0,1],[128,256,8,128,128,16777216,524288,1048576,32768,16777216,16777216,16777216,8192,16384,32768,18474376,18474376,16777216,128,256,8,1048576,1048576,16777216,16777216],[1024,16777216,128,1024,32768,1048576,4194304,128,524288,4194304,16777216,16777216,65536,18474376,8192,65536,18474376,18474376,1024,16777216,128,1024,1048576,1048576,16777216],25952098⟩
theorem p32_valid : c32.fastValid p32 = true := by decide
theorem p32_root : p32 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p32_never (m : Machine) (hm : compatible p32 m) : NeverHalts m :=
  c32.sound p32 (c32.fastValid_sound _ p32_valid) m hm
def leaf32 (B : Nat) : WeightedTNFCertificate B p32 6 :=
  WeightedTNFCertificate.nonhalt p32_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p32_never m hm)
#print axioms p32_never
#print axioms leaf32

/-- tree112 path [[1,19],[8,4]]; 1RB1RE_1RC1LF_0RD1RB_1LD1RE_0LB0LB_---0LA. -/
def p33 : PartialMachine := fromCodes [7,19,11,22,13,7,14,19,4,4,24,0]
def c33 : Data 4 := ⟨0,[0,1,2,3,2,2,0,1],[128,256,8,128,32768,16777216,524288,1048576,32768,16777216,16777216,16777216,8192,16384,32768,17425672,16826632,16777216,128,256,8,1048576,1048576,16777216,16777216],[1024,16777216,128,1024,32768,1048576,4194304,128,524288,4194304,16777216,16777216,65536,17376256,8192,65536,16826632,16826632,1024,16777216,128,1024,1048576,1048576,16777216],25952114⟩
theorem p33_valid : c33.fastValid p33 = true := by decide
theorem p33_root : p33 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p33_never (m : Machine) (hm : compatible p33 m) : NeverHalts m :=
  c33.sound p33 (c33.fastValid_sound _ p33_valid) m hm
def leaf33 (B : Nat) : WeightedTNFCertificate B p33 6 :=
  WeightedTNFCertificate.nonhalt p33_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p33_never m hm)
#print axioms p33_never
#print axioms leaf33

/-- tree112 path [[1,19],[8,14]]; 1RB1RE_1RC1LF_0RD1RB_1LD1RE_1LD0LB_---0LA. -/
def p34 : PartialMachine := fromCodes [7,19,11,22,13,7,14,19,14,4,24,0]
def c34 : Data 4 := ⟨0,[0,1,2,3,2,2,0,1],[128,256,8,128,128,16777216,524288,1048576,32768,16777216,16777216,16777216,8192,16384,32768,18474376,18474376,16777216,128,256,8,1048576,1048576,16777216,16777216],[1024,16777216,128,1024,32768,1048576,4194304,128,524288,4194304,16777216,16777216,65536,18474376,8192,65536,18474376,18474376,1024,16777216,128,1024,1048576,1048576,16777216],25952098⟩
theorem p34_valid : c34.fastValid p34 = true := by decide
theorem p34_root : p34 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p34_never (m : Machine) (hm : compatible p34 m) : NeverHalts m :=
  c34.sound p34 (c34.fastValid_sound _ p34_valid) m hm
def leaf34 (B : Nat) : WeightedTNFCertificate B p34 6 :=
  WeightedTNFCertificate.nonhalt p34_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p34_never m hm)
#print axioms p34_never
#print axioms leaf34

/-- tree112 path [[1,23],[10,4]]; 1RB1RF_1RC1LF_0RD1RB_1LD1RE_---0LB_0LB0LA. -/
def p35 : PartialMachine := fromCodes [7,23,11,22,13,7,14,19,24,4,4,0]
def c35 : Data 4 := ⟨0,[0,1,2,3,2,2,0,1],[128,256,8,128,16777216,32768,524288,1048576,32768,17825792,16777216,17825792,8192,16384,32768,18474376,16777216,17875208,128,256,8,1048576,16777216,1048576,16777216],[2048,65664,128,1024,32768,1048576,8388608,128,524288,4194304,17825792,17825792,131072,17376384,8192,65536,17875208,17875208,2048,16777344,128,1024,1048576,1048576,16777216],21757810⟩
theorem p35_valid : c35.fastValid p35 = true := by decide
theorem p35_root : p35 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p35_never (m : Machine) (hm : compatible p35 m) : NeverHalts m :=
  c35.sound p35 (c35.fastValid_sound _ p35_valid) m hm
def leaf35 (B : Nat) : WeightedTNFCertificate B p35 6 :=
  WeightedTNFCertificate.nonhalt p35_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p35_never m hm)
#print axioms p35_never
#print axioms leaf35

/-- tree116 path [[8,22],[1,19]]; 1RB1RE_1RC1LF_0RD1RC_1LD1RE_1LF0LB_---0LA. -/
def p36 : PartialMachine := fromCodes [7,19,11,22,13,11,14,19,22,4,24,0]
def c36 : Data 4 := ⟨0,[0,1,0,2,3,2,0,1],[128,256,8,16777216,16777216,16777216,8192,16384,8,16777216,16384,16777216,8192,16384,2097152,2097152,16384,16777216,128,256,8,1024,16777216,16777216,16777216],[1024,16777216,256,1024,2097160,16384,65536,16384,16384,65536,16777216,16384,65536,16384,16384,65536,2097152,16384,1024,16777216,256,1024,2097152,16384,16777216],31066942⟩
theorem p36_valid : c36.fastValid p36 = true := by decide
theorem p36_root : p36 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p36_never (m : Machine) (hm : compatible p36 m) : NeverHalts m :=
  c36.sound p36 (c36.fastValid_sound _ p36_valid) m hm
def leaf36 (B : Nat) : WeightedTNFCertificate B p36 6 :=
  WeightedTNFCertificate.nonhalt p36_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p36_never m hm)
#print axioms p36_never
#print axioms leaf36

/-- tree117 path [[8,7],[1,15]]; 1RB1RD_1RC1LF_0RD0LD_1LD1RE_1RB0LB_---0LA. -/
def p37 : PartialMachine := fromCodes [7,15,11,22,13,12,14,19,7,4,24,0]
def c37 : Data 4 := ⟨0,[0,1,2,3,2,2,0,1],[128,256,8,128,128,16777216,524288,1048576,32768,16777216,524288,16777216,8192,16384,32768,18474376,8192,16777216,128,256,8,1048576,128,16777216,16777216],[512,16777216,1048584,1024,32768,1048576,2097152,128,524288,4194304,16777216,16777216,32768,18474376,18474376,65536,18474376,18474376,512,16777216,128,1024,1048576,1048576,16777216],25952098⟩
theorem p37_valid : c37.fastValid p37 = true := by decide
theorem p37_root : p37 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p37_never (m : Machine) (hm : compatible p37 m) : NeverHalts m :=
  c37.sound p37 (c37.fastValid_sound _ p37_valid) m hm
def leaf37 (B : Nat) : WeightedTNFCertificate B p37 6 :=
  WeightedTNFCertificate.nonhalt p37_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p37_never m hm)
#print axioms p37_never
#print axioms leaf37

/-- tree117 path [[8,7],[1,22]]; 1RB1LF_1RC1LF_0RD0LD_1LD1RE_1RB0LB_---0LA. -/
def p38 : PartialMachine := fromCodes [7,22,11,22,13,12,14,19,7,4,24,0]
def c38 : Data 4 := ⟨0,[0,1,2,3,2,2,0,1],[128,256,8,128,128,16777216,524288,1048576,32768,16777216,524288,16777216,8192,16384,32768,18474376,8192,16777216,128,256,8,1048576,128,16777216,16777216],[16777216,16777216,1048584,1024,32768,1048576,128,128,524288,4194304,16777216,16777216,18474376,18474376,18474376,65536,18474376,18474376,16777216,16777216,128,1024,1048576,1048576,16777216],25952098⟩
theorem p38_valid : c38.fastValid p38 = true := by decide
theorem p38_root : p38 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p38_never (m : Machine) (hm : compatible p38 m) : NeverHalts m :=
  c38.sound p38 (c38.fastValid_sound _ p38_valid) m hm
def leaf38 (B : Nat) : WeightedTNFCertificate B p38 6 :=
  WeightedTNFCertificate.nonhalt p38_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p38_never m hm)
#print axioms p38_never
#print axioms leaf38

/-- tree122 path [[8,9],[10,8]]; 1RB---_1RC1LF_0RD0RE_1LD1RE_0RC0LB_0LC0LA. -/
def p39 : PartialMachine := fromCodes [7,24,11,22,13,17,14,19,9,4,8,0]
def c39 : Data 4 := ⟨0,[0,1,0,2,3,2,0,1],[2049,34816,32768,512,32768,4,1,2048,32772,32768,32768,4,262144,2049,4,32768,32772,1048576,16777217,32768,32768,512,32768,4,16777216],[16777216,2048,32768,2048,2,1,16777216,131072,34816,2048,2,1,16777216,131072,34816,2048,524288,262144,16777216,2048,32768,34816,2,1,16777216],17043456⟩
theorem p39_valid : c39.fastValid (reflectPartial p39) = true := by decide
theorem p39_root : p39 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p39_never (m : Machine) (hm : compatible p39 m) : NeverHalts m :=
  reflectNever m (c39.sound (reflectPartial p39) (c39.fastValid_sound _ p39_valid) (reflectTable m) (reflectCompatible p39 m hm))
def leaf39 (B : Nat) : WeightedTNFCertificate B p39 6 :=
  WeightedTNFCertificate.nonhalt p39_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p39_never m hm)
#print axioms p39_never
#print axioms leaf39

/-- tree124 path [[8,15],[1,8]]; 1RB0LC_1RC1LF_0RD1RE_1LD1RE_1RD0LB_---0LA. -/
def p40 : PartialMachine := fromCodes [7,8,11,22,13,19,14,19,15,4,24,0]
def c40 : Data 4 := ⟨0,[0,1,2,3,2,2,0,3],[128,256,8,6291456,512,16777216,524288,1048576,32768,16777216,2097152,16777216,8192,16384,32768,23168008,32768,16777216,524288,1048576,8,2097152,2097152,16777216,16777216],[6291456,16777216,1024,1024,32776,1048576,2097152,4194304,4194304,4194304,16777216,2097152,23168008,23168008,65536,65536,23168008,24232968,2097152,4194304,4194304,4194304,2097152,2097152,16777216],25426738⟩
theorem p40_valid : c40.fastValid p40 = true := by decide
theorem p40_root : p40 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p40_never (m : Machine) (hm : compatible p40 m) : NeverHalts m :=
  c40.sound p40 (c40.fastValid_sound _ p40_valid) m hm
def leaf40 (B : Nat) : WeightedTNFCertificate B p40 6 :=
  WeightedTNFCertificate.nonhalt p40_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p40_never m hm)
#print axioms p40_never
#print axioms leaf40

/-- tree124 path [[8,15],[1,12]]; 1RB0LD_1RC1LF_0RD1RE_1LD1RE_1RD0LB_---0LA. -/
def p41 : PartialMachine := fromCodes [7,12,11,22,13,19,14,19,15,4,24,0]
def c41 : Data 4 := ⟨0,[0,1,2,3,2,2,0,3],[128,256,8,6291456,512,16777216,524288,1048576,32768,16777216,2097152,16777216,8192,16384,32768,23168008,32768,16777216,524288,1048576,8,2097152,2097152,16777216,16777216],[2097152,16777216,1024,1024,32776,1048576,2097152,4194304,4194304,4194304,16777216,2097152,23168008,23168008,65536,65536,23168008,24232968,2097152,4194304,4194304,4194304,2097152,2097152,16777216],25426738⟩
theorem p41_valid : c41.fastValid p41 = true := by decide
theorem p41_root : p41 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p41_never (m : Machine) (hm : compatible p41 m) : NeverHalts m :=
  c41.sound p41 (c41.fastValid_sound _ p41_valid) m hm
def leaf41 (B : Nat) : WeightedTNFCertificate B p41 6 :=
  WeightedTNFCertificate.nonhalt p41_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p41_never m hm)
#print axioms p41_never
#print axioms leaf41

/-- tree126 path [[10,13],[8,8]]; 1RB---_1RC1LF_0RD0RF_1LD1RE_0LC0LB_0RD0LA. -/
def p42 : PartialMachine := fromCodes [7,24,11,22,13,21,14,19,8,4,13,0]
def c42 : Data 4 := ⟨0,[0,1,0,2,3,2,0,1],[1,2048,32768,512,4,32768,1,2048,32768,32768,4,32768,262144,16777216,32768,32768,1048576,32768,16777216,2048,32768,512,4,32768,16777216],[16777216,2048,32768,32768,2,1,16777216,131072,1,2048,2,1,16777216,131072,16777217,2048,524288,262144,16777216,2048,32768,32768,2,1,16777216],17051648⟩
theorem p42_valid : c42.fastValid (reflectPartial p42) = true := by decide
theorem p42_root : p42 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p42_never (m : Machine) (hm : compatible p42 m) : NeverHalts m :=
  reflectNever m (c42.sound (reflectPartial p42) (c42.fastValid_sound _ p42_valid) (reflectTable m) (reflectCompatible p42 m hm))
def leaf42 (B : Nat) : WeightedTNFCertificate B p42 6 :=
  WeightedTNFCertificate.nonhalt p42_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p42_never m hm)
#print axioms p42_never
#print axioms leaf42

/-- tree126 path [[10,22],[1,23]]; 1RB1RF_1RC1LF_0RD0RF_1LD1RE_---0LB_1LF0LA. -/
def p43 : PartialMachine := fromCodes [7,23,11,22,13,21,14,19,24,4,22,0]
def c43 : Data 4 := ⟨0,[0,1,2,3,2,2,0,1],[128,256,8,1048608,16777216,1048608,524288,1048576,32768,1048616,16777216,32,8192,16384,32768,1295656,16777216,1196320,128,256,8,1048608,16777216,1048576,16777216],[2048,1048608,32,1024,32768,1048576,8388608,32,131072,4194304,1048616,32,131072,1196320,131072,65536,1229096,1196320,2048,1048576,32,1024,1048608,1048576,16777216],21755218⟩
theorem p43_valid : c43.fastValid p43 = true := by decide
theorem p43_root : p43 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p43_never (m : Machine) (hm : compatible p43 m) : NeverHalts m :=
  c43.sound p43 (c43.fastValid_sound _ p43_valid) m hm
def leaf43 (B : Nat) : WeightedTNFCertificate B p43 6 :=
  WeightedTNFCertificate.nonhalt p43_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p43_never m hm)
#print axioms p43_never
#print axioms leaf43

/-- tree128 path [[10,7],[1,14]]; 1RB1LD_1RC1LF_0RD1RF_1LD1RE_---0LB_1RB0LA. -/
def p44 : PartialMachine := fromCodes [7,14,11,22,13,23,14,19,24,4,7,0]
def c44 : Data 4 := ⟨0,[0,1,2,1,2,3,3,3],[128,256,8,0,16777216,128,128,256,32768,128,16777216,128,524288,1048576,32768,2304,16777216,524288,524288,1048576,2097152,33065344,16777216,524288,16777216],[0,2048,2048,1024,32768,256,128,2048,2048,1024,128,256,2304,33065344,8388608,4194304,2129920,1048832,33065344,33065344,8388608,4194304,33065344,33065344,16777216],33502224⟩
theorem p44_valid : c44.fastValid p44 = true := by decide
theorem p44_root : p44 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p44_never (m : Machine) (hm : compatible p44 m) : NeverHalts m :=
  c44.sound p44 (c44.fastValid_sound _ p44_valid) m hm
def leaf44 (B : Nat) : WeightedTNFCertificate B p44 6 :=
  WeightedTNFCertificate.nonhalt p44_root (support6 _) (fromCodes_noAssignedHalt _) (fun m hm => p44_never m hm)
#print axioms p44_never
#print axioms leaf44

end BB6.Agent7FAR.DepthEightBatch
