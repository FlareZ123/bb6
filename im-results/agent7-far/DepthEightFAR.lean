import WeightedTNFBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent7FAR.DepthEight
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay

/-- Every six-state partial machine has support below cut six. -/
theorem support6 (p : PartialMachine) : TNFSupport p 6 := by
  intro s t h
  exact ⟨s.1.isLt, fun mv _ => mv.next.isLt⟩

/-- The FAR code encoding has only ordinary rows or unassigned rows, never a halt row. -/
theorem fromCodes_noAssignedHalt (xs : List Nat) :
    weightedTNFNoAssignedHalt (fromCodes xs) := by
  intro s
  unfold fromCodes
  cases h : xs[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n =>
      by_cases hn : n < 24
      · simp [h, hn]
      · simp [h, hn]

/-- Parent residual 86; original-orientation FAR certificate from Actions run 45466300325.
    Table: 1RB0LB_1RC1LF_0RD1RA_1LD1RE_---0LB_---0LA. DFA size 5. -/
def p86_0 : PartialMachine := fromCodes [7,4,11,22,13,3,14,19,24,4,24,0]
def c86_0 : Data 5 := ⟨0,[0,1,4,2,3,0,4,4,4,4],[128,142606592,8,1609400303,1193321478,1073741824,8192,16384,421799424,1214518728,1073741824,1140867117,2,4,2097152,86144,1073741824,1074790914,1109409991,1430593316,1006632976,2097281,1493177864,1074348386,306184192,67375360,138412320,1609400303,1073741824,1073742848,1073741824],[1609400303,1073741856,72,1028,1609400303,16512,1342182432,1,69632,65792,1074009088,1609400303,128,1609400303,1,302268634,128,1073741826,266,1126255909,50351364,268439688,1277165580,144703744,1609400303,1609400303,16777216,268441865,1609400303,1609400303,1073741824],2145369982⟩
theorem p86_0_valid : c86_0.fastValid p86_0 = true := by decide
theorem p86_0_root : p86_0 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p86_0_support : TNFSupport p86_0 6 := support6 _
theorem p86_0_noAssignedHalt : weightedTNFNoAssignedHalt p86_0 := fromCodes_noAssignedHalt _
theorem p86_0_neverHalts (m : Machine) (hm : compatible p86_0 m) : NeverHalts m :=
  c86_0.sound p86_0 (c86_0.fastValid_sound _ p86_0_valid) m hm
def p86_0_leaf (B : Nat) : WeightedTNFCertificate B p86_0 6 :=
  farDataNonhaltLeaf p86_0_root p86_0_support p86_0_noAssignedHalt c86_0 p86_0_valid
theorem p86_0_weightedBound (B : Nat) (m : Machine) (hm : compatible p86_0 m) : WeightedBound B m :=
  (p86_0_leaf B).sound m hm
#print axioms p86_0_neverHalts
#print axioms p86_0_leaf
#print axioms p86_0_weightedBound

/-- Parent residual 86; original-orientation FAR certificate from Actions run 45466309502.
    Table: 1RB1LD_1RC1LF_0RD1RA_1LD1RE_---0LB_---0LA. DFA size 5. -/
def p86_1 : PartialMachine := fromCodes [7,14,11,22,13,3,14,19,24,4,24,0]
def c86_1 : Data 5 := ⟨0,[0,1,2,3,2,2,4,0,2,2],[128,256,134250504,1853749247,1751122752,1073741824,136060961,1048576,207672336,1108607104,1073741824,1207993928,2367840,16384,32769,1853749247,1073741824,1207993864,532514,16388,134217728,4194432,1073741824,1073741824,336734656,16688,134250496,134217857,1082130434,1310777428,1073741824],[1853749247,1078002721,1744904296,1073742848,1853749247,1048704,1141964932,1,857120,4194304,1073741952,1853749247,1853749247,1853749247,33558528,1078001664,1853749247,1862139903,128,1853749247,1,539592436,128,1242595336,1073873029,1073741857,537925456,66560,203218959,1610629380,1073741824],2012217214⟩
theorem p86_1_valid : c86_1.fastValid p86_1 = true := by decide
theorem p86_1_root : p86_1 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p86_1_support : TNFSupport p86_1 6 := support6 _
theorem p86_1_noAssignedHalt : weightedTNFNoAssignedHalt p86_1 := fromCodes_noAssignedHalt _
theorem p86_1_neverHalts (m : Machine) (hm : compatible p86_1 m) : NeverHalts m :=
  c86_1.sound p86_1 (c86_1.fastValid_sound _ p86_1_valid) m hm
def p86_1_leaf (B : Nat) : WeightedTNFCertificate B p86_1 6 :=
  farDataNonhaltLeaf p86_1_root p86_1_support p86_1_noAssignedHalt c86_1 p86_1_valid
theorem p86_1_weightedBound (B : Nat) (m : Machine) (hm : compatible p86_1 m) : WeightedBound B m :=
  (p86_1_leaf B).sound m hm
#print axioms p86_1_neverHalts
#print axioms p86_1_leaf
#print axioms p86_1_weightedBound

/-- Parent residual 112; original-orientation FAR certificate from Actions run 45466318520.
    Table: 1RB1LC_1RC1LF_0RD1RB_1LD1RE_---0LB_---0LA. DFA size 4. -/
def p112_0 : PartialMachine := fromCodes [7,10,11,22,13,7,14,19,24,4,24,0]
def c112_0 : Data 4 := ⟨0,[0,1,2,3,2,2,0,1],[136,260,8,1048708,16777216,16778240,524288,1048580,32768,17301512,16777216,17301504,5454640,30565136,2658308,33554364,17301504,16777216,128,278784,8,5243012,17301512,16777216,16777216],[1040,16777232,128,1024,2659212,1048708,128,128,524296,4194304,16777216,17302536,33554364,33554364,73728,5573120,33554364,33554364,30608948,16778240,128,1280,1048580,1048580,16777216],32243570⟩
theorem p112_0_valid : c112_0.fastValid p112_0 = true := by decide
theorem p112_0_root : p112_0 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p112_0_support : TNFSupport p112_0 6 := support6 _
theorem p112_0_noAssignedHalt : weightedTNFNoAssignedHalt p112_0 := fromCodes_noAssignedHalt _
theorem p112_0_neverHalts (m : Machine) (hm : compatible p112_0 m) : NeverHalts m :=
  c112_0.sound p112_0 (c112_0.fastValid_sound _ p112_0_valid) m hm
def p112_0_leaf (B : Nat) : WeightedTNFCertificate B p112_0 6 :=
  farDataNonhaltLeaf p112_0_root p112_0_support p112_0_noAssignedHalt c112_0 p112_0_valid
theorem p112_0_weightedBound (B : Nat) (m : Machine) (hm : compatible p112_0 m) : WeightedBound B m :=
  (p112_0_leaf B).sound m hm
#print axioms p112_0_neverHalts
#print axioms p112_0_leaf
#print axioms p112_0_weightedBound

/-- Parent residual 112; original-orientation FAR certificate from Actions run 45466327492.
    Table: 1RB1RD_1RC1LF_0RD1RB_1LD1RE_---0LB_---0LA. DFA size 4. -/
def p112_1 : PartialMachine := fromCodes [7,15,11,22,13,7,14,19,24,4,24,0]
def c112_1 : Data 4 := ⟨0,[0,1,3,2,0,1,3,3],[136,1048960,8,132,16777216,16777218,549888,16384,3670016,33290207,24232332,19169280,32896,16640,32776,16388,27820612,18890758,536704,15926852,2130944,33290207,22102600,29987904,16777216],[512,31061469,128,10651395,12186840,16516,32776,128,26748370,65536,33290207,33290239,11010560,33290207,128,10721048,16388,16516,3712773,33290207,8978560,12583944,33290207,33290207,16777216],33501042⟩
theorem p112_1_valid : c112_1.fastValid p112_1 = true := by decide
theorem p112_1_root : p112_1 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p112_1_support : TNFSupport p112_1 6 := support6 _
theorem p112_1_noAssignedHalt : weightedTNFNoAssignedHalt p112_1 := fromCodes_noAssignedHalt _
theorem p112_1_neverHalts (m : Machine) (hm : compatible p112_1 m) : NeverHalts m :=
  c112_1.sound p112_1 (c112_1.fastValid_sound _ p112_1_valid) m hm
def p112_1_leaf (B : Nat) : WeightedTNFCertificate B p112_1 6 :=
  farDataNonhaltLeaf p112_1_root p112_1_support p112_1_noAssignedHalt c112_1 p112_1_valid
theorem p112_1_weightedBound (B : Nat) (m : Machine) (hm : compatible p112_1 m) : WeightedBound B m :=
  (p112_1_leaf B).sound m hm
#print axioms p112_1_neverHalts
#print axioms p112_1_leaf
#print axioms p112_1_weightedBound

/-- Parent residual 112; original-orientation FAR certificate from Actions run 45466336469.
    Table: 1RB1LE_1RC1LF_0RD1RB_1LD1RE_---0LB_---0LA. DFA size 6. -/
def p112_2 : PartialMachine := fromCodes [7,18,11,22,13,7,14,19,24,4,24,0]
def c112_2 : Data 6 := ⟨0,[0,1,2,3,2,2,5,4,2,0,2,2],[8589934720,256,1073741832,134754467775,68719476740,74123067778,50855936,1048576,49312,76321178020,68719476736,69062377608,2219057281,16793860,68723704324,136759343102,68719476736,77379457248,33554432,68157572,8589934592,16777220,68786585600,79456895488,34749546886,16777220,77311017216,120276910861,82779324672,103350796480,70934863888,68722641184,97715342185,128,68719476736,69793218560,68719476736],[77310460032,128885269650,128,68719477760,74175267236,1048704,129154752694,33554432,34086912,4194304,69878169988,77310460032,129175725238,129175725238,94522908802,17448370192,117431915438,117431912878,128885269650,85932966928,33554432,268435456,16777220,82797412750,128,128885269650,60132163586,52891049233,68736253956,74207216014,128851648514,94560650560,51542302736,68719543296,78670233864,17825796,68719476736],128847970174⟩
theorem p112_2_valid : c112_2.fastValid p112_2 = true := by decide
theorem p112_2_root : p112_2 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p112_2_support : TNFSupport p112_2 6 := support6 _
theorem p112_2_noAssignedHalt : weightedTNFNoAssignedHalt p112_2 := fromCodes_noAssignedHalt _
theorem p112_2_neverHalts (m : Machine) (hm : compatible p112_2 m) : NeverHalts m :=
  c112_2.sound p112_2 (c112_2.fastValid_sound _ p112_2_valid) m hm
def p112_2_leaf (B : Nat) : WeightedTNFCertificate B p112_2 6 :=
  farDataNonhaltLeaf p112_2_root p112_2_support p112_2_noAssignedHalt c112_2 p112_2_valid
theorem p112_2_weightedBound (B : Nat) (m : Machine) (hm : compatible p112_2 m) : WeightedBound B m :=
  (p112_2_leaf B).sound m hm
#print axioms p112_2_neverHalts
#print axioms p112_2_leaf
#print axioms p112_2_weightedBound

/-- Parent residual 112; original-orientation FAR certificate from Actions run 45466346380.
    Table: 1RB1LF_1RC1LF_0RD1RB_1LD1RE_---0LB_---0LA. DFA size 4. -/
def p112_3 : PartialMachine := fromCodes [7,22,11,22,13,7,14,19,24,4,24,0]
def c112_3 : Data 4 := ⟨0,[0,1,2,3,2,2,0,1],[2097280,524737,29892904,1048704,16777480,16778241,525321,1048576,8054787,16777217,16777216,16777227,16785564,16800,184843,33554431,16777217,16777217,128,1054980,2097160,1048704,16777217,16777219,16777216],[16777216,16777216,128,1024,33226687,1048708,128,128,532480,4194304,16777216,17302537,18359437,18359437,532480,73729,33554351,33062316,21169760,16778240,128,1024,1048576,1048708,16777216],30146422⟩
theorem p112_3_valid : c112_3.fastValid p112_3 = true := by decide
theorem p112_3_root : p112_3 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p112_3_support : TNFSupport p112_3 6 := support6 _
theorem p112_3_noAssignedHalt : weightedTNFNoAssignedHalt p112_3 := fromCodes_noAssignedHalt _
theorem p112_3_neverHalts (m : Machine) (hm : compatible p112_3 m) : NeverHalts m :=
  c112_3.sound p112_3 (c112_3.fastValid_sound _ p112_3_valid) m hm
def p112_3_leaf (B : Nat) : WeightedTNFCertificate B p112_3 6 :=
  farDataNonhaltLeaf p112_3_root p112_3_support p112_3_noAssignedHalt c112_3 p112_3_valid
theorem p112_3_weightedBound (B : Nat) (m : Machine) (hm : compatible p112_3 m) : WeightedBound B m :=
  (p112_3_leaf B).sound m hm
#print axioms p112_3_neverHalts
#print axioms p112_3_leaf
#print axioms p112_3_weightedBound

end BB6.Agent7FAR.DepthEight
