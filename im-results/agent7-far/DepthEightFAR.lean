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


/-! ## Four genuine one-hole frontier closures (24 Nov 2026)

These four tables belong to the 101-entry siblingFinalRoster, unlike the six
growth-covered two-hole alternatives above. -/

/-- Parent 85, F/0 hole; table 1RB0LD_1RC1LF_0RD1LA_1LD1RE_1RD0LB_---0LA.
    Four-state original-orientation hit, Actions run 45469713882. -/
def p85_0 : PartialMachine := fromCodes [7,12,11,22,13,2,14,19,15,4,24,0]
def c85_0 : Data 4 := ⟨0,[0,1,2,3,2,2,0,3],
  [4194432,256,2097160,7340096,2359808,16777728,2621568,3145728,1081344,23658624,2097152,19957760,8212,16385,32768,33131976,1083392,26561300,5767312,1048576,2097160,6291456,2097152,16777216,16777216],
  [6815948,31457345,7373896,1024,7372872,3932872,2097152,6292480,7373896,6291456,23593088,16253128,33411020,33131983,33131983,2165760,33131976,33411035,6291456,6292480,6291456,6291456,6291456,6291456,16777216],
  25688882⟩
theorem p85_0_valid : c85_0.fastValid p85_0 = true := by decide
theorem p85_0_root : p85_0 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p85_0_support : TNFSupport p85_0 6 := support6 _
theorem p85_0_noAssignedHalt : weightedTNFNoAssignedHalt p85_0 := fromCodes_noAssignedHalt _
theorem p85_0_neverHalts (m : Machine) (hm : compatible p85_0 m) : NeverHalts m :=
  c85_0.sound p85_0 (c85_0.fastValid_sound _ p85_0_valid) m hm
def p85_0_leaf (B : Nat) : WeightedTNFCertificate B p85_0 6 :=
  farDataNonhaltLeaf p85_0_root p85_0_support p85_0_noAssignedHalt c85_0 p85_0_valid
theorem p85_0_weightedBound (B : Nat) (m : Machine) (hm : compatible p85_0 m) : WeightedBound B m :=
  (p85_0_leaf B).sound m hm
#print axioms p85_0_neverHalts
#print axioms p85_0_leaf
#print axioms p85_0_weightedBound

/-- Parent 85, A/1=`1RD` then E/0=`1RC`; exact one-hole table 1RB1RD_1RC1LF_0RD1LA_1LD1RE_1RC0LB_---0LA.
    Five-state original-orientation SMT hit, Actions run 45524530843. -/
def p85_1 : PartialMachine := fromCodes [7, 15, 11, 22, 13, 2, 14, 19, 11, 4, 24, 0]
def c85_1 : Data 5 := ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 2, 1],
  [136, 256, 134218889, 0, 272630146, 1074790528, 268967937, 1048716, 1073774592, 2068959135, 1048576, 1073742336, 86581248, 1064968, 553746452, 2068959135, 536986387, 1207992336, 2097289, 256, 134217732, 1048716, 33554692, 1107296256, 140, 1614810380, 69256712, 16778377, 16826640, 1073742352, 1073741824],
  [1644233236, 1095795721, 16778249, 16778240, 1610645504, 3145868, 2097152, 16778249, 2068959135, 541065216, 2068959135, 2068959135, 32768, 2068959135, 2068959135, 268500996, 2068959135, 2138165151, 136315392, 2068959135, 16778249, 16778249, 1048716, 3145868, 1346372096, 2017476636, 2064715549, 306185744, 1750171665, 1048716, 1073741824],
  1993079666⟩
theorem p85_1_valid : c85_1.fastValid p85_1 = true := by decide
theorem p85_1_root : p85_1 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p85_1_support : TNFSupport p85_1 6 := support6 _
theorem p85_1_noAssignedHalt : weightedTNFNoAssignedHalt p85_1 := fromCodes_noAssignedHalt _
theorem p85_1_neverHalts (m : Machine) (hm : compatible p85_1 m) : NeverHalts m :=
  c85_1.sound p85_1 (c85_1.fastValid_sound _ p85_1_valid) m hm
def p85_1_leaf (B : Nat) : WeightedTNFCertificate B p85_1 6 :=
  farDataNonhaltLeaf p85_1_root p85_1_support p85_1_noAssignedHalt c85_1 p85_1_valid
theorem p85_1_weightedBound (B : Nat) (m : Machine) (hm : compatible p85_1 m) : WeightedBound B m :=
  (p85_1_leaf B).sound m hm
#print axioms p85_1_neverHalts
#print axioms p85_1_leaf
#print axioms p85_1_weightedBound

/-- Parent 85, A/1=`1RD` then E/0=`1RD`; exact one-hole table 1RB1RD_1RC1LF_0RD1LA_1LD1RE_1RD0LB_---0LA.
    Five-state original-orientation SMT hit, Actions run 45525084160. -/
def p85_2 : PartialMachine := fromCodes [7, 15, 11, 22, 13, 2, 14, 19, 15, 4, 24, 0]
def c85_2 : Data 5 := ⟨0,[0, 1, 4, 2, 3, 1, 0, 1, 4, 4],
  [128, 33554688, 8, 1551476488, 268444164, 1073741824, 269000708, 16384, 136347648, 1551476488, 2129920, 1073741824, 1048704, 1048832, 2129920, 2129920, 33280, 1073741824, 132, 67109120, 1048584, 2130944, 1481647616, 1073741826, 33562624, 67108864, 134250504, 1551476488, 134848512, 1073741834, 1073741824],
  [1073742336, 1073741824, 1477477376, 1024, 204579848, 1064968, 32768, 33792, 1550951432, 65536, 1551476488, 1551476492, 1073906192, 1551476488, 33792, 1024, 2129920, 3178504, 134349316, 1476501512, 33792, 1024, 1211138312, 3162120, 134217730, 1551476488, 1551476488, 272703488, 1551476488, 1585030920, 1073741824],
  2145336190⟩
theorem p85_2_valid : c85_2.fastValid p85_2 = true := by decide
theorem p85_2_root : p85_2 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p85_2_support : TNFSupport p85_2 6 := support6 _
theorem p85_2_noAssignedHalt : weightedTNFNoAssignedHalt p85_2 := fromCodes_noAssignedHalt _
theorem p85_2_neverHalts (m : Machine) (hm : compatible p85_2 m) : NeverHalts m :=
  c85_2.sound p85_2 (c85_2.fastValid_sound _ p85_2_valid) m hm
def p85_2_leaf (B : Nat) : WeightedTNFCertificate B p85_2 6 :=
  farDataNonhaltLeaf p85_2_root p85_2_support p85_2_noAssignedHalt c85_2 p85_2_valid
theorem p85_2_weightedBound (B : Nat) (m : Machine) (hm : compatible p85_2 m) : WeightedBound B m :=
  (p85_2_leaf B).sound m hm
#print axioms p85_2_neverHalts
#print axioms p85_2_leaf
#print axioms p85_2_weightedBound

/-- Parent 114, A/1 hole; table 1RB---_1RC1LF_0RD0RC_1LD1RE_0LB0LB_0RC0LA.
    One-state reflected hit, Actions run 45469722441. -/
def p114_0 : PartialMachine := fromCodes [7,24,11,22,13,9,14,19,4,4,9,0]
def c114_0 : Data 1 := ⟨0,[0,0],[1,32,8,8,2,8,64],[64,32,8,32,2,1,64],64⟩
theorem p114_0_valid : c114_0.fastValid (reflectPartial p114_0) = true := by decide
theorem p114_0_root : p114_0 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p114_0_support : TNFSupport p114_0 6 := support6 _
theorem p114_0_noAssignedHalt : weightedTNFNoAssignedHalt p114_0 := fromCodes_noAssignedHalt _
theorem p114_0_neverHalts (m : Machine) (hm : compatible p114_0 m) : NeverHalts m :=
  reflectNever m
    (c114_0.sound (reflectPartial p114_0)
      (c114_0.fastValid_sound _ p114_0_valid)
      (reflectTable m) (reflectCompatible p114_0 m hm))
def p114_0_leaf (B : Nat) : WeightedTNFCertificate B p114_0 6 :=
  WeightedTNFCertificate.nonhalt p114_0_root p114_0_support p114_0_noAssignedHalt
    (fun m hm => p114_0_neverHalts m hm)
theorem p114_0_weightedBound (B : Nat) (m : Machine) (hm : compatible p114_0 m) : WeightedBound B m :=
  (p114_0_leaf B).sound m hm
#print axioms p114_0_neverHalts
#print axioms p114_0_leaf
#print axioms p114_0_weightedBound

/-- Parent 116, F/0 hole; table 1RB1LA_1RC1LF_0RD1RC_1LD1RE_0LA0LB_---0LA.
    Six-state original-orientation hit, Actions run 45469732966. -/
def p116_0 : PartialMachine := fromCodes [7,2,11,22,13,11,14,19,0,4,24,0]
def c116_0 : Data 6 := ⟨0,[0,1,3,2,5,2,4,4,4,4,4,3],
  [128,4295492034,4268168,16384,94624181697,68720541825,24584,16512,22592618682,134754598399,81739873431,73015129505,1073766529,8589959233,8589934721,8590090977,8589951105,68719612257,117571881381,107622640892,111809373370,134754598911,8589959361,68853924193,68977571328,68792484022,47397250324,134754598911,134754598911,83822266691,1734691,68830259291,241241174,8594210945,94696537831,81609295904,68719476736],
  [16512,104221133996,57445084536,8592139287,134485077502,16512,16385,16384,42983254040,65665,116389576127,8589959841,16512,4276353,16384,88289,8589959393,8589951105,99010740215,117566078911,35501638664,133623557612,98991833079,31167509753,134754598911,134754598911,81942185406,17696012934,134754598911,136902082559,4276361,129956506777,44412656419,4276353,116263612411,8658778603,68719476736],
  128844734258⟩
theorem p116_0_valid : c116_0.fastValid p116_0 = true := by decide
theorem p116_0_root : p116_0 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p116_0_support : TNFSupport p116_0 6 := support6 _
theorem p116_0_noAssignedHalt : weightedTNFNoAssignedHalt p116_0 := fromCodes_noAssignedHalt _
theorem p116_0_neverHalts (m : Machine) (hm : compatible p116_0 m) : NeverHalts m :=
  c116_0.sound p116_0 (c116_0.fastValid_sound _ p116_0_valid) m hm
def p116_0_leaf (B : Nat) : WeightedTNFCertificate B p116_0 6 :=
  farDataNonhaltLeaf p116_0_root p116_0_support p116_0_noAssignedHalt c116_0 p116_0_valid
theorem p116_0_weightedBound (B : Nat) (m : Machine) (hm : compatible p116_0 m) : WeightedBound B m :=
  (p116_0_leaf B).sound m hm
#print axioms p116_0_neverHalts
#print axioms p116_0_leaf
#print axioms p116_0_weightedBound

/-- Parent 128, E/0 hole; table 1RB0LB_1RC1LF_0RD1RF_1LD1RE_---0LB_1RB0LA.
    Five-state original-orientation hit, Actions run 45469741496. -/
def p128_0 : PartialMachine := fromCodes [7,4,11,22,13,23,14,19,24,4,7,0]
def c128_0 : Data 5 := ⟨0,[0,1,4,2,3,0,4,4,4,4],
  [160,67109120,8,2130411502,2128313838,128,379203712,16384,134352904,915943878,1078018080,679485600,34078722,67108868,2097152,128,1082130472,2,181610458,67108864,739250336,32,1484787720,33554432,47916627,68157440,706238530,2130411502,1078001664,34078720,1073741824],
  [2130411502,545394720,910167040,3212288,2130411502,16512,34078850,32,131072,65536,310911106,2130411502,128,2130411502,32,471606654,128,68174080,710499018,545397024,545263616,378019844,714758222,70254912,2130411502,2130411502,545263616,818946048,2130411502,2130411502,1073741824],
  2145337182⟩
theorem p128_0_valid : c128_0.fastValid p128_0 = true := by decide
theorem p128_0_root : p128_0 initialSlot = some (some ⟨true, true, 1⟩) := by decide
theorem p128_0_support : TNFSupport p128_0 6 := support6 _
theorem p128_0_noAssignedHalt : weightedTNFNoAssignedHalt p128_0 := fromCodes_noAssignedHalt _
theorem p128_0_neverHalts (m : Machine) (hm : compatible p128_0 m) : NeverHalts m :=
  c128_0.sound p128_0 (c128_0.fastValid_sound _ p128_0_valid) m hm
def p128_0_leaf (B : Nat) : WeightedTNFCertificate B p128_0 6 :=
  farDataNonhaltLeaf p128_0_root p128_0_support p128_0_noAssignedHalt c128_0 p128_0_valid
theorem p128_0_weightedBound (B : Nat) (m : Machine) (hm : compatible p128_0 m) : WeightedBound B m :=
  (p128_0_leaf B).sound m hm
#print axioms p128_0_neverHalts
#print axioms p128_0_leaf
#print axioms p128_0_weightedBound


end BB6.Agent7FAR.DepthEight
