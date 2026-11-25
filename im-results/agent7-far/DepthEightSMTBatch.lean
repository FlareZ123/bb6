import DepthEightFAR

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay
open BB6.Agent7FAR.DepthEight

namespace BB6.Agent7FAR.DepthEightSMTBatch

/-!
The 78 one-hole FAR certificates below were synthesized by the sharded QF_BV
composition search in Actions run 45525504552 (DFA sizes 1–6, 2 s per
size/orientation). Each table is an exact member of the checked depth-eight
sibling residual roster. The generated Data objects are untrusted candidates;
each is independently checked here through Data.fastValid_sound.
-/

/- Roster line 1; parent 86 / tree86; path A/1=0LD → E/0=0LB; DFA 5 original; CI run 45525504552. Table: 1RB0LD_1RC1LF_0RD1RA_1LD1RE_0LB0LB_---0LA. -/
def pRoster1 : PartialMachine := fromCodes [7, 12, 11, 22, 13, 3, 14, 19, 4, 4, 24, 0]
def cRoster1 : Data 5 := ⟨0,[0, 1, 3, 2, 4, 0, 3, 3, 3, 3],
  [128, 1150140897, 10, 1560280575, 1560280575, 1073741828, 1350707236, 16384, 15552602, 1593835007, 1350707236, 1073741828, 1073741830, 4, 134234241, 69792, 128, 1073741824, 1411907810, 269522246, 270566526, 1560280575, 1560280575, 1073741824, 311214211, 337166596, 14704776, 82049, 1073741834, 1090535438, 1073741824],
  [1560280575, 1082264672, 1073743968, 1082264576, 1560280575, 16512, 1350711332, 65537, 1210332388, 65536, 1558134133, 1560280575, 129, 1560280575, 65537, 1480659257, 65664, 1073741838, 1560280575, 1560280575, 8746070, 206319679, 1560280575, 1560280575, 1284786606, 1086573964, 283924, 72974406, 1549778383, 1442840575, 1073741824],
  2013183870⟩
theorem pRoster1_valid : cRoster1.fastValid pRoster1 = true := by decide
theorem pRoster1_neverHalts (m : Machine) (hm : compatible pRoster1 m) : NeverHalts m :=
  cRoster1.sound pRoster1 (cRoster1.fastValid_sound _ pRoster1_valid) m hm
#print axioms pRoster1_neverHalts


/- Roster line 2; parent 86 / tree86; path A/1=0LD → E/0=1LD; DFA 5 original; CI run 45525504552. Table: 1RB0LD_1RC1LF_0RD1RA_1LD1RE_1LD0LB_---0LA. -/
def pRoster2 : PartialMachine := fromCodes [7, 12, 11, 22, 13, 3, 14, 19, 14, 4, 24, 0]
def cRoster2 : Data 5 := ⟨0,[0, 1, 2, 3, 2, 2, 4, 0, 2, 2],
  [128, 1311648, 37749768, 2147483647, 2147483647, 1879189551, 168308740, 1048576, 98560, 2147483647, 2147483647, 1445856520, 1191993890, 1083924490, 2106704146, 2147483647, 2147483647, 1268570114, 1078460418, 1048836, 134217728, 4194432, 128, 1073741824, 520060382, 10502144, 1504816940, 136315009, 1048162547, 1090912259, 1073741824],
  [2147483647, 2147483647, 536903745, 25577241, 2147483647, 1048704, 2147483647, 1, 393216, 4194304, 2147483647, 2147483647, 2147483647, 2147483647, 1933711920, 1917126760, 2147483647, 2147483647, 4194433, 2147483647, 1, 164184662, 128, 2147483647, 149948544, 1183662836, 1622454502, 289497602, 517314313, 1091830692, 1073741824],
  2005925758⟩
theorem pRoster2_valid : cRoster2.fastValid pRoster2 = true := by decide
theorem pRoster2_neverHalts (m : Machine) (hm : compatible pRoster2 m) : NeverHalts m :=
  cRoster2.sound pRoster2 (cRoster2.fastValid_sound _ pRoster2_valid) m hm
#print axioms pRoster2_neverHalts


/- Roster line 3; parent 86 / tree86; path A/1=0RE → E/0=0LD; DFA 5 original; CI run 45525504552. Table: 1RB0RE_1RC1LF_0RD1RA_1LD1RE_0LD0LB_---0LA. -/
def pRoster3 : PartialMachine := fromCodes [7, 17, 11, 22, 13, 3, 14, 19, 12, 4, 24, 0]
def cRoster3 : Data 5 := ⟨0,[0, 1, 4, 2, 3, 0, 4, 4, 4, 4],
  [128, 256, 4194312, 2146039807, 2146039807, 1082134528, 2105344, 16384, 1207959552, 2146039807, 2093531297, 1157632000, 2, 5, 2097152, 128, 0, 1074266112, 1929916630, 624984368, 136315008, 65537, 16896, 1073741824, 1182843296, 67109248, 134217728, 2146039807, 2146039807, 1225265153, 1073741824],
  [16, 2146039807, 64, 1024, 2146039807, 16896, 268500992, 65537, 4096, 65536, 2146039807, 2146039807, 4194304, 2146039807, 1, 16, 128, 2146039807, 378290194, 1078481152, 16777280, 274726912, 4210840, 256, 336068992, 2146039807, 1795216674, 268960000, 2146039807, 2146039807, 1073741824],
  2145271678⟩
theorem pRoster3_valid : cRoster3.fastValid pRoster3 = true := by decide
theorem pRoster3_neverHalts (m : Machine) (hm : compatible pRoster3 m) : NeverHalts m :=
  cRoster3.sound pRoster3 (cRoster3.fastValid_sound _ pRoster3_valid) m hm
#print axioms pRoster3_neverHalts


/- Roster line 6; parent 86 / tree86; path A/1=0RF → F/0=0LD; DFA 4 original; CI run 45525504552. Table: 1RB0RF_1RC1LF_0RD1RA_1LD1RE_---0LB_0LD0LA. -/
def pRoster6 : PartialMachine := fromCodes [7, 21, 11, 22, 13, 3, 14, 19, 24, 4, 12, 0]
def cRoster6 : Data 4 := ⟨0,[0, 1, 2, 1, 3, 3, 3, 3],
  [130, 256, 98382, 0, 27530406, 4, 128, 256, 33537, 130, 17110594, 17110643, 7049839, 17825880, 2097672, 33483, 28968358, 384, 6918528, 30523661, 23069222, 33544175, 29869738, 33544175, 16777216],
  [131242, 584, 576, 1024, 28956483, 260, 131809, 585, 576, 1024, 130, 390, 27362403, 29349887, 17057286, 6619977, 19306251, 32479213, 12227563, 33544175, 32474189, 24610506, 33544175, 33544175, 16777216],
  33389620⟩
theorem pRoster6_valid : cRoster6.fastValid pRoster6 = true := by decide
theorem pRoster6_neverHalts (m : Machine) (hm : compatible pRoster6 m) : NeverHalts m :=
  cRoster6.sound pRoster6 (cRoster6.fastValid_sound _ pRoster6_valid) m hm
#print axioms pRoster6_neverHalts


/- Roster line 7; parent 86 / tree86; path A/1=1RF → F/0=0LE; DFA 6 original; CI run 45525504552. Table: 1RB1RF_1RC1LF_0RD1RA_1LD1RE_---0LB_0LE0LA. -/
def pRoster7 : PartialMachine := fromCodes [7, 23, 11, 22, 13, 3, 14, 19, 24, 4, 16, 0]
def cRoster7 : Data 6 := ⟨0,[0, 1, 5, 2, 4, 3, 5, 1, 5, 5, 5, 5],
  [128, 256, 262152, 0, 68719476736, 68719476740, 2147491840, 16384, 8589967360, 132567102410, 120280908315, 137405399007, 1581058, 68157440, 134217728, 69760, 68719476736, 81807397760, 128, 67109120, 8724156544, 137405399007, 68719476736, 16512, 2147483648, 4362604544, 8724152576, 142884997, 68719476736, 136331624413, 2484674954, 4363124736, 10871635976, 137405399007, 68720525440, 137405399007, 68719476736],
  [69941200900, 85899345984, 17179869248, 1024, 8592064512, 16512, 2147647490, 262145, 266240, 65536, 71204430218, 137405399007, 8388608, 137405399007, 262144, 272629760, 128, 81807397760, 34896742400, 87271747791, 1090523200, 335545856, 137405399007, 16512, 34897788928, 137436837343, 1082396744, 17180393472, 115387216842, 137405366237, 34905131008, 137405399007, 1090781184, 17448304640, 137405399007, 137405399007, 68719476736],
  137296068466⟩
theorem pRoster7_valid : cRoster7.fastValid pRoster7 = true := by decide
theorem pRoster7_neverHalts (m : Machine) (hm : compatible pRoster7 m) : NeverHalts m :=
  cRoster7.sound pRoster7 (cRoster7.fastValid_sound _ pRoster7_valid) m hm
#print axioms pRoster7_neverHalts


/- Roster line 8; parent 112 / tree112; path A/1=0LC → E/0=0LA; DFA 5 original; CI run 45525504552. Table: 1RB0LC_1RC1LF_0RD1RB_1LD1RE_0LA0LB_---0LA. -/
def pRoster8 : PartialMachine := fromCodes [7, 8, 11, 22, 13, 7, 14, 19, 0, 4, 24, 0]
def cRoster8 : Data 5 := ⟨0,[0, 1, 4, 2, 3, 1, 4, 0, 4, 4],
  [128, 256, 8, 1592911258, 2113536, 1074790400, 8192, 16384, 134217736, 1593436126, 1592911258, 1073741828, 128, 256, 2097152, 2113536, 2113536, 1073741824, 2, 4, 135266304, 4309136, 16384, 1073741824, 33554432, 67109120, 134217736, 1592911258, 1592911258, 1073741824, 1073741824],
  [1593046526, 1073751170, 128, 33555456, 1552982424, 2113732, 16400, 4309136, 8192, 65536, 1592911258, 1593435614, 1083359636, 1592911258, 128, 4195328, 2113536, 2113600, 4309136, 1073742082, 8194, 4227088, 1525728264, 1065218, 1593046430, 1592911258, 33554560, 268436480, 1592911258, 1592911258, 1073741824],
  2141073262⟩
theorem pRoster8_valid : cRoster8.fastValid pRoster8 = true := by decide
theorem pRoster8_neverHalts (m : Machine) (hm : compatible pRoster8 m) : NeverHalts m :=
  cRoster8.sound pRoster8 (cRoster8.fastValid_sound _ pRoster8_valid) m hm
#print axioms pRoster8_neverHalts


/- Roster line 9; parent 112 / tree112; path A/1=0LC → E/0=1RA; DFA 5 original; CI run 45525504552. Table: 1RB0LC_1RC1LF_0RD1RB_1LD1RE_1RA0LB_---0LA. -/
def pRoster9 : PartialMachine := fromCodes [7, 8, 11, 22, 13, 7, 14, 19, 3, 4, 24, 0]
def cRoster9 : Data 5 := ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 2, 0],
  [1048704, 268968752, 403243117, 1484650493, 1048640, 1076150800, 137887829, 1048576, 1615193, 1484650493, 272936960, 1073742080, 3941676, 270550288, 557072, 1484650493, 1484354832, 1073742592, 128, 282896, 134217728, 1048644, 64, 1073741824, 143789302, 4268133, 405325177, 135266432, 5551977, 1073771840, 1073741824],
  [1484650493, 2130706431, 128, 402658592, 1484650493, 135266436, 1048576, 144, 409575681, 4194304, 1484650493, 1509816317, 1484650493, 1484650493, 270656000, 1342267781, 1484650493, 1484650493, 1484650493, 1484650493, 128, 1342276864, 1048644, 135266304, 135266432, 2018374343, 805381366, 16, 138196989, 2115719594, 1073741824],
  2011955070⟩
theorem pRoster9_valid : cRoster9.fastValid pRoster9 = true := by decide
theorem pRoster9_neverHalts (m : Machine) (hm : compatible pRoster9 m) : NeverHalts m :=
  cRoster9.sound pRoster9 (cRoster9.fastValid_sound _ pRoster9_valid) m hm
#print axioms pRoster9_neverHalts


/- Roster line 10; parent 112 / tree112; path A/1=0LC → E/0=1RB; DFA 5 original; CI run 45525504552. Table: 1RB0LC_1RC1LF_0RD1RB_1LD1RE_1RB0LB_---0LA. -/
def pRoster10 : PartialMachine := fromCodes [7, 8, 11, 22, 13, 7, 14, 19, 7, 4, 24, 0]
def cRoster10 : Data 5 := ⟨0,[0, 1, 4, 2, 3, 1, 4, 0, 4, 4],
  [128, 318949776, 492132110, 1610088350, 16512, 1208123721, 532496, 16384, 134610944, 1610088350, 1601666826, 1277349888, 41104, 33024, 2097152, 278656, 402128778, 1143341056, 285212818, 156717572, 453246984, 16528, 1601699594, 1277476864, 33587344, 67108864, 169997322, 1610088350, 33558528, 1176150297, 1073741824],
  [1610088350, 1610088350, 128, 1082529288, 1311166608, 2113664, 16384, 144, 1401321472, 65536, 1610088350, 1610088350, 1604845458, 1610088350, 128, 1082529280, 16512, 2113536, 16528, 1117931920, 318767106, 16, 151404674, 235198344, 1610088350, 1610088350, 41943040, 268779648, 1610088350, 1610088415, 1073741824],
  2145369966⟩
theorem pRoster10_valid : cRoster10.fastValid pRoster10 = true := by decide
theorem pRoster10_neverHalts (m : Machine) (hm : compatible pRoster10 m) : NeverHalts m :=
  cRoster10.sound pRoster10 (cRoster10.fastValid_sound _ pRoster10_valid) m hm
#print axioms pRoster10_neverHalts


/- Roster line 11; parent 112 / tree112; path A/1=0LC → E/0=0RF; DFA 5 original; CI run 45525504552. Table: 1RB0LC_1RC1LF_0RD1RB_1LD1RE_0RF0LB_---0LA. -/
def pRoster11 : PartialMachine := fromCodes [7, 8, 11, 22, 13, 7, 14, 19, 21, 4, 24, 0]
def cRoster11 : Data 5 := ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 2, 0],
  [1048704, 1074790656, 590890, 1545332158, 32, 1410351492, 67710976, 1048576, 40960, 2095048190, 1343881632, 1209057668, 1187968, 81920, 49200, 1545332158, 68288768, 1544568996, 100663424, 256, 134217728, 1048608, 1826578806, 1074806784, 4098, 268435844, 1081352, 135266432, 268616096, 1301316042, 1073741824],
  [1557915070, 1478223254, 128, 1040, 1209786496, 135266432, 1048576, 144, 532480, 4194304, 1545332158, 2095048190, 1587277247, 1545332158, 8320, 65552, 1545332158, 1545332158, 269041920, 1545332158, 128, 268438672, 1048608, 134217860, 135266432, 1216360577, 66690, 16, 1342283776, 269533580, 1073741824],
  2012217214⟩
theorem pRoster11_valid : cRoster11.fastValid pRoster11 = true := by decide
theorem pRoster11_neverHalts (m : Machine) (hm : compatible pRoster11 m) : NeverHalts m :=
  cRoster11.sound pRoster11 (cRoster11.fastValid_sound _ pRoster11_valid) m hm
#print axioms pRoster11_neverHalts


/- Roster line 12; parent 112 / tree112; path A/1=0LD → E/0=1LC; DFA 4 original; CI run 45525504552. Table: 1RB0LD_1RC1LF_0RD1RB_1LD1RE_1LC0LB_---0LA. -/
def pRoster12 : PartialMachine := fromCodes [7, 12, 11, 22, 13, 7, 14, 19, 10, 4, 24, 0]
def cRoster12 : Data 4 := ⟨0,[0, 1, 3, 2, 0, 1, 3, 3],
  [128, 17826048, 8, 16516, 22074381, 21045769, 8448, 16388, 3260936, 33159101, 4232, 16785672, 128, 1065393, 32776, 82052, 17541, 27700850, 569473, 7913604, 2150401, 33159101, 33159101, 16777484, 16777216],
  [50317, 33159165, 128, 1025, 33158797, 16388, 4233, 128, 57352, 65664, 33159101, 118924, 17541, 17541, 128, 1029, 16388, 16516, 33159101, 33159101, 27862668, 5785268, 33159101, 33159101, 16777216],
  33434482⟩
theorem pRoster12_valid : cRoster12.fastValid pRoster12 = true := by decide
theorem pRoster12_neverHalts (m : Machine) (hm : compatible pRoster12 m) : NeverHalts m :=
  cRoster12.sound pRoster12 (cRoster12.fastValid_sound _ pRoster12_valid) m hm
#print axioms pRoster12_neverHalts


/- Roster line 13; parent 112 / tree112; path A/1=0LD → E/0=1RD; DFA 4 original; CI run 45525504552. Table: 1RB0LD_1RC1LF_0RD1RB_1LD1RE_1RD0LB_---0LA. -/
def pRoster13 : PartialMachine := fromCodes [7, 12, 11, 22, 13, 7, 14, 19, 15, 4, 24, 0]
def cRoster13 : Data 4 := ⟨0,[0, 1, 2, 3, 2, 2, 0, 1],
  [128, 392, 264, 128, 17302112, 25166084, 534924, 1048576, 1606784, 33161134, 2097280, 23593224, 12800, 20989956, 19439752, 33161134, 17336608, 18908804, 128, 392, 8, 1048708, 18358792, 25165824, 16777216],
  [3408267, 20465284, 128, 1024, 10269833, 1048576, 2359424, 128, 2638976, 4194304, 33161134, 33161134, 33161134, 33161134, 2695720, 2196872, 33161134, 33161134, 33554350, 33161134, 128, 1024, 1048580, 1048708, 16777216],
  32243574⟩
theorem pRoster13_valid : cRoster13.fastValid pRoster13 = true := by decide
theorem pRoster13_neverHalts (m : Machine) (hm : compatible pRoster13 m) : NeverHalts m :=
  cRoster13.sound pRoster13 (cRoster13.fastValid_sound _ pRoster13_valid) m hm
#print axioms pRoster13_neverHalts


/- Roster line 15; parent 112 / tree112; path A/1=0LD → E/0=1LF; DFA 4 original; CI run 45525504552. Table: 1RB0LD_1RC1LF_0RD1RB_1LD1RE_1LF0LB_---0LA. -/
def pRoster15 : PartialMachine := fromCodes [7, 12, 11, 22, 13, 7, 14, 19, 22, 4, 24, 0]
def cRoster15 : Data 4 := ⟨0,[0, 1, 3, 2, 0, 1, 3, 3],
  [136, 28562210, 20492, 128, 18900360, 16809984, 2106368, 16384, 2622728, 20473224, 128, 16777216, 32896, 1048968, 8, 16516, 17544, 16809992, 20448256, 3678208, 2113792, 24667528, 24667528, 16826380, 16777216],
  [20492, 18697816, 128, 1032, 33290222, 16516, 33928, 128, 21505032, 81920, 20473224, 53388, 17544, 17843336, 128, 17416, 16516, 16516, 24997768, 24667528, 21520520, 20971520, 24667528, 24671624, 16777216],
  33471350⟩
theorem pRoster15_valid : cRoster15.fastValid pRoster15 = true := by decide
theorem pRoster15_neverHalts (m : Machine) (hm : compatible pRoster15 m) : NeverHalts m :=
  cRoster15.sound pRoster15 (cRoster15.fastValid_sound _ pRoster15_valid) m hm
#print axioms pRoster15_neverHalts


/- Roster line 16; parent 112 / tree112; path A/1=1RE → E/0=1LA; DFA 4 original; CI run 45525504552. Table: 1RB1RE_1RC1LF_0RD1RB_1LD1RE_1LA0LB_---0LA. -/
def pRoster16 : PartialMachine := fromCodes [7, 19, 11, 22, 13, 7, 14, 19, 2, 4, 24, 0]
def cRoster16 : Data 4 := ⟨0,[0, 1, 2, 3, 2, 2, 0, 1],
  [128, 256, 3407881, 1048708, 17594813, 16777216, 14156038, 1048576, 18914444, 24436142, 16793856, 16777216, 3304870, 16640, 1098012, 20970943, 20970943, 16777216, 128, 256, 3145737, 1048580, 1048708, 16777218, 16777216],
  [3074, 16777216, 128, 265362, 20241580, 1048580, 4194304, 128, 524288, 4194336, 16793856, 16793856, 1903667, 20970943, 17309728, 67586, 20970943, 20970943, 16780290, 17440802, 128, 17826839, 1048576, 1048708, 16777216],
  25952114⟩
theorem pRoster16_valid : cRoster16.fastValid pRoster16 = true := by decide
theorem pRoster16_neverHalts (m : Machine) (hm : compatible pRoster16 m) : NeverHalts m :=
  cRoster16.sound pRoster16 (cRoster16.fastValid_sound _ pRoster16_valid) m hm
#print axioms pRoster16_neverHalts


/- Roster line 17; parent 112 / tree112; path A/1=1RE → E/0=0LB; DFA 4 original; CI run 45525504552. Table: 1RB1RE_1RC1LF_0RD1RB_1LD1RE_0LB0LB_---0LA. -/
def pRoster17 : PartialMachine := fromCodes [7, 19, 11, 22, 13, 7, 14, 19, 4, 4, 24, 0]
def cRoster17 : Data 4 := ⟨0,[0, 1, 3, 2, 0, 1, 3, 3],
  [128, 256, 136, 16516, 3730094, 16794118, 582030, 16512, 2622084, 19459054, 16793792, 16777216, 128, 1573260, 8, 147620, 16512, 16793604, 524290, 1048576, 3197444, 33554431, 20507630, 16777216, 16777216],
  [138272, 25231488, 128, 1024, 3731086, 16512, 65536, 128, 13381718, 65664, 19450858, 16794310, 132096, 25233537, 128, 1056, 147588, 16512, 4227080, 30375935, 9201520, 4325376, 33222638, 20638702, 16777216],
  33468274⟩
theorem pRoster17_valid : cRoster17.fastValid pRoster17 = true := by decide
theorem pRoster17_neverHalts (m : Machine) (hm : compatible pRoster17 m) : NeverHalts m :=
  cRoster17.sound pRoster17 (cRoster17.fastValid_sound _ pRoster17_valid) m hm
#print axioms pRoster17_neverHalts


/- Roster line 18; parent 112 / tree112; path A/1=1RE → E/0=1LD; DFA 4 original; CI run 45525504552. Table: 1RB1RE_1RC1LF_0RD1RB_1LD1RE_1LD0LB_---0LA. -/
def pRoster18 : PartialMachine := fromCodes [7, 19, 11, 22, 13, 7, 14, 19, 14, 4, 24, 0]
def cRoster18 : Data 4 := ⟨0,[0, 1, 3, 2, 0, 1, 3, 3],
  [128, 264, 16520, 16512, 132, 16777472, 8209, 16384, 3146884, 33291711, 24800671, 16777224, 128, 1048837, 137, 16516, 16388, 16777474, 565250, 20464645, 3147012, 24800671, 24800671, 23226370, 16777216],
  [3818637, 16933121, 128, 1049740, 7499166, 16516, 69656, 128, 16785664, 65536, 24800671, 24800671, 2106369, 24800671, 128, 20063625, 16388, 16516, 13746485, 24800671, 19529861, 7356428, 24800671, 24800671, 16777216],
  33435490⟩
theorem pRoster18_valid : cRoster18.fastValid pRoster18 = true := by decide
theorem pRoster18_neverHalts (m : Machine) (hm : compatible pRoster18 m) : NeverHalts m :=
  cRoster18.sound pRoster18 (cRoster18.fastValid_sound _ pRoster18_valid) m hm
#print axioms pRoster18_neverHalts


/- Roster line 19; parent 112 / tree112; path A/1=1RF → F/0=0LB; DFA 4 original; CI run 45525504552. Table: 1RB1RF_1RC1LF_0RD1RB_1LD1RE_---0LB_0LB0LA. -/
def pRoster19 : PartialMachine := fromCodes [7, 23, 11, 22, 13, 7, 14, 19, 24, 4, 4, 0]
def cRoster19 : Data 4 := ⟨0,[0, 1, 2, 3, 2, 2, 0, 1],
  [262272, 2097536, 3407884, 9437316, 19137024, 3457964, 2646144, 1048580, 2392064, 20901887, 17621676, 20767662, 5775360, 16388, 33312, 33550335, 16794120, 20767662, 128, 278918, 1048588, 1048708, 17302048, 1048580, 16777216],
  [27840, 14642389, 128, 8389776, 4121582, 1048708, 8650752, 128, 8930372, 4194436, 20898798, 24961967, 29495715, 31419605, 8921296, 9399489, 20967422, 24961967, 12586116, 31419605, 128, 1044, 1048580, 1048708, 16777216],
  21757810⟩
theorem pRoster19_valid : cRoster19.fastValid pRoster19 = true := by decide
theorem pRoster19_neverHalts (m : Machine) (hm : compatible pRoster19 m) : NeverHalts m :=
  cRoster19.sound pRoster19 (cRoster19.fastValid_sound _ pRoster19_valid) m hm
#print axioms pRoster19_neverHalts


/- Roster line 20; parent 112 / tree112; path A/1=1RF → F/0=1LD; DFA 2 original; CI run 45525504552. Table: 1RB1RF_1RC1LF_0RD1RB_1LD1RE_---0LB_1LD0LA. -/
def pRoster20 : PartialMachine := fromCodes [7, 23, 11, 22, 13, 7, 14, 19, 24, 4, 14, 0]
def cRoster20 : Data 2 := ⟨0,[0, 1, 0, 1],
  [130, 386, 8, 386, 4096, 384, 130, 386, 394, 386, 4096, 386, 4096],
  [2795, 128, 386, 3494, 394, 386, 2795, 128, 128, 3494, 386, 386, 4096],
  5136⟩
theorem pRoster20_valid : cRoster20.fastValid pRoster20 = true := by decide
theorem pRoster20_neverHalts (m : Machine) (hm : compatible pRoster20 m) : NeverHalts m :=
  cRoster20.sound pRoster20 (cRoster20.fastValid_sound _ pRoster20_valid) m hm
#print axioms pRoster20_neverHalts


/- Roster line 21; parent 114 / tree114; path E/0=1LB → F/0=0RC; DFA 1 reflected; CI run 45525504552. Table: 1RB---_1RC1LF_0RD0RC_1LD1RE_1LB0LB_0RC0LA. -/
def pRoster21 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 9, 14, 19, 6, 4, 9, 0]
def cRoster21 : Data 1 := ⟨0,[0, 0],
  [1, 32, 8, 8, 2, 8, 64],
  [64, 32, 8, 32, 2, 1, 64],
  64⟩
theorem pRoster21_valid : cRoster21.fastValid (reflect pRoster21) = true := by decide
theorem pRoster21_neverHalts (m : Machine) (hm : compatible pRoster21 m) : NeverHalts m :=
  cRoster21.sound (reflect pRoster21) (cRoster21.fastValid_sound _ pRoster21_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster21_neverHalts


/- Roster line 22; parent 114 / tree114; path E/0=1RB → A/1=0LD; DFA 6 original; CI run 45525504552. Table: 1RB0LD_1RC1LF_0RD0RC_1LD1RE_1RB0LB_---0LA. -/
def pRoster22 : PartialMachine := fromCodes [7, 12, 11, 22, 13, 9, 14, 19, 7, 4, 24, 0]
def cRoster22 : Data 6 := ⟨0,[0, 1, 3, 2, 4, 3, 3, 3, 5, 3, 3, 0],
  [128, 1048832, 3628094328, 137430169599, 128, 70868008962, 19950302224, 16384, 136385152, 128534017752, 35988201520, 68920836160, 6443024643, 34898247730, 134217728, 8589934592, 29666873538, 68719477664, 655360, 1114112, 673260112, 137430169599, 11279044702, 68987978240, 524290, 17319428482, 8589934592, 16, 17183605612, 70866960386, 38281218, 22684897324, 4431319148, 124239050448, 52765402802, 68719476736, 68719476736],
  [137430169599, 111670722641, 17186160724, 1024, 124239050448, 16384, 53570756914, 67108864, 1572864, 65536, 124239050456, 137430169599, 29717205474, 137430169599, 67108864, 17187750160, 8589934592, 137430120447, 137438822399, 137430169599, 34360786945, 12538471463, 137430169599, 137430300671, 133097420496, 85854869439, 73016021098, 62182135312, 102785201110, 65635734508, 128, 111670722641, 36508272246, 16, 64080181247, 8591048960, 68719476736],
  137304719214⟩
theorem pRoster22_valid : cRoster22.fastValid pRoster22 = true := by decide
theorem pRoster22_neverHalts (m : Machine) (hm : compatible pRoster22 m) : NeverHalts m :=
  cRoster22.sound pRoster22 (cRoster22.fastValid_sound _ pRoster22_valid) m hm
#print axioms pRoster22_neverHalts


/- Roster line 23; parent 114 / tree114; path E/0=0LC → F/0=0RC; DFA 1 reflected; CI run 45525504552. Table: 1RB---_1RC1LF_0RD0RC_1LD1RE_0LC0LB_0RC0LA. -/
def pRoster23 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 9, 14, 19, 8, 4, 9, 0]
def cRoster23 : Data 1 := ⟨0,[0, 0],
  [47, 60, 8, 8, 4, 8, 64],
  [64, 40, 8, 44, 6, 1, 64],
  64⟩
theorem pRoster23_valid : cRoster23.fastValid (reflect pRoster23) = true := by decide
theorem pRoster23_neverHalts (m : Machine) (hm : compatible pRoster23 m) : NeverHalts m :=
  cRoster23.sound (reflect pRoster23) (cRoster23.fastValid_sound _ pRoster23_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster23_neverHalts


/- Roster line 24; parent 114 / tree114; path E/0=0LC → F/0=0RD; DFA 1 reflected; CI run 45525504552. Table: 1RB---_1RC1LF_0RD0RC_1LD1RE_0LC0LB_0RD0LA. -/
def pRoster24 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 9, 14, 19, 8, 4, 13, 0]
def cRoster24 : Data 1 := ⟨0,[0, 0],
  [41, 40, 8, 8, 4, 8, 64],
  [64, 32, 8, 40, 2, 1, 64],
  64⟩
theorem pRoster24_valid : cRoster24.fastValid (reflect pRoster24) = true := by decide
theorem pRoster24_neverHalts (m : Machine) (hm : compatible pRoster24 m) : NeverHalts m :=
  cRoster24.sound (reflect pRoster24) (cRoster24.fastValid_sound _ pRoster24_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster24_neverHalts


/- Roster line 25; parent 114 / tree114; path E/0=0RC → F/0=0RC; DFA 1 reflected; CI run 45525504552. Table: 1RB---_1RC1LF_0RD0RC_1LD1RE_0RC0LB_0RC0LA. -/
def pRoster25 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 9, 14, 19, 9, 4, 9, 0]
def cRoster25 : Data 1 := ⟨0,[0, 0],
  [63, 44, 8, 8, 8, 8, 64],
  [64, 32, 12, 44, 14, 17, 64],
  64⟩
theorem pRoster25_valid : cRoster25.fastValid (reflect pRoster25) = true := by decide
theorem pRoster25_neverHalts (m : Machine) (hm : compatible pRoster25 m) : NeverHalts m :=
  cRoster25.sound (reflect pRoster25) (cRoster25.fastValid_sound _ pRoster25_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster25_neverHalts


/- Roster line 26; parent 114 / tree114; path E/0=0RC → F/0=0RD; DFA 1 reflected; CI run 45525504552. Table: 1RB---_1RC1LF_0RD0RC_1LD1RE_0RC0LB_0RD0LA. -/
def pRoster26 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 9, 14, 19, 9, 4, 13, 0]
def cRoster26 : Data 1 := ⟨0,[0, 0],
  [17, 32, 8, 8, 8, 8, 64],
  [64, 32, 8, 32, 2, 1, 64],
  64⟩
theorem pRoster26_valid : cRoster26.fastValid (reflect pRoster26) = true := by decide
theorem pRoster26_neverHalts (m : Machine) (hm : compatible pRoster26 m) : NeverHalts m :=
  cRoster26.sound (reflect pRoster26) (cRoster26.fastValid_sound _ pRoster26_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster26_neverHalts


/- Roster line 27; parent 114 / tree114; path E/0=0RC → F/0=0LE; DFA 1 reflected; CI run 45525504552. Table: 1RB---_1RC1LF_0RD0RC_1LD1RE_0RC0LB_0LE0LA. -/
def pRoster27 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 9, 14, 19, 9, 4, 16, 0]
def cRoster27 : Data 1 := ⟨0,[0, 0],
  [33, 34, 24, 8, 8, 16, 64],
  [64, 32, 8, 32, 2, 1, 64],
  64⟩
theorem pRoster27_valid : cRoster27.fastValid (reflect pRoster27) = true := by decide
theorem pRoster27_neverHalts (m : Machine) (hm : compatible pRoster27 m) : NeverHalts m :=
  cRoster27.sound (reflect pRoster27) (cRoster27.fastValid_sound _ pRoster27_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster27_neverHalts


/- Roster line 28; parent 114 / tree114; path E/0=0RC → F/0=1LE; DFA 1 reflected; CI run 45525504552. Table: 1RB---_1RC1LF_0RD0RC_1LD1RE_0RC0LB_1LE0LA. -/
def pRoster28 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 9, 14, 19, 9, 4, 18, 0]
def cRoster28 : Data 1 := ⟨0,[0, 0],
  [33, 34, 24, 8, 8, 16, 64],
  [64, 32, 8, 32, 2, 1, 64],
  64⟩
theorem pRoster28_valid : cRoster28.fastValid (reflect pRoster28) = true := by decide
theorem pRoster28_neverHalts (m : Machine) (hm : compatible pRoster28 m) : NeverHalts m :=
  cRoster28.sound (reflect pRoster28) (cRoster28.fastValid_sound _ pRoster28_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster28_neverHalts


/- Roster line 29; parent 114 / tree114; path E/0=1LC → F/0=0RC; DFA 1 reflected; CI run 45525504552. Table: 1RB---_1RC1LF_0RD0RC_1LD1RE_1LC0LB_0RC0LA. -/
def pRoster29 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 9, 14, 19, 10, 4, 9, 0]
def cRoster29 : Data 1 := ⟨0,[0, 0],
  [41, 40, 8, 8, 4, 8, 64],
  [64, 32, 8, 40, 2, 1, 64],
  64⟩
theorem pRoster29_valid : cRoster29.fastValid (reflect pRoster29) = true := by decide
theorem pRoster29_neverHalts (m : Machine) (hm : compatible pRoster29 m) : NeverHalts m :=
  cRoster29.sound (reflect pRoster29) (cRoster29.fastValid_sound _ pRoster29_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster29_neverHalts


/- Roster line 30; parent 114 / tree114; path E/0=1LC → F/0=0RD; DFA 1 reflected; CI run 45525504552. Table: 1RB---_1RC1LF_0RD0RC_1LD1RE_1LC0LB_0RD0LA. -/
def pRoster30 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 9, 14, 19, 10, 4, 13, 0]
def cRoster30 : Data 1 := ⟨0,[0, 0],
  [41, 40, 8, 8, 4, 8, 64],
  [64, 32, 8, 40, 2, 1, 64],
  64⟩
theorem pRoster30_valid : cRoster30.fastValid (reflect pRoster30) = true := by decide
theorem pRoster30_neverHalts (m : Machine) (hm : compatible pRoster30 m) : NeverHalts m :=
  cRoster30.sound (reflect pRoster30) (cRoster30.fastValid_sound _ pRoster30_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster30_neverHalts


/- Roster line 31; parent 114 / tree114; path E/0=1LD → F/0=0RC; DFA 1 reflected; CI run 45525504552. Table: 1RB---_1RC1LF_0RD0RC_1LD1RE_1LD0LB_0RC0LA. -/
def pRoster31 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 9, 14, 19, 14, 4, 9, 0]
def cRoster31 : Data 1 := ⟨0,[0, 0],
  [1, 32, 8, 8, 8, 8, 64],
  [64, 32, 8, 32, 2, 1, 64],
  64⟩
theorem pRoster31_valid : cRoster31.fastValid (reflect pRoster31) = true := by decide
theorem pRoster31_neverHalts (m : Machine) (hm : compatible pRoster31 m) : NeverHalts m :=
  cRoster31.sound (reflect pRoster31) (cRoster31.fastValid_sound _ pRoster31_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster31_neverHalts


/- Roster line 32; parent 115 / tree115; path F/0=0LB → E/0=0RC; DFA 3 reflected; CI run 45525504552. Table: 1RB---_1RC1LF_0RD1LC_1LD1RE_0RC0LB_0LB0LA. -/
def pRoster32 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 10, 14, 19, 9, 4, 4, 0]
def cRoster32 : Data 3 := ⟨0,[0, 1, 2, 1, 0, 1],
  [262143, 59658, 41476, 516, 60164, 139634, 228347, 256, 8964, 512, 58118, 8452, 260, 51460, 8960, 516, 60174, 44742, 262144],
  [458223, 2048, 16640, 56200, 2, 217107, 262176, 215328, 256, 2048, 8704, 20864, 458222, 2048, 256, 51456, 514, 20689, 262144],
  262144⟩
theorem pRoster32_valid : cRoster32.fastValid (reflect pRoster32) = true := by decide
theorem pRoster32_neverHalts (m : Machine) (hm : compatible pRoster32 m) : NeverHalts m :=
  cRoster32.sound (reflect pRoster32) (cRoster32.fastValid_sound _ pRoster32_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster32_neverHalts


/- Roster line 33; parent 115 / tree115; path F/0=0LB → E/0=0RD; DFA 1 reflected; CI run 45525504552. Table: 1RB---_1RC1LF_0RD1LC_1LD1RE_0RD0LB_0LB0LA. -/
def pRoster33 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 10, 14, 19, 13, 4, 4, 0]
def cRoster33 : Data 1 := ⟨0,[0, 0],
  [63, 62, 10, 8, 10, 2, 64],
  [64, 32, 20, 52, 14, 1, 64],
  64⟩
theorem pRoster33_valid : cRoster33.fastValid (reflect pRoster33) = true := by decide
theorem pRoster33_neverHalts (m : Machine) (hm : compatible pRoster33 m) : NeverHalts m :=
  cRoster33.sound (reflect pRoster33) (cRoster33.fastValid_sound _ pRoster33_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster33_neverHalts


/- Roster line 38; parent 116 / tree116; path E/0=0LF → A/1=1LA; DFA 6 original; CI run 45525504552. Table: 1RB1LA_1RC1LF_0RD1RC_1LD1RE_0LF0LB_---0LA. -/
def pRoster38 : PartialMachine := fromCodes [7, 2, 11, 22, 13, 11, 14, 19, 20, 4, 24, 0]
def cRoster38 : Data 6 := ⟨0,[0, 1, 3, 2, 4, 2, 3, 3, 3, 5, 3, 3],
  [128, 5751376688, 16392, 0, 77080521736, 70866968576, 4581269761, 16384, 4565630976, 128754347048, 134283272, 128620129320, 8196, 16384, 134217728, 134365313, 128754215976, 68753055744, 2181562369, 1196032, 2097665, 137346379433, 137346379433, 111440260136, 2148007937, 4296015904, 2097161, 17314111488, 117481564841, 105260803104, 2181579776, 6443499528, 2097280, 73182298120, 134217728, 99590744609, 68719476736],
  [16384, 96142585404, 73153904896, 68719477760, 137363156649, 16384, 16384, 16384, 62277566464, 268500992, 128754347048, 671113376, 16384, 17179893768, 16384, 65536, 134234241, 134217728, 137363156921, 137346379433, 108050514432, 17353565217, 137346379433, 137346412201, 90871393193, 85899371656, 4296015872, 17179869184, 134234240, 16392, 137346379433, 68753114112, 7148274208, 23796932777, 73148743688, 137346379433, 68719476736],
  120124837746⟩
theorem pRoster38_valid : cRoster38.fastValid pRoster38 = true := by decide
theorem pRoster38_neverHalts (m : Machine) (hm : compatible pRoster38 m) : NeverHalts m :=
  cRoster38.sound pRoster38 (cRoster38.fastValid_sound _ pRoster38_valid) m hm
#print axioms pRoster38_neverHalts


/- Roster line 40; parent 116 / tree116; path E/0=1LF → A/1=0LD; DFA 6 original; CI run 45525504552. Table: 1RB0LD_1RC1LF_0RD1RC_1LD1RE_1LF0LB_---0LA. -/
def pRoster40 : PartialMachine := fromCodes [7, 12, 11, 22, 13, 11, 14, 19, 22, 4, 24, 0]
def cRoster40 : Data 6 := ⟨0,[0, 1, 5, 2, 3, 2, 5, 4, 5, 5, 5, 5],
  [1152, 6459272520, 270607372, 0, 79593328323, 68732059904, 24576, 16384, 94976369157, 68990133965, 16384, 68719477253, 8192, 16384, 2097152, 2124288, 268460224, 68723671040, 70908938312, 11225638405, 79611072204, 268526789, 92839365194, 72357216812, 75430906180, 4633182212, 27919966976, 82076886989, 24576, 76499788202, 71408304192, 21562499072, 25923011072, 101422067663, 101422067663, 68726833154, 68719476736],
  [0, 68990029317, 71069925772, 1153, 102495808343, 16641, 17544, 50312, 16384, 65536, 68990133965, 8192, 268461248, 268460096, 16384, 65537, 2124288, 2123777, 68990136013, 68721650752, 28121845249, 268435520, 2099200, 18433, 6778020040, 4382059591, 75162004873, 17516988160, 69055637189, 69222793165, 101422067663, 101422067663, 6660581697, 17196648329, 101422067663, 102542340079, 68719476736],
  137168325426⟩
theorem pRoster40_valid : cRoster40.fastValid pRoster40 = true := by decide
theorem pRoster40_neverHalts (m : Machine) (hm : compatible pRoster40 m) : NeverHalts m :=
  cRoster40.sound pRoster40 (cRoster40.fastValid_sound _ pRoster40_valid) m hm
#print axioms pRoster40_neverHalts


/- Roster line 43; parent 116 / tree116; path E/0=1LF → A/1=1RE; DFA 4 original; CI run 45525504552. Table: 1RB1RE_1RC1LF_0RD1RC_1LD1RE_1LF0LB_---0LA. -/
def pRoster43 : PartialMachine := fromCodes [7, 19, 11, 22, 13, 11, 14, 19, 22, 4, 24, 0]
def cRoster43 : Data 4 := ⟨0,[0, 1, 0, 2, 3, 2, 0, 1],
  [262272, 24960, 5416200, 17459616, 21117494, 16777216, 532608, 16512, 5587231, 16908320, 16384, 17301506, 8192, 16640, 2097152, 2386313, 16512, 16777216, 128, 384, 13805151, 17536, 22243555, 17302528, 16777216],
  [1024, 16908832, 6340880, 1024, 7823775, 16768, 590850, 16384, 16384, 8456224, 16908320, 16512, 852096, 16512, 16384, 9502752, 2124160, 24960, 1152, 16908288, 2367880, 1024, 7694623, 16640, 16777216],
  31112062⟩
theorem pRoster43_valid : cRoster43.fastValid pRoster43 = true := by decide
theorem pRoster43_neverHalts (m : Machine) (hm : compatible pRoster43 m) : NeverHalts m :=
  cRoster43.sound pRoster43 (cRoster43.fastValid_sound _ pRoster43_valid) m hm
#print axioms pRoster43_neverHalts


/- Roster line 45; parent 117 / tree117; path E/0=1RA → A/1=0LB; DFA 5 original; CI run 45525504552. Table: 1RB0LB_1RC1LF_0RD0LD_1LD1RE_1RA0LB_---0LA. -/
def pRoster45 : PartialMachine := fromCodes [7, 4, 11, 22, 13, 12, 14, 19, 3, 4, 24, 0]
def cRoster45 : Data 5 := ⟨0,[0, 1, 4, 2, 3, 0, 4, 4, 4, 4],
  [128, 1082352097, 135341580, 2147483647, 18909519, 1073872962, 9445376, 16384, 134258956, 1215513768, 285741316, 1074890506, 270770562, 67108932, 2179072, 17024, 1, 1073741824, 909224934, 67150977, 245993286, 65537, 1206400082, 1879409950, 101269508, 370477380, 403701768, 2147483647, 84017408, 1073872896, 1073741824],
  [2147483647, 1610743808, 2147483647, 1024, 2147483647, 16384, 1610743808, 1, 521115910, 65536, 1208173704, 2147483647, 128, 2147483647, 1, 1140851344, 128, 1073872896, 2027138956, 2012458550, 1265887212, 268551313, 513484301, 1873803245, 2147483647, 2147483647, 2147483647, 527062753, 2147483647, 2147483647, 1073741824],
  2145304446⟩
theorem pRoster45_valid : cRoster45.fastValid pRoster45 = true := by decide
theorem pRoster45_neverHalts (m : Machine) (hm : compatible pRoster45 m) : NeverHalts m :=
  cRoster45.sound pRoster45 (cRoster45.fastValid_sound _ pRoster45_valid) m hm
#print axioms pRoster45_neverHalts


/- Roster line 46; parent 117 / tree117; path E/0=1RA → A/1=1LD; DFA 5 original; CI run 45525504552. Table: 1RB1LD_1RC1LF_0RD0LD_1LD1RE_1RA0LB_---0LA. -/
def pRoster46 : PartialMachine := fromCodes [7, 14, 11, 22, 13, 12, 14, 19, 3, 4, 24, 0]
def cRoster46 : Data 5 := ⟨0,[0, 1, 2, 3, 2, 2, 4, 0, 2, 0],
  [128, 256, 537149773, 1832908287, 136859713, 1073741824, 134742272, 1048576, 537440264, 1844444671, 134479873, 1073741824, 536896561, 603996160, 151552329, 1832908287, 1052673, 1073741952, 2, 134747220, 136314881, 1048704, 1, 1207959560, 537002146, 272646404, 151565576, 1, 16789505, 1073741824, 1073741824],
  [1832908287, 1762000929, 1832908287, 1024, 1832908287, 1048704, 1612841123, 1, 1745223713, 4194304, 1612841123, 1832908287, 1832908287, 1832908287, 1832908287, 84000824, 1832908287, 1832908287, 128, 1832908287, 1, 1680011544, 128, 1091568000, 1, 1352928466, 674844817, 2359314, 1064172925, 16777472, 1073741824],
  2005925758⟩
theorem pRoster46_valid : cRoster46.fastValid pRoster46 = true := by decide
theorem pRoster46_neverHalts (m : Machine) (hm : compatible pRoster46 m) : NeverHalts m :=
  cRoster46.sound pRoster46 (cRoster46.fastValid_sound _ pRoster46_valid) m hm
#print axioms pRoster46_neverHalts


/- Roster line 47; parent 117 / tree117; path E/0=0RB → F/0=0LB; DFA 1 reflected; CI run 45525504552. Table: 1RB---_1RC1LF_0RD0LD_1LD1RE_0RB0LB_0LB0LA. -/
def pRoster47 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 12, 14, 19, 5, 4, 4, 0]
def cRoster47 : Data 1 := ⟨0,[0, 0],
  [1, 32, 10, 8, 2, 2, 64],
  [64, 32, 8, 32, 2, 1, 64],
  64⟩
theorem pRoster47_valid : cRoster47.fastValid (reflect pRoster47) = true := by decide
theorem pRoster47_neverHalts (m : Machine) (hm : compatible pRoster47 m) : NeverHalts m :=
  cRoster47.sound (reflect pRoster47) (cRoster47.fastValid_sound _ pRoster47_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster47_neverHalts


/- Roster line 48; parent 117 / tree117; path E/0=0RB → F/0=1LD; DFA 1 reflected; CI run 45525504552. Table: 1RB---_1RC1LF_0RD0LD_1LD1RE_0RB0LB_1LD0LA. -/
def pRoster48 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 12, 14, 19, 5, 4, 14, 0]
def cRoster48 : Data 1 := ⟨0,[0, 0],
  [1, 32, 8, 8, 8, 8, 64],
  [64, 32, 8, 32, 2, 1, 64],
  64⟩
theorem pRoster48_valid : cRoster48.fastValid (reflect pRoster48) = true := by decide
theorem pRoster48_neverHalts (m : Machine) (hm : compatible pRoster48 m) : NeverHalts m :=
  cRoster48.sound (reflect pRoster48) (cRoster48.fastValid_sound _ pRoster48_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster48_neverHalts


/- Roster line 49; parent 117 / tree117; path E/0=1RB → A/1=1RD; DFA 4 original; CI run 45525504552. Table: 1RB1RD_1RC1LF_0RD0LD_1LD1RE_1RB0LB_---0LA. -/
def pRoster49 : PartialMachine := fromCodes [7, 15, 11, 22, 13, 12, 14, 19, 7, 4, 24, 0]
def cRoster49 : Data 4 := ⟨0,[0, 1, 2, 3, 2, 2, 0, 1],
  [4194432, 19403649, 8, 5243008, 946601, 16777472, 947664, 1048576, 22078609, 16777472, 17301504, 32770768, 23602193, 18538769, 5285128, 33554429, 25881913, 22943184, 2097280, 256, 5243020, 1049216, 128, 16777216, 16777216],
  [524832, 17302016, 24229884, 16778240, 33357753, 1049216, 2097152, 4194432, 17302016, 4194304, 16777472, 17039616, 17926437, 33554429, 33554429, 17287877, 33554429, 33554429, 25166336, 25690624, 128, 1024, 1048704, 1049216, 16777216],
  28311410⟩
theorem pRoster49_valid : cRoster49.fastValid pRoster49 = true := by decide
theorem pRoster49_neverHalts (m : Machine) (hm : compatible pRoster49 m) : NeverHalts m :=
  cRoster49.sound pRoster49 (cRoster49.fastValid_sound _ pRoster49_valid) m hm
#print axioms pRoster49_neverHalts


/- Roster line 50; parent 117 / tree117; path E/0=1RB → A/1=1LE; DFA 6 reflected; CI run 45525504552. Table: 1RB1LE_1RC1LF_0RD0LD_1LD1RE_1RB0LB_---0LA. -/
def pRoster50 : PartialMachine := fromCodes [7, 18, 11, 22, 13, 12, 14, 19, 7, 4, 24, 0]
def cRoster50 : Data 6 := ⟨0,[0, 1, 2, 4, 3, 1, 5, 5, 5, 5, 5, 5],
  [8590201345, 2048, 134217728, 512, 4096, 71177880096, 38514143776, 3072, 4096, 134217728, 4096, 136616816611, 8724526081, 1024, 115964087137, 512, 12288, 103079215616, 8592335617, 133143969761, 51684593825, 8589934592, 17793431584, 85899350017, 133143969761, 17733649408, 137438953443, 8592064512, 1090912256, 73014444032, 133143986145, 133009752033, 137438953443, 8724152320, 133009752033, 68719476736, 68719476736],
  [3072, 2048, 8, 1024, 546, 2151677953, 269025312, 545390592, 16809984, 38217583585, 8192, 4096, 1024, 2048, 2097152, 1024, 51540131840, 262144, 17179869248, 38217583585, 9663676416, 3072, 19369830400, 1073741824, 17196646400, 35441999872, 9663676416, 2048, 2148007936, 1074003968, 17448304640, 34896609280, 8589934592, 133009752033, 2147483776, 1140850720, 68719476736],
  128712329442⟩
theorem pRoster50_valid : cRoster50.fastValid (reflect pRoster50) = true := by decide
theorem pRoster50_neverHalts (m : Machine) (hm : compatible pRoster50 m) : NeverHalts m :=
  cRoster50.sound (reflect pRoster50) (cRoster50.fastValid_sound _ pRoster50_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster50_neverHalts


/- Roster line 51; parent 117 / tree117; path E/0=1RB → A/1=1LF; DFA 4 original; CI run 45525504552. Table: 1RB1LF_1RC1LF_0RD0LD_1LD1RE_1RB0LB_---0LA. -/
def pRoster51 : PartialMachine := fromCodes [7, 22, 11, 22, 13, 12, 14, 19, 7, 4, 24, 0]
def cRoster51 : Data 4 := ⟨0,[0, 1, 3, 2, 0, 1, 3, 3],
  [128, 524608, 4194313, 16512, 2182, 16777218, 4235264, 16384, 2129920, 33292287, 1056771, 16777221, 128, 17827072, 4104, 147456, 128, 16777216, 524288, 26749995, 2106881, 33292287, 23809312, 16779273, 16777216],
  [16781472, 16781472, 23289848, 16778274, 33095227, 16512, 128, 128, 33259003, 65536, 33292287, 16798402, 16847016, 16871866, 128, 4326408, 16384, 16512, 33292287, 33292287, 33292287, 7399754, 33292287, 33292287, 16777216],
  33468278⟩
theorem pRoster51_valid : cRoster51.fastValid pRoster51 = true := by decide
theorem pRoster51_neverHalts (m : Machine) (hm : compatible pRoster51 m) : NeverHalts m :=
  cRoster51.sound pRoster51 (cRoster51.fastValid_sound _ pRoster51_valid) m hm
#print axioms pRoster51_neverHalts


/- Roster line 52; parent 117 / tree117; path E/0=0RC → F/0=0RC; DFA 1 reflected; CI run 45525504552. Table: 1RB---_1RC1LF_0RD0LD_1LD1RE_0RC0LB_0RC0LA. -/
def pRoster52 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 12, 14, 19, 9, 4, 9, 0]
def cRoster52 : Data 1 := ⟨0,[0, 0],
  [1, 32, 8, 8, 8, 8, 64],
  [64, 32, 8, 32, 2, 1, 64],
  64⟩
theorem pRoster52_valid : cRoster52.fastValid (reflect pRoster52) = true := by decide
theorem pRoster52_neverHalts (m : Machine) (hm : compatible pRoster52 m) : NeverHalts m :=
  cRoster52.sound (reflect pRoster52) (cRoster52.fastValid_sound _ pRoster52_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster52_neverHalts


/- Roster line 53; parent 121 / tree121; path F/0=0LB → E/0=0RD; DFA 1 reflected; CI run 45525504552. Table: 1RB---_1RC1LF_0RD0LE_1LD1RE_0RD0LB_0LB0LA. -/
def pRoster53 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 16, 14, 19, 13, 4, 4, 0]
def cRoster53 : Data 1 := ⟨0,[0, 0],
  [33, 34, 10, 8, 10, 2, 64],
  [64, 32, 16, 32, 2, 1, 64],
  64⟩
theorem pRoster53_valid : cRoster53.fastValid (reflect pRoster53) = true := by decide
theorem pRoster53_neverHalts (m : Machine) (hm : compatible pRoster53 m) : NeverHalts m :=
  cRoster53.sound (reflect pRoster53) (cRoster53.fastValid_sound _ pRoster53_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster53_neverHalts


/- Roster line 54; parent 122 / tree122; path E/0=0LA → A/1=0LC; DFA 5 original; CI run 45525504552. Table: 1RB0LC_1RC1LF_0RD0RE_1LD1RE_0LA0LB_---0LA. -/
def pRoster54 : PartialMachine := fromCodes [7, 8, 11, 22, 13, 17, 14, 19, 0, 4, 24, 0]
def cRoster54 : Data 5 := ⟨0,[0, 1, 3, 2, 4, 1, 3, 3, 3, 0],
  [268435600, 18688, 538969354, 2088529274, 16384, 1073758208, 536879104, 16384, 1075839232, 2088693114, 2088529274, 1140850712, 144, 1342177536, 134217728, 16793600, 2088512864, 1207959552, 268959744, 1050880, 69207344, 2088529274, 2088529274, 1073741826, 1484810662, 1961378092, 476867602, 268435456, 16384, 1073758210, 1073741824],
  [2097049082, 1342177296, 144, 1750615042, 1551385880, 134234112, 16384, 268435600, 4194306, 536936448, 2088529274, 2088529274, 2097114618, 2088529274, 268435456, 5243906, 16793600, 134217728, 2088529274, 2088529274, 342885408, 944242960, 2088529274, 2105470330, 268435456, 1342310832, 944242976, 16, 2084323640, 16384, 1073741824],
  1744809838⟩
theorem pRoster54_valid : cRoster54.fastValid pRoster54 = true := by decide
theorem pRoster54_neverHalts (m : Machine) (hm : compatible pRoster54 m) : NeverHalts m :=
  cRoster54.sound pRoster54 (cRoster54.fastValid_sound _ pRoster54_valid) m hm
#print axioms pRoster54_neverHalts


/- Roster line 55; parent 122 / tree122; path E/0=0LA → A/1=1RD; DFA 5 original; CI run 45525504552. Table: 1RB1RD_1RC1LF_0RD0RE_1LD1RE_0LA0LB_---0LA. -/
def pRoster55 : PartialMachine := fromCodes [7, 15, 11, 22, 13, 17, 14, 19, 0, 4, 24, 0]
def cRoster55 : Data 5 := ⟨0,[0, 1, 4, 2, 3, 1, 4, 1, 4, 4],
  [32904, 8453, 402785288, 0, 16384, 1073742528, 1621176329, 16384, 704807944, 2138752412, 2138752412, 1224753152, 152, 16777472, 6324232, 16384, 1091191064, 1073741824, 37855360, 707445120, 690094088, 6307992, 16384, 1107296640, 36749320, 637534224, 1745880064, 2138752412, 2138752412, 1073741960, 1073741824],
  [1748177413, 1824769176, 1478657048, 426771584, 990545288, 16576, 4227088, 4227224, 1410859036, 8454144, 2138752412, 2138752412, 201851396, 2138817948, 4194328, 1480590464, 16384, 16512, 1822070276, 1148879892, 272629904, 486540544, 980599816, 16384, 2030060808, 2138752412, 946881552, 1950401932, 2138752412, 2138752412, 1073741824],
  2141138790⟩
theorem pRoster55_valid : cRoster55.fastValid pRoster55 = true := by decide
theorem pRoster55_neverHalts (m : Machine) (hm : compatible pRoster55 m) : NeverHalts m :=
  cRoster55.sound pRoster55 (cRoster55.fastValid_sound _ pRoster55_valid) m hm
#print axioms pRoster55_neverHalts


/- Roster line 56; parent 122 / tree122; path E/0=0LA → A/1=1LE; DFA 5 reflected; CI run 45525504552. Table: 1RB1LE_1RC1LF_0RD0RE_1LD1RE_0LA0LB_---0LA. -/
def pRoster56 : PartialMachine := fromCodes [7, 18, 11, 22, 13, 17, 14, 19, 0, 4, 24, 0]
def cRoster56 : Data 5 := ⟨0,[0, 1, 3, 2, 4, 4, 4, 1, 4, 4],
  [262145, 2048, 557056, 512, 1, 1076887600, 1023408729, 3072, 2375680, 32768, 262144, 1745626576, 1538742208, 2147483615, 2147483647, 1060384848, 564139138, 1379220609, 786433, 134743057, 1061042007, 2097733, 151261184, 1075882117, 2147483615, 2147483615, 2147483647, 134217744, 598016192, 1411924744, 1073741824],
  [1024, 2048, 2883587, 1024, 8389126, 169375873, 65664, 131145, 2147483615, 2147483615, 524288, 262145, 277348616, 1610624133, 134743057, 2048, 444698762, 18223232, 1024, 2048, 819211, 1024, 1251127170, 293771409, 335613192, 545953936, 2147483615, 1070309343, 33624066, 151032064, 1073741824],
  2012478446⟩
theorem pRoster56_valid : cRoster56.fastValid (reflect pRoster56) = true := by decide
theorem pRoster56_neverHalts (m : Machine) (hm : compatible pRoster56 m) : NeverHalts m :=
  cRoster56.sound (reflect pRoster56) (cRoster56.fastValid_sound _ pRoster56_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster56_neverHalts


/- Roster line 57; parent 122 / tree122; path E/0=0LA → A/1=1LF; DFA 5 original; CI run 45525504552. Table: 1RB1LF_1RC1LF_0RD0RE_1LD1RE_0LA0LB_---0LA. -/
def pRoster57 : PartialMachine := fromCodes [7, 22, 11, 22, 13, 17, 14, 19, 0, 4, 24, 0]
def cRoster57 : Data 5 := ⟨0,[0, 1, 4, 2, 3, 1, 4, 4, 4, 4],
  [4264064, 256, 147544072, 1610604499, 138559616, 1073743872, 1074014482, 16384, 134218496, 1608736656, 1073741824, 1073741824, 128, 67113363, 6291456, 212992, 16384, 1073742848, 42228098, 75910275, 526476868, 4276224, 16384, 1074306048, 172280195, 77612032, 140656640, 1609555859, 1609555859, 1073742120, 1073741824],
  [1073743872, 1140984832, 136314896, 1077941264, 134218496, 17024, 4259968, 4259968, 268435456, 65536, 1306739712, 1073743872, 1073744896, 1176734848, 4259840, 134144, 16384, 16384, 1609555330, 1575734402, 297963536, 402719744, 409162624, 499896210, 1609555859, 1609555859, 270730240, 1547847808, 1609555859, 1610604467, 1073741824],
  2141106046⟩
theorem pRoster57_valid : cRoster57.fastValid pRoster57 = true := by decide
theorem pRoster57_neverHalts (m : Machine) (hm : compatible pRoster57 m) : NeverHalts m :=
  cRoster57.sound pRoster57 (cRoster57.fastValid_sound _ pRoster57_valid) m hm
#print axioms pRoster57_neverHalts


/- Roster line 59; parent 122 / tree122; path E/0=0RB → F/0=0LD; DFA 5 original; CI run 45525504552. Table: 1RB---_1RC1LF_0RD0RE_1LD1RE_0RB0LB_0LD0LA. -/
def pRoster59 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 17, 14, 19, 5, 4, 12, 0]
def cRoster59 : Data 5 := ⟨0,[0, 1, 4, 2, 3, 4, 1, 2, 4, 4],
  [128, 269222144, 16392, 0, 1342990595, 2621440, 1283434768, 16384, 1308895241, 510521243, 505686151, 510651551, 169889600, 67108867, 2097161, 589952, 524288, 524800, 1073750017, 16384, 1074013969, 4817036, 524416, 2638338, 44568640, 504941982, 203687048, 1585442719, 33959174, 1585446847, 1073741824],
  [1073750024, 65544, 404792344, 69239936, 1312189727, 541184, 1073741824, 4292616, 470829064, 65536, 472482841, 1141899907, 1073758464, 1585442719, 4194312, 470558096, 589952, 1446661771, 1074405385, 65544, 1543513090, 65536, 472647048, 1585442719, 1660944384, 1585442719, 302597400, 304006411, 1585442719, 1593835519, 1073741824],
  2140553042⟩
theorem pRoster59_valid : cRoster59.fastValid pRoster59 = true := by decide
theorem pRoster59_neverHalts (m : Machine) (hm : compatible pRoster59 m) : NeverHalts m :=
  cRoster59.sound pRoster59 (cRoster59.fastValid_sound _ pRoster59_valid) m hm
#print axioms pRoster59_neverHalts


/- Roster line 60; parent 122 / tree122; path E/0=0RC → F/0=0LC; DFA 4 reflected; CI run 45525504552. Table: 1RB---_1RC1LF_0RD0RE_1LD1RE_0RC0LB_0LC0LA. -/
def pRoster60 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 17, 14, 19, 9, 4, 8, 0]
def cRoster60 : Data 4 := ⟨0,[0, 1, 0, 2, 3, 2, 1, 1],
  [14340023, 1083652, 32768, 1050116, 33280, 1081348, 23060479, 1084420, 1081348, 32768, 32768, 1048580, 33554431, 23056255, 1048580, 32768, 1081604, 1048580, 31457279, 9473028, 32768, 1050116, 33282, 1048836, 16777216],
  [25480816, 2048, 1081348, 149504, 650, 1950577, 25954715, 147456, 1085220, 149504, 32770, 4342581, 25991331, 24309721, 9473796, 2048, 524290, 31210194, 25783432, 2048, 1081348, 1101604, 138, 17631579, 16777216],
  17051712⟩
theorem pRoster60_valid : cRoster60.fastValid (reflect pRoster60) = true := by decide
theorem pRoster60_neverHalts (m : Machine) (hm : compatible pRoster60 m) : NeverHalts m :=
  cRoster60.sound (reflect pRoster60) (cRoster60.fastValid_sound _ pRoster60_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster60_neverHalts


/- Roster line 61; parent 122 / tree122; path E/0=1RC → F/0=0LB; DFA 5 original; CI run 45525504552. Table: 1RB---_1RC1LF_0RD0RE_1LD1RE_1RC0LB_0LB0LA. -/
def pRoster61 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 17, 14, 19, 11, 4, 4, 0]
def cRoster61 : Data 5 := ⟨0,[0, 1, 4, 2, 3, 4, 4, 2, 4, 4],
  [128, 4194696, 4325384, 0, 795095036, 134267136, 1078092320, 16384, 134234112, 2146435069, 1290457248, 1877934076, 38273408, 71434280, 6438912, 16544, 658160228, 16512, 750970448, 210780160, 149181036, 6438924, 16384, 211862408, 1116224088, 210796800, 136348424, 2147483645, 1854831732, 2147483645, 1073741824],
  [1799359644, 1440138607, 1908936721, 207148980, 244048192, 16384, 1192663489, 4325384, 297795944, 65536, 1861222396, 2147483645, 1073819652, 2147483645, 4325384, 298222948, 16512, 1878982652, 1369253237, 4325513, 830806021, 65536, 1244518300, 212910888, 2096533925, 2147483645, 397031577, 352715044, 2147483645, 2147483645, 1073741824],
  2141044594⟩
theorem pRoster61_valid : cRoster61.fastValid pRoster61 = true := by decide
theorem pRoster61_neverHalts (m : Machine) (hm : compatible pRoster61 m) : NeverHalts m :=
  cRoster61.sound pRoster61 (cRoster61.fastValid_sound _ pRoster61_valid) m hm
#print axioms pRoster61_neverHalts


/- Roster line 62; parent 122 / tree122; path E/0=1RC → F/0=1LD; DFA 5 original; CI run 45525504552. Table: 1RB---_1RC1LF_0RD0RE_1LD1RE_1RC0LB_1LD0LA. -/
def pRoster62 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 17, 14, 19, 11, 4, 14, 0]
def cRoster62 : Data 5 := ⟨0,[0, 1, 4, 2, 3, 4, 4, 2, 4, 4],
  [2208, 2147483615, 534507260, 1026, 402157567, 0, 382238653, 16384, 1560856853, 2097152, 1457254140, 16384, 1450920953, 375523977, 2115744, 81920, 1560848468, 540672, 2112880639, 285763664, 529546405, 4210848, 16384, 222383022, 2013229055, 67692628, 215500478, 2147483647, 67108868, 2147483647, 1073741824],
  [1449888941, 0, 2147481342, 1026, 2147483647, 17536, 1380649376, 4194432, 2147483390, 66562, 0, 2145386238, 2146435071, 2147483647, 4194432, 1610547175, 16384, 2097736021, 1380649376, 4196512, 270012329, 65538, 251461374, 1610153983, 2146434814, 2147483647, 1610473206, 534183678, 2147483647, 2147483647, 1073741824],
  2141173086⟩
theorem pRoster62_valid : cRoster62.fastValid pRoster62 = true := by decide
theorem pRoster62_neverHalts (m : Machine) (hm : compatible pRoster62 m) : NeverHalts m :=
  cRoster62.sound pRoster62 (cRoster62.fastValid_sound _ pRoster62_valid) m hm
#print axioms pRoster62_neverHalts


/- Roster line 63; parent 123 / tree123; path F/0=0RA → A/1=1RF; DFA 3 original; CI run 45525504552. Table: 1RB1RF_1RC1LF_0RD1LE_1LD1RE_---0LB_0RA0LA. -/
def pRoster63 : PartialMachine := fromCodes [7, 23, 11, 22, 13, 18, 14, 19, 24, 4, 1, 0]
def cRoster63 : Data 3 := ⟨0,[0, 1, 0, 2, 0, 2],
  [8320, 256, 131081, 162017, 393220, 1, 8384, 16384, 262152, 162017, 262144, 131073, 8384, 16384, 131592, 225409, 262144, 1, 262144],
  [141344, 145633, 270337, 1024, 426760, 159936, 131072, 141345, 328705, 65536, 159937, 151745, 131104, 141345, 141345, 65536, 155777, 1, 262144],
  361746⟩
theorem pRoster63_valid : cRoster63.fastValid pRoster63 = true := by decide
theorem pRoster63_neverHalts (m : Machine) (hm : compatible pRoster63 m) : NeverHalts m :=
  cRoster63.sound pRoster63 (cRoster63.fastValid_sound _ pRoster63_valid) m hm
#print axioms pRoster63_neverHalts


/- Roster line 64; parent 123 / tree123; path F/0=0LB → E/0=0RD; DFA 1 reflected; CI run 45525504552. Table: 1RB---_1RC1LF_0RD1LE_1LD1RE_0RD0LB_0LB0LA. -/
def pRoster64 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 18, 14, 19, 13, 4, 4, 0]
def cRoster64 : Data 1 := ⟨0,[0, 0],
  [33, 34, 10, 8, 10, 2, 64],
  [64, 32, 16, 32, 2, 1, 64],
  64⟩
theorem pRoster64_valid : cRoster64.fastValid (reflect pRoster64) = true := by decide
theorem pRoster64_neverHalts (m : Machine) (hm : compatible pRoster64 m) : NeverHalts m :=
  cRoster64.sound (reflect pRoster64) (cRoster64.fastValid_sound _ pRoster64_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster64_neverHalts


/- Roster line 65; parent 123 / tree123; path F/0=1RC → E/0=0RD; DFA 2 reflected; CI run 45525504552. Table: 1RB---_1RC1LF_0RD1LE_1LD1RE_0RD0LB_1RC0LA. -/
def pRoster65 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 18, 14, 19, 13, 4, 11, 0]
def cRoster65 : Data 2 := ⟨0,[0, 1, 0, 1],
  [3077, 2342, 514, 3984, 514, 2054, 7167, 514, 514, 512, 514, 2, 4096],
  [4096, 2048, 1024, 2180, 2, 3073, 7167, 6874, 1024, 2052, 2, 1, 4096],
  4160⟩
theorem pRoster65_valid : cRoster65.fastValid (reflect pRoster65) = true := by decide
theorem pRoster65_neverHalts (m : Machine) (hm : compatible pRoster65 m) : NeverHalts m :=
  cRoster65.sound (reflect pRoster65) (cRoster65.fastValid_sound _ pRoster65_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster65_neverHalts


/- Roster line 66; parent 124 / tree124; path E/0=0RB → F/0=0LE; DFA 6 original; CI run 45525504552. Table: 1RB---_1RC1LF_0RD1RE_1LD1RE_0RB0LB_0LE0LA. -/
def pRoster66 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 19, 14, 19, 5, 4, 16, 0]
def cRoster66 : Data 6 := ⟨0,[0, 1, 4, 2, 3, 5, 4, 4, 4, 4, 1, 4],
  [128, 256, 68719476744, 0, 2, 49408, 6476537864, 16384, 2283832322, 92847859626, 17213956104, 92852055982, 2147491840, 4294967296, 2097160, 114816, 524288, 92847859626, 33554440, 67108864, 81205691420, 17181982856, 68719476477, 82896277577, 33554440, 67108864, 134217728, 92847859626, 2181038082, 137438953471, 33554444, 67108904, 134251008, 92512314762, 128, 49280, 68719476736],
  [68719476746, 88385119242, 73216377866, 1024, 19564913922, 16384, 68719493130, 17179869192, 268500992, 65536, 92847858090, 68786585864, 68719493128, 86237103370, 17179869184, 17179869184, 128, 73150759176, 70866960384, 92847859626, 23891362826, 17448370176, 134317866, 4362076456, 68719476736, 92847859626, 335544320, 68987995144, 92847859626, 75363303976, 68719476736, 86235497738, 17448304642, 86167797760, 88217347466, 73083650824, 68719476736],
  120256970614⟩
theorem pRoster66_valid : cRoster66.fastValid pRoster66 = true := by decide
theorem pRoster66_neverHalts (m : Machine) (hm : compatible pRoster66 m) : NeverHalts m :=
  cRoster66.sound pRoster66 (cRoster66.fastValid_sound _ pRoster66_valid) m hm
#print axioms pRoster66_neverHalts


/- Roster line 67; parent 124 / tree124; path E/0=1RB → A/1=0LB; DFA 5 original; CI run 45525504552. Table: 1RB0LB_1RC1LF_0RD1RE_1LD1RE_1RB0LB_---0LA. -/
def pRoster67 : PartialMachine := fromCodes [7, 4, 11, 22, 13, 19, 14, 19, 7, 4, 24, 0]
def cRoster67 : Data 5 := ⟨0,[0, 1, 3, 2, 4, 0, 3, 3, 3, 3],
  [128, 66464, 71609, 1752922047, 128, 1073872896, 1476649459, 16512, 1210278063, 1610831522, 1752790711, 1484760699, 19, 134217751, 134234257, 16512, 1210278823, 1073741856, 536461294, 1752905398, 1752920759, 1752922047, 1752913847, 1752922030, 1603504, 5977762, 1618027142, 17, 599360, 1081816985, 1073741824],
  [1752922047, 1073872896, 1610831522, 1073940006, 1752922047, 16512, 1073741856, 17, 542865339, 65568, 1610695328, 1820325823, 145, 1752922047, 17, 1748727743, 16512, 1073872896, 1752922047, 1752922047, 544962495, 1752921791, 1752922047, 2021652479, 136388601, 1184493954, 678572082, 1752920995, 71609, 1115040, 1073741824],
  2013216622⟩
theorem pRoster67_valid : cRoster67.fastValid pRoster67 = true := by decide
theorem pRoster67_neverHalts (m : Machine) (hm : compatible pRoster67 m) : NeverHalts m :=
  cRoster67.sound pRoster67 (cRoster67.fastValid_sound _ pRoster67_valid) m hm
#print axioms pRoster67_neverHalts


/- Roster line 68; parent 124 / tree124; path E/0=1RB → A/1=1LC; DFA 5 original; CI run 45525504552. Table: 1RB1LC_1RC1LF_0RD1RE_1LD1RE_1RB0LB_---0LA. -/
def pRoster68 : PartialMachine := fromCodes [7, 10, 11, 22, 13, 19, 14, 19, 7, 4, 24, 0]
def cRoster68 : Data 5 := ⟨0,[0, 1, 4, 2, 3, 0, 4, 4, 4, 4],
  [128, 256, 8, 1580822430, 128, 1073741836, 1125655040, 16384, 134220292, 1545691548, 8192, 1342701568, 26214666, 4, 2097152, 16512, 10, 1073741836, 324599884, 335546370, 402653184, 16, 302515274, 1342177288, 301989896, 67109132, 134217728, 1580822430, 33554692, 1074790540, 1073741824],
  [1589211038, 1073742864, 1073742848, 1024, 1580822430, 16512, 1073750164, 16, 65536, 65536, 1073750148, 1580822430, 144, 1580822430, 16, 67109392, 128, 1073758348, 1475898502, 1107313668, 268435724, 335546368, 169439118, 1580855198, 1580822430, 1580822430, 370147340, 268435456, 1580822430, 1597599710, 1073741824],
  2145337198⟩
theorem pRoster68_valid : cRoster68.fastValid pRoster68 = true := by decide
theorem pRoster68_neverHalts (m : Machine) (hm : compatible pRoster68 m) : NeverHalts m :=
  cRoster68.sound pRoster68 (cRoster68.fastValid_sound _ pRoster68_valid) m hm
#print axioms pRoster68_neverHalts


/- Roster line 69; parent 124 / tree124; path E/0=1RB → A/1=1LD; DFA 5 original; CI run 45525504552. Table: 1RB1LD_1RC1LF_0RD1RE_1LD1RE_1RB0LB_---0LA. -/
def pRoster69 : PartialMachine := fromCodes [7, 14, 11, 22, 13, 19, 14, 19, 7, 4, 24, 0]
def cRoster69 : Data 5 := ⟨0,[0, 1, 2, 3, 2, 2, 4, 0, 2, 2],
  [128, 16640, 536944680, 1795024382, 128, 1074790414, 41418916, 1048576, 1073774900, 1707655606, 1074266144, 1117323456, 273162240, 1211187522, 2129928, 1795024382, 33644590, 1409376784, 2097154, 1048580, 134217856, 1048736, 1073807370, 1073741824, 750284657, 16384, 1470726596, 1048592, 23946724, 1082130464, 1073741824],
  [2063590911, 1610613776, 1024, 1024, 1795024382, 1048576, 1082917024, 16, 182051012, 4456448, 1082654880, 2147346430, 1795028478, 1795024382, 4300872, 1078001672, 1795024382, 2147346430, 128, 1795024382, 16, 1610613776, 128, 1076887566, 581976212, 1074038024, 1078001664, 65536, 710500840, 674292136, 1073741824],
  2012217198⟩
theorem pRoster69_valid : cRoster69.fastValid pRoster69 = true := by decide
theorem pRoster69_neverHalts (m : Machine) (hm : compatible pRoster69 m) : NeverHalts m :=
  cRoster69.sound pRoster69 (cRoster69.fastValid_sound _ pRoster69_valid) m hm
#print axioms pRoster69_neverHalts


/- Roster line 70; parent 124 / tree124; path E/0=1RC → A/1=1RD; DFA 5 original; CI run 45525504552. Table: 1RB1RD_1RC1LF_0RD1RE_1LD1RE_1RC0LB_---0LA. -/
def pRoster70 : PartialMachine := fromCodes [7, 15, 11, 22, 13, 19, 14, 19, 11, 4, 24, 0]
def cRoster70 : Data 5 := ⟨0,[0, 1, 4, 2, 3, 1, 4, 1, 4, 4],
  [128, 34918656, 8, 0, 1559754112, 1073741824, 39612416, 16384, 134234240, 1141915776, 16384, 1328868835, 128, 256, 2097152, 1097856, 1218471712, 1140867072, 67108992, 5243136, 136315008, 21504, 8421664, 1073758208, 33820672, 67108864, 135315456, 1559754656, 67108864, 1295540609, 1073741824],
  [1443488, 1107558408, 517470137, 1024, 486139785, 1064960, 33800, 1024, 4391936, 65536, 1140867200, 1278263424, 335839744, 1350698144, 1024, 1024, 16384, 1097856, 9454240, 1350960288, 1024, 1082131488, 134234240, 16384, 416753328, 1593833401, 268567552, 268435584, 1559754656, 1559754677, 1073741824],
  2145364850⟩
theorem pRoster70_valid : cRoster70.fastValid pRoster70 = true := by decide
theorem pRoster70_neverHalts (m : Machine) (hm : compatible pRoster70 m) : NeverHalts m :=
  cRoster70.sound pRoster70 (cRoster70.fastValid_sound _ pRoster70_valid) m hm
#print axioms pRoster70_neverHalts


/- Roster line 72; parent 124 / tree124; path E/0=1RC → A/1=1LF; DFA 5 original; CI run 45525504552. Table: 1RB1LF_1RC1LF_0RD1RE_1LD1RE_1RC0LB_---0LA. -/
def pRoster72 : PartialMachine := fromCodes [7, 22, 11, 22, 13, 19, 14, 19, 11, 4, 24, 0]
def cRoster72 : Data 5 := ⟨0,[0, 1, 3, 2, 4, 1, 3, 3, 0, 1],
  [128, 1073774976, 201326604, 1215430545, 2130176, 1073741825, 63514880, 134234240, 2097408, 1215430545, 16384, 1075839232, 128, 1048832, 134250625, 134234240, 17280, 1224737420, 9961472, 1076887688, 2129920, 1215430545, 1074807296, 1075856000, 132, 1075855624, 1108339805, 134239233, 39948770, 1073741825, 1073741824],
  [1212209408, 1212274952, 1025, 1024, 1215430545, 201343116, 16782337, 5121, 1079064577, 65536, 1215430545, 1215430545, 1215430545, 1215430545, 5121, 1074805760, 134234240, 134234244, 1087454227, 1624357915, 1079056400, 4264977, 1215430545, 1144308620, 1746999099, 1751220027, 1025, 1024, 107843987, 201343116, 1073741824],
  2013211518⟩
theorem pRoster72_valid : cRoster72.fastValid pRoster72 = true := by decide
theorem pRoster72_neverHalts (m : Machine) (hm : compatible pRoster72 m) : NeverHalts m :=
  cRoster72.sound pRoster72 (cRoster72.fastValid_sound _ pRoster72_valid) m hm
#print axioms pRoster72_neverHalts


/- Roster line 73; parent 124 / tree124; path E/0=1RD → A/1=0LC; DFA 4 original; CI run 45525504552. Table: 1RB0LC_1RC1LF_0RD1RE_1LD1RE_1RD0LB_---0LA. -/
def pRoster73 : PartialMachine := fromCodes [7, 8, 11, 22, 13, 19, 14, 19, 15, 4, 24, 0]
def cRoster73 : Data 4 := ⟨0,[0, 1, 3, 2, 0, 2, 3, 3],
  [82048, 256, 32776, 98304, 49672, 16777216, 57369, 49156, 2130952, 20972560, 32768, 20195376, 91148, 49156, 8, 32768, 32768, 16777216, 18464576, 17925636, 6340632, 23184920, 2115072, 22872101, 16777216],
  [99332, 16908288, 33792, 1024, 2130952, 115212, 42132, 99328, 111816, 65536, 20972560, 114700, 124061, 99328, 66560, 65536, 32768, 115340, 23184924, 23316028, 4195348, 6341120, 23184920, 24506047, 16777216],
  33426290⟩
theorem pRoster73_valid : cRoster73.fastValid pRoster73 = true := by decide
theorem pRoster73_neverHalts (m : Machine) (hm : compatible pRoster73 m) : NeverHalts m :=
  cRoster73.sound pRoster73 (cRoster73.fastValid_sound _ pRoster73_valid) m hm
#print axioms pRoster73_neverHalts


/- Roster line 74; parent 124 / tree124; path E/0=1RD → A/1=0LD; DFA 4 original; CI run 45525504552. Table: 1RB0LD_1RC1LF_0RD1RE_1LD1RE_1RD0LB_---0LA. -/
def pRoster74 : PartialMachine := fromCodes [7, 12, 11, 22, 13, 19, 14, 19, 15, 4, 24, 0]
def cRoster74 : Data 4 := ⟨0,[0, 1, 3, 2, 0, 2, 3, 3],
  [128, 16778496, 2327388, 98368, 29516428, 16785608, 8320, 16448, 28312584, 16835788, 32768, 17842192, 41088, 16384, 33928, 32832, 32832, 16818888, 1777810, 1188492, 2254668, 32761853, 19972660, 17850376, 16777216],
  [41153, 16901120, 12830592, 1024, 28345497, 57408, 98304, 99328, 9536120, 65536, 16827592, 57536, 42048, 99328, 99328, 65536, 32832, 57536, 32763901, 33288191, 4194948, 14835997, 32761853, 32761853, 16777216],
  33426230⟩
theorem pRoster74_valid : cRoster74.fastValid pRoster74 = true := by decide
theorem pRoster74_neverHalts (m : Machine) (hm : compatible pRoster74 m) : NeverHalts m :=
  cRoster74.sound pRoster74 (cRoster74.fastValid_sound _ pRoster74_valid) m hm
#print axioms pRoster74_neverHalts


/- Roster line 75; parent 124 / tree124; path E/0=1RD → A/1=1RD; DFA 5 original; CI run 45525504552. Table: 1RB1RD_1RC1LF_0RD1RE_1LD1RE_1RD0LB_---0LA. -/
def pRoster75 : PartialMachine := fromCodes [7, 15, 11, 22, 13, 19, 14, 19, 15, 4, 24, 0]
def cRoster75 : Data 5 := ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 2, 2],
  [128, 1073742080, 8, 1533146652, 9728, 1073741826, 34340869, 1048576, 33280, 1073774592, 2097152, 1073741824, 4202496, 16384, 136347648, 1533146652, 32768, 1073741824, 132, 100663552, 134217728, 2097152, 134251016, 1073741824, 8192, 17408, 32768, 136315904, 32768, 1073760581, 1073741824],
  [1073742336, 1342177280, 1024, 1024, 1207992836, 1048584, 2098176, 1024, 37749248, 4194304, 1073774592, 1073774592, 33280, 1533146652, 67072, 65536, 1533146652, 1600780190, 131584, 1342242816, 1024, 1024, 2097152, 3145740, 402685952, 1480656384, 1342243328, 1342243840, 1482802688, 1496318472, 1073741824],
  2010119038⟩
theorem pRoster75_valid : cRoster75.fastValid pRoster75 = true := by decide
theorem pRoster75_neverHalts (m : Machine) (hm : compatible pRoster75 m) : NeverHalts m :=
  cRoster75.sound pRoster75 (cRoster75.fastValid_sound _ pRoster75_valid) m hm
#print axioms pRoster75_neverHalts


/- Roster line 76; parent 124 / tree124; path E/0=1RD → A/1=1LF; DFA 5 original; CI run 45525504552. Table: 1RB1LF_1RC1LF_0RD1RE_1LD1RE_1RD0LB_---0LA. -/
def pRoster76 : PartialMachine := fromCodes [7, 22, 11, 22, 13, 19, 14, 19, 15, 4, 24, 0]
def cRoster76 : Data 5 := ⟨0,[0, 1, 2, 3, 2, 2, 4, 1, 2, 2],
  [128, 153567616, 135266444, 0, 187835264, 1073741858, 71894024, 1048576, 1198515350, 1610610590, 2097152, 1468920818, 137846788, 135315712, 1241887380, 1610610590, 134250496, 1608364694, 4793472, 2097408, 135266316, 2097152, 136364800, 1073741824, 1560278166, 35086340, 16900352, 3146884, 18981120, 1334702706, 1073741824],
  [1260269028, 1108344960, 1024, 1024, 1610610326, 1048704, 2098312, 1032, 4194304, 4194304, 1610610590, 1610610686, 1610610590, 1610610590, 43074560, 281083904, 1610610590, 1610610590, 1610610590, 1610610590, 1024, 1024, 2097152, 3145868, 1350731026, 1449751706, 46880144, 4391808, 1466954902, 1278264110, 1073741824],
  2010119026⟩
theorem pRoster76_valid : cRoster76.fastValid pRoster76 = true := by decide
theorem pRoster76_neverHalts (m : Machine) (hm : compatible pRoster76 m) : NeverHalts m :=
  cRoster76.sound pRoster76 (cRoster76.fastValid_sound _ pRoster76_valid) m hm
#print axioms pRoster76_neverHalts


/- Roster line 77; parent 124 / tree124; path E/0=0RF → A/1=0RD; DFA 5 original; CI run 45525504552. Table: 1RB0RD_1RC1LF_0RD1RE_1LD1RE_0RF0LB_---0LA. -/
def pRoster77 : PartialMachine := fromCodes [7, 13, 11, 22, 13, 19, 14, 19, 21, 4, 24, 0]
def cRoster77 : Data 5 := ⟨0,[0, 1, 3, 2, 4, 0, 3, 3, 3, 3],
  [128, 1073742080, 1073742876, 2113789887, 32, 1342439552, 1107435524, 16384, 538968064, 2113789887, 8404992, 1073741824, 524418, 67108884, 134217728, 32, 545259520, 1073741824, 524289, 1048832, 538968072, 2113789887, 75499552, 1073807616, 524288, 1154745380, 69206024, 16384, 25231392, 1075838980, 1073741824],
  [1048584, 2113789887, 1086325764, 1073742848, 2113789887, 16384, 2129920, 16, 138477568, 65536, 2113789887, 2113789887, 134217728, 2113920959, 16, 272629776, 32, 2113789887, 1075838976, 2113789887, 4261888, 7864320, 2113789887, 2113789887, 2216456, 2052586775, 71303168, 4194304, 1572707775, 1679114637, 1073741824],
  2013249406⟩
theorem pRoster77_valid : cRoster77.fastValid pRoster77 = true := by decide
theorem pRoster77_neverHalts (m : Machine) (hm : compatible pRoster77 m) : NeverHalts m :=
  cRoster77.sound pRoster77 (cRoster77.fastValid_sound _ pRoster77_valid) m hm
#print axioms pRoster77_neverHalts


/- Roster line 79; parent 126 / tree126; path F/0=0LA → A/1=1RD; DFA 2 original; CI run 45525504552. Table: 1RB1RD_1RC1LF_0RD0RF_1LD1RE_---0LB_0LA0LA. -/
def pRoster79 : PartialMachine := fromCodes [7, 15, 11, 22, 13, 21, 14, 19, 24, 4, 0, 0]
def cRoster79 : Data 2 := ⟨0,[0, 1, 0, 1],
  [640, 260, 1032, 416, 4160, 256, 640, 256, 72, 256, 4096, 260, 4096],
  [544, 544, 32, 1056, 8026, 256, 2688, 32, 32, 1024, 256, 388, 4096],
  7190⟩
theorem pRoster79_valid : cRoster79.fastValid pRoster79 = true := by decide
theorem pRoster79_neverHalts (m : Machine) (hm : compatible pRoster79 m) : NeverHalts m :=
  cRoster79.sound pRoster79 (cRoster79.fastValid_sound _ pRoster79_valid) m hm
#print axioms pRoster79_neverHalts


/- Roster line 81; parent 126 / tree126; path F/0=0LA → A/1=1LF; DFA 2 original; CI run 45525504552. Table: 1RB1LF_1RC1LF_0RD0RF_1LD1RE_---0LB_0LA0LA. -/
def pRoster81 : PartialMachine := fromCodes [7, 22, 11, 22, 13, 21, 14, 19, 24, 4, 0, 0]
def cRoster81 : Data 2 := ⟨0,[0, 1, 0, 1],
  [2208, 324, 649, 2535, 4096, 324, 128, 260, 137, 2503, 4096, 324, 4096],
  [2210, 2210, 34, 3104, 973, 454, 2210, 2210, 34, 3104, 454, 455, 4096],
  5136⟩
theorem pRoster81_valid : cRoster81.fastValid pRoster81 = true := by decide
theorem pRoster81_neverHalts (m : Machine) (hm : compatible pRoster81 m) : NeverHalts m :=
  cRoster81.sound pRoster81 (cRoster81.fastValid_sound _ pRoster81_valid) m hm
#print axioms pRoster81_neverHalts


/- Roster line 82; parent 126 / tree126; path F/0=1LA → A/1=0RF; DFA 5 original; CI run 45525504552. Table: 1RB0RF_1RC1LF_0RD0RF_1LD1RE_---0LB_1LA0LA. -/
def pRoster82 : PartialMachine := fromCodes [7, 21, 11, 22, 13, 21, 14, 19, 24, 4, 2, 0]
def cRoster82 : Data 5 := ⟨0,[0, 1, 3, 2, 0, 1, 4, 4, 4, 4],
  [128, 1410943300, 4136, 20516, 1224736896, 32, 8192, 16388, 1039687848, 1291931820, 1214513320, 4473004, 128, 134222080, 4104, 20644, 1073746056, 1207980454, 1133073540, 1140936716, 1817708328, 2112446124, 1758229376, 16516, 39925544, 72427276, 138743808, 2147319724, 1090539656, 2147319724, 1073741824],
  [32, 1351205436, 32, 1024, 2147352559, 16388, 8388609, 32, 8978952, 94240, 1291931820, 8224, 32, 16516, 32, 1078002720, 20512, 20613, 536871936, 996171308, 594027176, 940383880, 20524, 134222080, 2099842688, 2147319724, 958421120, 1351090728, 2147319724, 2147319724, 1073741824],
  2139041618⟩
theorem pRoster82_valid : cRoster82.fastValid pRoster82 = true := by decide
theorem pRoster82_neverHalts (m : Machine) (hm : compatible pRoster82 m) : NeverHalts m :=
  cRoster82.sound pRoster82 (cRoster82.fastValid_sound _ pRoster82_valid) m hm
#print axioms pRoster82_neverHalts


/- Roster line 83; parent 126 / tree126; path F/0=1RA → A/1=0LC; DFA 3 original; CI run 45525504552. Table: 1RB0LC_1RC1LF_0RD0RF_1LD1RE_---0LB_1RA0LA. -/
def pRoster83 : PartialMachine := fromCodes [7, 8, 11, 22, 13, 21, 14, 19, 24, 4, 3, 0]
def cRoster83 : Data 3 := ⟨0,[0, 1, 0, 2, 0, 2],
  [128, 82305, 2056, 4160, 475146, 64, 8192, 16516, 2056, 12355, 416861, 4096, 8192, 16768, 2056, 77889, 314813, 4160, 262144],
  [4160, 4160, 32, 197699, 388543, 24964, 4160, 133152, 32, 65536, 12289, 8192, 64, 0, 32, 66626, 4160, 8192, 262144],
  362002⟩
theorem pRoster83_valid : cRoster83.fastValid pRoster83 = true := by decide
theorem pRoster83_neverHalts (m : Machine) (hm : compatible pRoster83 m) : NeverHalts m :=
  cRoster83.sound pRoster83 (cRoster83.fastValid_sound _ pRoster83_valid) m hm
#print axioms pRoster83_neverHalts


/- Roster line 84; parent 126 / tree126; path F/0=1RA → A/1=1RD; DFA 3 original; CI run 45525504552. Table: 1RB1RD_1RC1LF_0RD0RF_1LD1RE_---0LB_1RA0LA. -/
def pRoster84 : PartialMachine := fromCodes [7, 15, 11, 22, 13, 21, 14, 19, 24, 4, 3, 0]
def cRoster84 : Data 3 := ⟨0,[0, 1, 2, 1, 0, 1],
  [8320, 8578, 367676, 524286, 415325, 4416, 194, 8512, 35168, 4546, 413685, 4160, 194, 384, 165659, 146016, 524285, 4160, 262144],
  [133632, 143968, 2080, 1024, 191994, 29126, 139776, 146016, 135264, 1024, 4546, 12738, 139776, 145920, 14880, 1024, 498150, 12738, 262144],
  345116⟩
theorem pRoster84_valid : cRoster84.fastValid pRoster84 = true := by decide
theorem pRoster84_neverHalts (m : Machine) (hm : compatible pRoster84 m) : NeverHalts m :=
  cRoster84.sound pRoster84 (cRoster84.fastValid_sound _ pRoster84_valid) m hm
#print axioms pRoster84_neverHalts


/- Roster line 85; parent 126 / tree126; path F/0=1RA → A/1=1LF; DFA 2 original; CI run 45525504552. Table: 1RB1LF_1RC1LF_0RD0RF_1LD1RE_---0LB_1RA0LA. -/
def pRoster85 : PartialMachine := fromCodes [7, 22, 11, 22, 13, 21, 14, 19, 24, 4, 3, 0]
def cRoster85 : Data 2 := ⟨0,[0, 1, 0, 1],
  [2210, 324, 200, 2534, 4096, 68, 192, 324, 200, 3559, 4096, 68, 4096],
  [2274, 2080, 2080, 1479, 717, 454, 2080, 2080, 2080, 3567, 2244, 454, 4096],
  5648⟩
theorem pRoster85_valid : cRoster85.fastValid pRoster85 = true := by decide
theorem pRoster85_neverHalts (m : Machine) (hm : compatible pRoster85 m) : NeverHalts m :=
  cRoster85.sound pRoster85 (cRoster85.fastValid_sound _ pRoster85_valid) m hm
#print axioms pRoster85_neverHalts


/- Roster line 86; parent 126 / tree126; path F/0=1LB → A/1=0RD; DFA 5 original; CI run 45525504552. Table: 1RB0RD_1RC1LF_0RD0RF_1LD1RE_---0LB_1LB0LA. -/
def pRoster86 : PartialMachine := fromCodes [7, 13, 11, 22, 13, 21, 14, 19, 24, 4, 6, 0]
def cRoster86 : Data 5 := ⟨0,[0, 1, 2, 3, 2, 2, 4, 0, 2, 2],
  [128, 256, 8, 1757136317, 1073741824, 1757136317, 524416, 1048576, 33800, 1757136317, 1073741824, 1790694845, 541597952, 1075855361, 2129920, 1757136317, 1612709888, 1757136317, 2, 4, 135266432, 32, 1612727709, 134217984, 532480, 1064960, 33280, 1048576, 1073741824, 32, 1073741824],
  [1033, 1757136317, 32, 1024, 1757136317, 1048576, 163840, 536870912, 131072, 4194304, 1757136317, 1757136317, 539525120, 1757136317, 8536064, 65536, 1757136317, 1757136317, 134217728, 1757136317, 536870912, 539033616, 32, 1757136317, 32768, 548077572, 133120, 8454144, 680117436, 256, 1073741824],
  2012217214⟩
theorem pRoster86_valid : cRoster86.fastValid pRoster86 = true := by decide
theorem pRoster86_neverHalts (m : Machine) (hm : compatible pRoster86 m) : NeverHalts m :=
  cRoster86.sound pRoster86 (cRoster86.fastValid_sound _ pRoster86_valid) m hm
#print axioms pRoster86_neverHalts


/- Roster line 87; parent 126 / tree126; path F/0=0RD → E/0=0LC; DFA 4 reflected; CI run 45525504552. Table: 1RB---_1RC1LF_0RD0RF_1LD1RE_0LC0LB_0RD0LA. -/
def pRoster87 : PartialMachine := fromCodes [7, 24, 11, 22, 13, 21, 14, 19, 8, 4, 13, 0]
def cRoster87 : Data 4 := ⟨0,[0, 1, 0, 2, 3, 2, 3, 1],
  [625181, 4819470, 4227072, 512, 4, 2129928, 15961455, 4753964, 3244548, 32768, 12, 3179008, 14671675, 21596687, 3770914, 32768, 3179008, 3179020, 17402383, 4753945, 33280, 512, 3145728, 3179012, 16777216],
  [16777216, 2048, 33280, 98816, 32770, 557585, 22844809, 2820104, 21597727, 35336, 2, 32769, 30429324, 10684986, 19499551, 2048, 524288, 1344032, 17138949, 2048, 4227584, 4229640, 557572, 1311233, 16777216],
  17051648⟩
theorem pRoster87_valid : cRoster87.fastValid (reflect pRoster87) = true := by decide
theorem pRoster87_neverHalts (m : Machine) (hm : compatible pRoster87 m) : NeverHalts m :=
  cRoster87.sound (reflect pRoster87) (cRoster87.fastValid_sound _ pRoster87_valid) m
    (by simpa only [reflect_compatible] using hm)
#print axioms pRoster87_neverHalts


/- Roster line 89; parent 126 / tree126; path F/0=1LF → A/1=1RF; DFA 4 original; CI run 45525504552. Table: 1RB1RF_1RC1LF_0RD0RF_1LD1RE_---0LB_1LF0LA. -/
def pRoster89 : PartialMachine := fromCodes [7, 23, 11, 22, 13, 21, 14, 19, 24, 4, 22, 0]
def cRoster89 : Data 4 := ⟨0,[0, 1, 2, 3, 2, 2, 0, 1],
  [128, 18897282, 137, 9437348, 19400159, 1048608, 675978, 1048576, 23126291, 33554363, 16982016, 32, 22355974, 2123116, 2659466, 33554431, 23420971, 33554431, 128, 9296784, 9, 1048678, 23478274, 1048708, 16777216],
  [2048, 1048612, 32, 2121097, 33554431, 1048576, 8388736, 32, 13589178, 4194436, 25129643, 8388640, 2500906, 33554431, 33454497, 12669720, 33554431, 33554431, 2048, 5505221, 32, 20219272, 1048672, 1048708, 16777216],
  23852882⟩
theorem pRoster89_valid : cRoster89.fastValid pRoster89 = true := by decide
theorem pRoster89_neverHalts (m : Machine) (hm : compatible pRoster89 m) : NeverHalts m :=
  cRoster89.sound pRoster89 (cRoster89.fastValid_sound _ pRoster89_valid) m hm
#print axioms pRoster89_neverHalts


/- Roster line 90; parent 128 / tree128; path F/0=1RB → A/1=1LD; DFA 4 original; CI run 45525504552. Table: 1RB1LD_1RC1LF_0RD1RF_1LD1RE_---0LB_1RB0LA. -/
def pRoster90 : PartialMachine := fromCodes [7, 14, 11, 22, 13, 23, 14, 19, 24, 4, 7, 0]
def cRoster90 : Data 4 := ⟨0,[0, 1, 2, 1, 2, 3, 3, 3],
  [128, 256, 1081384, 0, 16781312, 128, 2215, 256, 32768, 2176, 26775552, 128, 524416, 1048576, 33280, 2432, 17865856, 13129518, 17401472, 1081984, 11538944, 33136512, 17825920, 18352768, 16777216],
  [2208, 2560, 27852544, 1280, 8697888, 256, 2211, 2048, 2048, 1024, 2176, 384, 1640832, 33423234, 9014784, 22058496, 11571712, 1098666, 33136562, 33136512, 12619520, 30938112, 33136512, 33136512, 16777216],
  33502292⟩
theorem pRoster90_valid : cRoster90.fastValid pRoster90 = true := by decide
theorem pRoster90_neverHalts (m : Machine) (hm : compatible pRoster90 m) : NeverHalts m :=
  cRoster90.sound pRoster90 (cRoster90.fastValid_sound _ pRoster90_valid) m hm
#print axioms pRoster90_neverHalts


/- Roster line 91; parent 128 / tree128; path F/0=0RC → A/1=0RF; DFA 2 original; CI run 45525504552. Table: 1RB0RF_1RC1LF_0RD1RF_1LD1RE_---0LB_0RC0LA. -/
def pRoster91 : PartialMachine := fromCodes [7, 21, 11, 22, 13, 23, 14, 19, 24, 4, 9, 0]
def cRoster91 : Data 2 := ⟨0,[0, 1, 0, 1],
  [2178, 260, 520, 2436, 4096, 4, 128, 256, 521, 2084, 4096, 4, 4096],
  [2080, 2080, 2048, 1478, 5641, 388, 2080, 2048, 2048, 1344, 2052, 260, 4096],
  5136⟩
theorem pRoster91_valid : cRoster91.fastValid pRoster91 = true := by decide
theorem pRoster91_neverHalts (m : Machine) (hm : compatible pRoster91 m) : NeverHalts m :=
  cRoster91.sound pRoster91 (cRoster91.fastValid_sound _ pRoster91_valid) m hm
#print axioms pRoster91_neverHalts


/- Roster line 92; parent 128 / tree128; path F/0=1RC → A/1=1RD; DFA 2 original; CI run 45525504552. Table: 1RB1RD_1RC1LF_0RD1RF_1LD1RE_---0LB_1RC0LA. -/
def pRoster92 : PartialMachine := fromCodes [7, 15, 11, 22, 13, 23, 14, 19, 24, 4, 11, 0]
def cRoster92 : Data 2 := ⟨0,[0, 1, 0, 1],
  [2690, 256, 2573, 2434, 4096, 256, 2178, 260, 9, 256, 4608, 256, 4096],
  [512, 2048, 2048, 1024, 3853, 260, 2560, 2050, 2048, 1024, 256, 386, 4096],
  5136⟩
theorem pRoster92_valid : cRoster92.fastValid pRoster92 = true := by decide
theorem pRoster92_neverHalts (m : Machine) (hm : compatible pRoster92 m) : NeverHalts m :=
  cRoster92.sound pRoster92 (cRoster92.fastValid_sound _ pRoster92_valid) m hm
#print axioms pRoster92_neverHalts


/- Roster line 94; parent 128 / tree128; path F/0=1RC → A/1=1LF; DFA 2 original; CI run 45525504552. Table: 1RB1LF_1RC1LF_0RD1RF_1LD1RE_---0LB_1RC0LA. -/
def pRoster94 : PartialMachine := fromCodes [7, 22, 11, 22, 13, 23, 14, 19, 24, 4, 11, 0]
def cRoster94 : Data 2 := ⟨0,[0, 1, 0, 1],
  [2242, 384, 4620, 2432, 4096, 448, 128, 384, 392, 359, 4096, 256, 4096],
  [2176, 2048, 2048, 1024, 5528, 384, 2048, 2048, 2048, 1024, 359, 384, 4096],
  5652⟩
theorem pRoster94_valid : cRoster94.fastValid pRoster94 = true := by decide
theorem pRoster94_neverHalts (m : Machine) (hm : compatible pRoster94 m) : NeverHalts m :=
  cRoster94.sound pRoster94 (cRoster94.fastValid_sound _ pRoster94_valid) m hm
#print axioms pRoster94_neverHalts


/- Roster line 95; parent 128 / tree128; path F/0=0RF → A/1=0RD; DFA 5 original; CI run 45525504552. Table: 1RB0RD_1RC1LF_0RD1RF_1LD1RE_---0LB_0RF0LA. -/
def pRoster95 : PartialMachine := fromCodes [7, 13, 11, 22, 13, 23, 14, 19, 24, 4, 21, 0]
def cRoster95 : Data 5 := ⟨0,[0, 1, 2, 3, 2, 2, 4, 0, 2, 2],
  [128, 256, 8, 1755041148, 1745354832, 32, 524544, 1048576, 49152, 1755041148, 1744830464, 671219776, 281094176, 16384, 536903680, 1755041148, 1207959552, 131072, 8194, 4, 134217728, 32, 1753892944, 536870912, 8194, 16422, 235176458, 1048576, 1074855940, 537001984, 1073741824],
  [13700376, 2023476604, 2048, 1024, 1755041148, 1048576, 1082229008, 32, 142672896, 4194304, 1755041148, 1755041148, 32768, 1755041662, 142802960, 66560, 1755041148, 1755041148, 134217728, 1755041148, 32, 65552, 32, 1755041148, 134250624, 1074946322, 131104, 65552, 127741372, 1073758464, 1073741824],
  1466826622⟩
theorem pRoster95_valid : cRoster95.fastValid pRoster95 = true := by decide
theorem pRoster95_neverHalts (m : Machine) (hm : compatible pRoster95 m) : NeverHalts m :=
  cRoster95.sound pRoster95 (cRoster95.fastValid_sound _ pRoster95_valid) m hm
#print axioms pRoster95_neverHalts


end BB6.Agent7FAR.DepthEightSMTBatch
