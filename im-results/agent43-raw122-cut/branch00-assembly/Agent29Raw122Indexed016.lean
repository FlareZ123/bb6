import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M016
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_9 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,1,4⟩ .empty) ⟨0,false,1,14⟩ (.node .empty ⟨0,false,1,19⟩ .empty)) ⟨0,false,1,29⟩ (.node (.node (.node .empty ⟨0,false,1,38⟩ .empty) ⟨0,false,1,41⟩ .empty) ⟨0,false,4,7⟩ (.node .empty ⟨0,false,4,23⟩ .empty)))
def t10_19 : Tree := (.node (.node (.node (.node .empty ⟨0,false,7,8⟩ .empty) ⟨0,false,7,24⟩ .empty) ⟨0,false,7,32⟩ (.node .empty ⟨0,false,7,42⟩ .empty)) ⟨0,false,7,45⟩ (.node (.node (.node .empty ⟨0,false,9,23⟩ .empty) ⟨0,false,9,30⟩ .empty) ⟨0,true,0,4⟩ (.node .empty ⟨0,true,0,14⟩ .empty)))
def t0_19 : Tree := .node t0_9 ⟨0,false,7,0⟩ t10_19
def t20_29 : Tree := (.node (.node (.node (.node .empty ⟨0,true,1,19⟩ .empty) ⟨0,true,1,29⟩ .empty) ⟨0,true,1,38⟩ (.node .empty ⟨0,true,1,41⟩ .empty)) ⟨0,true,4,11⟩ (.node (.node (.node .empty ⟨0,true,4,26⟩ .empty) ⟨0,true,5,23⟩ .empty) ⟨0,true,5,30⟩ (.node .empty ⟨0,true,7,4⟩ .empty)))
def t30_39 : Tree := (.node (.node (.node (.node .empty ⟨0,true,8,14⟩ .empty) ⟨0,true,8,19⟩ .empty) ⟨0,true,8,29⟩ (.node .empty ⟨0,true,8,38⟩ .empty)) ⟨0,true,8,41⟩ (.node (.node (.node .empty ⟨0,true,9,11⟩ .empty) ⟨0,true,9,26⟩ .empty) ⟨0,true,9,35⟩ (.node .empty ⟨0,true,9,44⟩ .empty)))
def t20_39 : Tree := .node t20_29 ⟨0,true,7,14⟩ t30_39
def t0_39 : Tree := .node t0_19 ⟨0,true,1,14⟩ t20_39
def t40_49 : Tree := (.node (.node (.node (.node .empty ⟨1,false,1,0⟩ .empty) ⟨1,false,2,3⟩ .empty) ⟨1,false,2,13⟩ (.node .empty ⟨1,false,2,18⟩ .empty)) ⟨1,false,2,28⟩ (.node (.node (.node .empty ⟨1,false,2,37⟩ .empty) ⟨1,false,2,40⟩ .empty) ⟨1,false,8,0⟩ (.node .empty ⟨1,false,9,6⟩ .empty)))
def t50_59 : Tree := (.node (.node (.node (.node .empty ⟨1,false,10,21⟩ .empty) ⟨1,false,10,22⟩ .empty) ⟨1,true,8,4⟩ (.node .empty ⟨1,true,8,14⟩ .empty)) ⟨1,true,8,19⟩ (.node (.node (.node .empty ⟨1,true,8,29⟩ .empty) ⟨1,true,8,38⟩ .empty) ⟨1,true,8,41⟩ (.node .empty ⟨2,false,2,0⟩ .empty)))
def t40_59 : Tree := .node t40_49 ⟨1,false,9,22⟩ t50_59
def t60_69 : Tree := (.node (.node (.node (.node .empty ⟨2,false,4,12⟩ .empty) ⟨2,false,4,16⟩ .empty) ⟨2,false,4,27⟩ (.node .empty ⟨2,false,4,36⟩ .empty)) ⟨2,false,4,39⟩ (.node (.node (.node .empty ⟨2,false,10,5⟩ .empty) ⟨2,false,10,15⟩ .empty) ⟨2,false,12,15⟩ (.node .empty ⟨2,false,12,20⟩ .empty)))
def t70_78 : Tree := (.node (.node (.node (.node .empty ⟨3,false,3,0⟩ .empty) ⟨3,false,4,16⟩ .empty) ⟨3,false,4,27⟩ (.node .empty ⟨3,false,4,39⟩ .empty)) ⟨3,false,5,11⟩ (.node (.node .empty ⟨3,false,5,26⟩ .empty) ⟨3,false,5,35⟩ (.node .empty ⟨3,false,5,44⟩ .empty)))
def t60_78 : Tree := .node t60_69 ⟨3,false,2,1⟩ t70_78
def t40_78 : Tree := .node t40_59 ⟨2,false,4,1⟩ t60_78
def t0_78 : Tree := .node t0_39 ⟨0,true,9,47⟩ t40_78
def t79_88 : Tree := (.node (.node (.node (.node .empty ⟨3,false,10,8⟩ .empty) ⟨3,false,10,24⟩ .empty) ⟨3,false,11,4⟩ (.node .empty ⟨3,false,11,14⟩ .empty)) ⟨3,false,12,8⟩ (.node (.node (.node .empty ⟨3,false,12,24⟩ .empty) ⟨3,false,12,32⟩ .empty) ⟨3,false,12,42⟩ (.node .empty ⟨3,false,12,45⟩ .empty)))
def t89_98 : Tree := (.node (.node (.node (.node .empty ⟨3,false,13,19⟩ .empty) ⟨3,false,13,29⟩ .empty) ⟨3,false,13,38⟩ (.node .empty ⟨3,false,13,41⟩ .empty)) ⟨3,true,1,2⟩ (.node (.node (.node .empty ⟨3,true,2,17⟩ .empty) ⟨3,true,5,0⟩ .empty) ⟨3,true,5,11⟩ (.node .empty ⟨3,true,5,26⟩ .empty)))
def t79_98 : Tree := .node t79_88 ⟨3,false,13,14⟩ t89_98
def t99_108 : Tree := (.node (.node (.node (.node .empty ⟨3,true,5,44⟩ .empty) ⟨3,true,5,47⟩ .empty) ⟨3,true,8,2⟩ (.node .empty ⟨3,true,9,9⟩ .empty)) ⟨3,true,10,9⟩ (.node (.node (.node .empty ⟨3,true,10,33⟩ .empty) ⟨4,false,0,5⟩ .empty) ⟨4,false,0,15⟩ (.node .empty ⟨4,false,0,20⟩ .empty)))
def t109_118 : Tree := (.node (.node (.node (.node .empty ⟨4,false,6,0⟩ .empty) ⟨4,false,6,10⟩ .empty) ⟨4,false,6,25⟩ (.node .empty ⟨4,false,6,34⟩ .empty)) ⟨4,false,6,43⟩ (.node (.node (.node .empty ⟨4,false,6,46⟩ .empty) ⟨4,true,0,15⟩ .empty) ⟨4,true,0,20⟩ (.node .empty ⟨4,true,2,1⟩ .empty)))
def t99_118 : Tree := .node t99_108 ⟨4,false,4,31⟩ t109_118
def t79_118 : Tree := .node t79_98 ⟨3,true,5,35⟩ t99_118
def t119_128 : Tree := (.node (.node (.node (.node .empty ⟨4,true,4,12⟩ .empty) ⟨4,true,4,16⟩ .empty) ⟨4,true,4,27⟩ (.node .empty ⟨4,true,4,36⟩ .empty)) ⟨4,true,4,39⟩ (.node (.node (.node .empty ⟨4,true,6,5⟩ .empty) ⟨4,true,6,15⟩ .empty) ⟨4,true,7,15⟩ (.node .empty ⟨4,true,7,20⟩ .empty)))
def t129_138 : Tree := (.node (.node (.node (.node .empty ⟨4,true,10,24⟩ .empty) ⟨4,true,12,8⟩ .empty) ⟨4,true,12,24⟩ (.node .empty ⟨4,true,12,32⟩ .empty)) ⟨4,true,12,42⟩ (.node (.node (.node .empty ⟨4,true,12,45⟩ .empty) ⟨5,false,0,21⟩ .empty) ⟨5,false,0,22⟩ (.node .empty ⟨5,true,1,3⟩ .empty)))
def t119_138 : Tree := .node t119_128 ⟨4,true,10,8⟩ t129_138
def t139_148 : Tree := (.node (.node (.node (.node .empty ⟨5,true,2,13⟩ .empty) ⟨5,true,2,18⟩ .empty) ⟨5,true,2,28⟩ (.node .empty ⟨5,true,2,37⟩ .empty)) ⟨5,true,2,40⟩ (.node (.node (.node .empty ⟨5,true,5,6⟩ .empty) ⟨5,true,5,22⟩ .empty) ⟨5,true,6,21⟩ (.node .empty ⟨5,true,6,22⟩ .empty)))
def t149_157 : Tree := (.node (.node (.node (.node .empty ⟨5,true,8,13⟩ .empty) ⟨5,true,9,10⟩ .empty) ⟨5,true,9,25⟩ (.node .empty ⟨5,true,10,10⟩ .empty)) ⟨5,true,10,25⟩ (.node (.node .empty ⟨5,true,10,34⟩ .empty) ⟨5,true,10,43⟩ (.node .empty ⟨5,true,10,46⟩ .empty)))
def t139_157 : Tree := .node t139_148 ⟨5,true,8,3⟩ t149_157
def t119_157 : Tree := .node t119_138 ⟨5,true,1,13⟩ t139_157
def t79_157 : Tree := .node t79_118 ⟨4,true,2,12⟩ t119_157
def t0_157 : Tree := .node t0_78 ⟨3,false,5,47⟩ t79_157
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 4, 0, 0, 5, 9, 0, 6, 0, 7, 0, 8, 0, 2, 0, 10, 11, 12, 0, 0, 13, 0, 0, 0],#[0, 1, 3, 2, 0, 0, 4, 0, 5, 8, 6, 0, 7, 0, 0, 0, 10, 9, 0, 0, 11, 0, 12, 16, 13, 0, 14, 0, 15, 24, 22, 0, 18, 17, 0, 0, 19, 0, 20, 32, 21, 0, 30, 0, 23, 0, 31, 0, 25, 9, 26, 0, 12, 27, 28, 17, 29, 0, 20, 45, 31, 0, 0, 0, 34, 33, 0, 0, 35, 0, 36, 39, 37, 0, 38, 0, 20, 42, 40, 17, 41, 0, 20, 8, 43, 33, 44, 0, 12, 27, 46, 33, 47, 0, 36, 27],
  #[[(false,0)],[(true,0)],[(true,1),(true,8)],[(false,2)],[(true,2)],[(false,4)],[(true,5)],[(true,6)],[(true,7)],[(true,4)],[(true,9)],[(false,10)],[(true,10)],[(false,12)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(false,4)],[(false,5)],[(false,6)],[(true,4),(true,41)],[(true,8),(true,24)],[(false,8)],[(false,10)],[(false,11),(false,26),(false,44)],[(false,12)],[(false,13)],[(false,14)],[(true,11)],[(true,16),(true,27),(true,39)],[(false,16)],[(false,18)],[(false,19),(false,29),(false,38),(false,41)],[(false,20)],[(false,15)],[(false,22)],[(true,14)],[(false,24)],[(false,25)],[(true,26),(true,44),(true,47)],[(false,27)],[(false,28)],[(false,21)],[(false,23),(false,30)],[(true,19)],[(true,32),(true,42),(true,45)],[(false,32)],[(false,34)],[(false,35),(false,47)],[(false,36)],[(false,37)],[(true,35)],[(false,39)],[(false,40)],[(true,38)],[(false,42)],[(false,43)],[(true,29)],[(false,45)],[(false,46)]],
  t0_157⟩
theorem check0_9 : t0_9.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check10_19 : t10_19.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node9 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,7,0⟩ = true := by decide
theorem check0_19 : t0_19.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node9 check0_9 check10_19
theorem check20_29 : t20_29.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check30_39 : t30_39.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node29 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,7,14⟩ = true := by decide
theorem check20_39 : t20_39.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node29 check20_29 check30_39
theorem node19 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,1,14⟩ = true := by decide
theorem check0_39 : t0_39.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node19 check0_19 check20_39
theorem check40_49 : t40_49.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check50_59 : t50_59.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node49 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,9,22⟩ = true := by decide
theorem check40_59 : t40_59.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node49 check40_49 check50_59
theorem check60_69 : t60_69.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check70_78 : t70_78.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node69 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,2,1⟩ = true := by decide
theorem check60_78 : t60_78.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node69 check60_69 check70_78
theorem node59 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,4,1⟩ = true := by decide
theorem check40_78 : t40_78.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node59 check40_59 check60_78
theorem node39 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,9,47⟩ = true := by decide
theorem check0_78 : t0_78.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node39 check0_39 check40_78
theorem check79_88 : t79_88.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check89_98 : t89_98.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node88 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,13,14⟩ = true := by decide
theorem check79_98 : t79_98.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node88 check79_88 check89_98
theorem check99_108 : t99_108.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check109_118 : t109_118.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node108 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,4,31⟩ = true := by decide
theorem check99_118 : t99_118.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node108 check99_108 check109_118
theorem node98 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,5,35⟩ = true := by decide
theorem check79_118 : t79_118.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node98 check79_98 check99_118
theorem check119_128 : t119_128.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check129_138 : t129_138.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node128 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,10,8⟩ = true := by decide
theorem check119_138 : t119_138.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node128 check119_128 check129_138
theorem check139_148 : t139_148.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check149_157 : t149_157.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node148 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,8,3⟩ = true := by decide
theorem check139_157 : t139_157.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node148 check139_148 check149_157
theorem node138 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,1,13⟩ = true := by decide
theorem check119_157 : t119_157.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node138 check119_138 check139_157
theorem node118 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,2,12⟩ = true := by decide
theorem check79_157 : t79_157.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node118 check79_118 check119_157
theorem node78 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,5,47⟩ = true := by decide
theorem check0_157 : t0_157.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node78 check0_78 check79_157
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_157
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M016
