import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M033
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_12 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,6⟩ (.node .empty ⟨0,false,0,11⟩ .empty)) ⟨0,false,0,19⟩ (.node (.node .empty ⟨0,false,0,24⟩ .empty) ⟨0,false,2,11⟩ .empty)) ⟨0,false,2,12⟩ (.node (.node (.node .empty ⟨0,false,2,15⟩ .empty) ⟨0,false,2,24⟩ .empty) ⟨0,false,7,0⟩ (.node (.node .empty ⟨0,false,7,11⟩ .empty) ⟨0,false,7,12⟩ .empty)))
def t13_25 : Tree := (.node (.node (.node (.node .empty ⟨0,false,7,24⟩ .empty) ⟨0,true,0,4⟩ (.node .empty ⟨0,true,0,10⟩ .empty)) ⟨0,true,0,23⟩ (.node (.node .empty ⟨0,true,1,6⟩ .empty) ⟨0,true,1,17⟩ .empty)) ⟨0,true,1,19⟩ (.node (.node (.node .empty ⟨0,true,2,4⟩ .empty) ⟨0,true,2,10⟩ .empty) ⟨0,true,2,15⟩ (.node (.node .empty ⟨0,true,2,20⟩ .empty) ⟨0,true,2,23⟩ .empty)))
def t0_25 : Tree := .node t0_12 ⟨0,false,7,15⟩ t13_25
def t26_38 : Tree := (.node (.node (.node (.node .empty ⟨0,true,6,6⟩ .empty) ⟨0,true,6,17⟩ (.node .empty ⟨0,true,6,19⟩ .empty)) ⟨0,true,7,4⟩ (.node (.node .empty ⟨0,true,7,10⟩ .empty) ⟨0,true,7,15⟩ .empty)) ⟨0,true,7,20⟩ (.node (.node (.node .empty ⟨0,true,7,23⟩ .empty) ⟨0,true,7,24⟩ .empty) ⟨1,false,0,7⟩ (.node (.node .empty ⟨1,false,0,20⟩ .empty) ⟨1,false,1,0⟩ .empty)))
def t39_50 : Tree := (.node (.node (.node (.node .empty ⟨1,false,1,9⟩ .empty) ⟨1,false,1,10⟩ .empty) ⟨1,false,1,13⟩ (.node (.node .empty ⟨1,false,1,22⟩ .empty) ⟨1,false,1,23⟩ .empty)) ⟨1,false,6,0⟩ (.node (.node (.node .empty ⟨1,false,6,4⟩ .empty) ⟨1,false,6,10⟩ .empty) ⟨1,false,6,14⟩ (.node (.node .empty ⟨1,false,6,15⟩ .empty) ⟨1,false,6,20⟩ .empty)))
def t26_50 : Tree := .node t26_38 ⟨1,false,1,5⟩ t39_50
def t0_50 : Tree := .node t0_25 ⟨0,true,2,24⟩ t26_50
def t51_63 : Tree := (.node (.node (.node (.node .empty ⟨1,false,6,24⟩ .empty) ⟨1,true,0,6⟩ (.node .empty ⟨1,true,0,19⟩ .empty)) ⟨1,true,1,5⟩ (.node (.node .empty ⟨1,true,1,9⟩ .empty) ⟨1,true,1,13⟩ .empty)) ⟨1,true,1,22⟩ (.node (.node (.node .empty ⟨2,false,1,6⟩ .empty) ⟨2,false,1,19⟩ .empty) ⟨2,false,2,0⟩ (.node (.node .empty ⟨2,false,2,8⟩ .empty) ⟨2,false,2,18⟩ .empty)))
def t64_76 : Tree := (.node (.node (.node (.node .empty ⟨2,false,7,0⟩ .empty) ⟨2,false,7,2⟩ (.node .empty ⟨2,false,7,3⟩ .empty)) ⟨2,false,7,8⟩ (.node (.node .empty ⟨2,false,7,14⟩ .empty) ⟨2,false,7,18⟩ .empty)) ⟨2,false,7,19⟩ (.node (.node (.node .empty ⟨2,false,7,21⟩ .empty) ⟨2,false,7,23⟩ .empty) ⟨2,true,2,2⟩ (.node (.node .empty ⟨2,true,2,3⟩ .empty) ⟨2,true,2,8⟩ .empty)))
def t51_76 : Tree := .node t51_63 ⟨2,false,2,21⟩ t64_76
def t77_89 : Tree := (.node (.node (.node (.node .empty ⟨2,true,2,21⟩ .empty) ⟨3,false,1,8⟩ (.node .empty ⟨3,false,1,21⟩ .empty)) ⟨3,false,2,1⟩ (.node (.node .empty ⟨3,false,3,0⟩ .empty) ⟨3,false,4,5⟩ .empty)) ⟨3,false,4,9⟩ (.node (.node (.node .empty ⟨3,false,4,13⟩ .empty) ⟨3,false,4,22⟩ .empty) ⟨3,false,7,1⟩ (.node (.node .empty ⟨3,false,7,2⟩ .empty) ⟨3,false,7,13⟩ .empty)))
def t90_101 : Tree := (.node (.node (.node (.node .empty ⟨3,false,7,22⟩ .empty) ⟨3,false,8,0⟩ .empty) ⟨3,false,8,1⟩ (.node (.node .empty ⟨3,false,8,2⟩ .empty) ⟨3,false,8,9⟩ .empty)) ⟨3,false,8,13⟩ (.node (.node (.node .empty ⟨3,false,8,21⟩ .empty) ⟨3,false,8,22⟩ .empty) ⟨3,true,0,9⟩ (.node (.node .empty ⟨3,true,0,22⟩ .empty) ⟨3,true,1,2⟩ .empty)))
def t77_101 : Tree := .node t77_89 ⟨3,false,7,21⟩ t90_101
def t51_101 : Tree := .node t51_76 ⟨2,true,2,18⟩ t77_101
def t0_101 : Tree := .node t0_50 ⟨1,false,6,23⟩ t51_101
def t102_114 : Tree := (.node (.node (.node (.node .empty ⟨3,true,3,9⟩ .empty) ⟨3,true,3,13⟩ (.node .empty ⟨3,true,3,16⟩ .empty)) ⟨3,true,3,22⟩ (.node (.node .empty ⟨3,true,6,2⟩ .empty) ⟨3,true,6,13⟩ .empty)) ⟨3,true,6,21⟩ (.node (.node (.node .empty ⟨3,true,6,22⟩ .empty) ⟨3,true,8,1⟩ .empty) ⟨3,true,8,5⟩ (.node (.node .empty ⟨3,true,8,9⟩ .empty) ⟨3,true,8,13⟩ .empty)))
def t115_127 : Tree := (.node (.node (.node (.node .empty ⟨3,true,8,22⟩ .empty) ⟨4,true,1,8⟩ (.node .empty ⟨4,true,1,18⟩ .empty)) ⟨4,true,1,21⟩ (.node (.node .empty ⟨4,true,2,1⟩ .empty) ⟨4,true,5,2⟩ .empty)) ⟨4,true,5,3⟩ (.node (.node (.node .empty ⟨4,true,5,8⟩ .empty) ⟨4,true,5,14⟩ .empty) ⟨4,true,5,18⟩ (.node (.node .empty ⟨4,true,5,19⟩ .empty) ⟨4,true,5,21⟩ .empty)))
def t102_127 : Tree := .node t102_114 ⟨3,true,8,16⟩ t115_127
def t128_140 : Tree := (.node (.node (.node (.node .empty ⟨4,true,7,1⟩ .empty) ⟨4,true,7,2⟩ (.node .empty ⟨4,true,7,9⟩ .empty)) ⟨4,true,7,13⟩ (.node (.node .empty ⟨4,true,7,21⟩ .empty) ⟨4,true,7,22⟩ .empty)) ⟨4,true,9,0⟩ (.node (.node (.node .empty ⟨4,true,9,2⟩ .empty) ⟨4,true,9,3⟩ .empty) ⟨4,true,9,8⟩ (.node (.node .empty ⟨4,true,9,14⟩ .empty) ⟨4,true,9,18⟩ .empty)))
def t141_152 : Tree := (.node (.node (.node (.node .empty ⟨4,true,9,21⟩ .empty) ⟨4,true,9,23⟩ .empty) ⟨5,false,1,3⟩ (.node (.node .empty ⟨5,false,1,8⟩ .empty) ⟨5,false,1,18⟩ .empty)) ⟨5,false,1,21⟩ (.node (.node (.node .empty ⟨5,false,2,5⟩ .empty) ⟨5,false,2,9⟩ .empty) ⟨5,false,2,13⟩ (.node (.node .empty ⟨5,false,2,16⟩ .empty) ⟨5,false,2,22⟩ .empty)))
def t128_152 : Tree := .node t128_140 ⟨4,true,9,19⟩ t141_152
def t102_152 : Tree := .node t102_127 ⟨4,true,5,23⟩ t128_152
def t153_165 : Tree := (.node (.node (.node (.node .empty ⟨5,false,6,8⟩ .empty) ⟨5,false,6,14⟩ (.node .empty ⟨5,false,6,18⟩ .empty)) ⟨5,false,6,19⟩ (.node (.node .empty ⟨5,false,6,21⟩ .empty) ⟨5,false,6,23⟩ .empty)) ⟨5,false,7,5⟩ (.node (.node (.node .empty ⟨5,false,7,9⟩ .empty) ⟨5,false,7,13⟩ .empty) ⟨5,false,7,16⟩ (.node (.node .empty ⟨5,false,7,22⟩ .empty) ⟨5,true,0,5⟩ .empty)))
def t166_178 : Tree := (.node (.node (.node (.node .empty ⟨5,true,0,10⟩ .empty) ⟨5,true,0,22⟩ (.node .empty ⟨5,true,0,23⟩ .empty)) ⟨5,true,1,3⟩ (.node (.node .empty ⟨5,true,1,8⟩ .empty) ⟨5,true,1,18⟩ .empty)) ⟨5,true,1,21⟩ (.node (.node (.node .empty ⟨5,true,2,5⟩ .empty) ⟨5,true,2,9⟩ .empty) ⟨5,true,2,16⟩ (.node (.node .empty ⟨5,true,2,22⟩ .empty) ⟨5,true,3,4⟩ .empty)))
def t153_178 : Tree := .node t153_165 ⟨5,true,0,9⟩ t166_178
def t179_191 : Tree := (.node (.node (.node (.node .empty ⟨5,true,3,14⟩ .empty) ⟨5,true,3,15⟩ (.node .empty ⟨5,true,3,20⟩ .empty)) ⟨5,true,3,23⟩ (.node (.node .empty ⟨5,true,3,24⟩ .empty) ⟨5,true,6,3⟩ .empty)) ⟨5,true,6,8⟩ (.node (.node (.node .empty ⟨5,true,6,14⟩ .empty) ⟨5,true,6,18⟩ .empty) ⟨5,true,6,19⟩ (.node (.node .empty ⟨5,true,6,21⟩ .empty) ⟨5,true,6,23⟩ .empty)))
def t192_203 : Tree := (.node (.node (.node (.node .empty ⟨5,true,7,9⟩ .empty) ⟨5,true,7,16⟩ .empty) ⟨5,true,7,22⟩ (.node (.node .empty ⟨5,true,8,0⟩ .empty) ⟨5,true,8,4⟩ .empty)) ⟨5,true,8,10⟩ (.node (.node (.node .empty ⟨5,true,8,14⟩ .empty) ⟨5,true,8,15⟩ .empty) ⟨5,true,8,20⟩ (.node (.node .empty ⟨5,true,8,23⟩ .empty) ⟨5,true,8,24⟩ .empty)))
def t179_203 : Tree := .node t179_191 ⟨5,true,7,5⟩ t192_203
def t153_203 : Tree := .node t153_178 ⟨5,true,3,10⟩ t179_203
def t102_203 : Tree := .node t102_152 ⟨5,false,6,3⟩ t153_203
def t0_203 : Tree := .node t0_101 ⟨3,true,3,5⟩ t102_203
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 6, 0, 5, 0, 0, 0, 0, 0, 7, 8, 6, 0, 9, 0, 0],#[0, 1, 3, 2, 14, 13, 4, 5, 12, 0, 6, 8, 7, 0, 0, 0, 10, 9, 19, 21, 11, 0, 0, 0, 0, 0, 19, 21, 15, 16, 12, 0, 17, 18, 0, 0, 10, 9, 20, 16, 12, 0, 23, 22, 19, 21, 24, 16, 12, 0],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,3)],[(true,2),(true,7)],[(true,6)],[(false,7)],[(true,8)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(true,3)],[(false,5)],[(false,6)],[(true,5)],[(true,8),(true,18)],[(false,8),(false,18)],[(false,10)],[(false,4),(false,15),(false,20),(false,24)],[(true,2)],[(false,2)],[(false,14)],[(true,14),(true,19),(true,23)],[(false,16)],[(true,16)],[(false,9),(false,13),(false,22)],[(false,19)],[(true,9),(true,13),(true,22)],[(true,21)],[(false,21)],[(false,23)]],
  t0_203⟩
theorem check0_12 : t0_12.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check13_25 : t13_25.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node12 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,7,15⟩ = true := by decide
theorem check0_25 : t0_25.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node12 check0_12 check13_25
theorem check26_38 : t26_38.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check39_50 : t39_50.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node38 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,1,5⟩ = true := by decide
theorem check26_50 : t26_50.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node38 check26_38 check39_50
theorem node25 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,2,24⟩ = true := by decide
theorem check0_50 : t0_50.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node25 check0_25 check26_50
theorem check51_63 : t51_63.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check64_76 : t64_76.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node63 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,2,21⟩ = true := by decide
theorem check51_76 : t51_76.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node63 check51_63 check64_76
theorem check77_89 : t77_89.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check90_101 : t90_101.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node89 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,7,21⟩ = true := by decide
theorem check77_101 : t77_101.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node89 check77_89 check90_101
theorem node76 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,2,18⟩ = true := by decide
theorem check51_101 : t51_101.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node76 check51_76 check77_101
theorem node50 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,6,23⟩ = true := by decide
theorem check0_101 : t0_101.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node50 check0_50 check51_101
theorem check102_114 : t102_114.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check115_127 : t115_127.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node114 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,8,16⟩ = true := by decide
theorem check102_127 : t102_127.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node114 check102_114 check115_127
theorem check128_140 : t128_140.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check141_152 : t141_152.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node140 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,9,19⟩ = true := by decide
theorem check128_152 : t128_152.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node140 check128_140 check141_152
theorem node127 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,5,23⟩ = true := by decide
theorem check102_152 : t102_152.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node127 check102_127 check128_152
theorem check153_165 : t153_165.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check166_178 : t166_178.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node165 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,0,9⟩ = true := by decide
theorem check153_178 : t153_178.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node165 check153_165 check166_178
theorem check179_191 : t179_191.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check192_203 : t192_203.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node191 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,7,5⟩ = true := by decide
theorem check179_203 : t179_203.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node191 check179_191 check192_203
theorem node178 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,3,10⟩ = true := by decide
theorem check153_203 : t153_203.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node178 check153_178 check179_203
theorem node152 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,6,3⟩ = true := by decide
theorem check102_203 : t102_203.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node152 check102_152 check153_203
theorem node101 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,3,5⟩ = true := by decide
theorem check0_203 : t0_203.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node101 check0_101 check102_203
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_203
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M033
