import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M088
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def t0_14 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,6⟩ (.node .empty ⟨0,false,0,10⟩ .empty)) ⟨0,false,0,28⟩ (.node (.node .empty ⟨0,false,4,1⟩ .empty) ⟨0,false,4,14⟩ (.node .empty ⟨0,false,4,31⟩ .empty))) ⟨0,false,6,0⟩ (.node (.node (.node .empty ⟨0,false,6,12⟩ .empty) ⟨0,false,6,21⟩ (.node .empty ⟨0,false,6,29⟩ .empty)) ⟨0,false,6,30⟩ (.node (.node .empty ⟨0,false,6,33⟩ .empty) ⟨0,true,0,4⟩ .empty)))
def t15_28 : Tree := (.node (.node (.node (.node .empty ⟨0,true,0,13⟩ .empty) ⟨0,true,0,17⟩ (.node .empty ⟨0,true,0,24⟩ .empty)) ⟨0,true,0,30⟩ (.node (.node .empty ⟨0,true,1,12⟩ .empty) ⟨0,true,1,29⟩ .empty)) ⟨0,true,2,10⟩ (.node (.node (.node .empty ⟨0,true,2,11⟩ .empty) ⟨0,true,2,28⟩ (.node .empty ⟨0,true,4,5⟩ .empty)) ⟨0,true,4,8⟩ (.node (.node .empty ⟨0,true,4,24⟩ .empty) ⟨0,true,4,27⟩ .empty)))
def t0_28 : Tree := .node t0_14 ⟨0,true,0,8⟩ t15_28
def t29_42 : Tree := (.node (.node (.node (.node .empty ⟨0,true,7,0⟩ .empty) ⟨0,true,7,10⟩ (.node .empty ⟨0,true,7,11⟩ .empty)) ⟨0,true,7,19⟩ (.node (.node .empty ⟨0,true,7,23⟩ .empty) ⟨0,true,7,28⟩ .empty)) ⟨0,true,7,29⟩ (.node (.node (.node .empty ⟨0,true,7,33⟩ .empty) ⟨0,true,7,39⟩ (.node .empty ⟨1,false,1,0⟩ .empty)) ⟨1,false,1,4⟩ (.node (.node .empty ⟨1,false,1,8⟩ .empty) ⟨1,false,1,13⟩ .empty)))
def t43_56 : Tree := (.node (.node (.node (.node .empty ⟨1,false,1,24⟩ .empty) ⟨1,false,1,30⟩ (.node .empty ⟨1,false,9,0⟩ .empty)) ⟨1,false,9,10⟩ (.node (.node .empty ⟨1,false,9,11⟩ .empty) ⟨1,false,9,19⟩ .empty)) ⟨1,false,9,23⟩ (.node (.node (.node .empty ⟨1,false,9,28⟩ .empty) ⟨1,false,9,29⟩ (.node .empty ⟨1,false,9,33⟩ .empty)) ⟨1,false,9,39⟩ (.node (.node .empty ⟨1,true,5,0⟩ .empty) ⟨1,true,5,10⟩ .empty)))
def t29_56 : Tree := .node t29_42 ⟨1,false,1,17⟩ t43_56
def t0_56 : Tree := .node t0_28 ⟨0,true,4,32⟩ t29_56
def t57_70 : Tree := (.node (.node (.node (.node .empty ⟨1,true,5,28⟩ .empty) ⟨1,true,5,39⟩ (.node .empty ⟨2,false,2,0⟩ .empty)) ⟨2,false,2,12⟩ (.node (.node .empty ⟨2,false,2,29⟩ .empty) ⟨2,false,6,0⟩ .empty)) ⟨2,false,6,2⟩ (.node (.node (.node .empty ⟨2,false,6,3⟩ .empty) ⟨2,false,6,5⟩ (.node .empty ⟨2,false,6,8⟩ .empty)) ⟨2,false,6,23⟩ (.node (.node .empty ⟨2,false,6,24⟩ .empty) ⟨2,false,6,27⟩ .empty)))
def t71_84 : Tree := (.node (.node (.node (.node .empty ⟨2,false,6,32⟩ .empty) ⟨2,false,6,34⟩ (.node .empty ⟨2,false,6,35⟩ .empty)) ⟨2,false,6,38⟩ (.node (.node .empty ⟨2,false,6,39⟩ .empty) ⟨2,true,2,3⟩ .empty)) ⟨2,true,2,7⟩ (.node (.node (.node .empty ⟨2,true,2,9⟩ .empty) ⟨2,true,2,16⟩ (.node .empty ⟨2,true,2,26⟩ .empty)) ⟨3,false,2,1⟩ (.node (.node .empty ⟨3,false,2,14⟩ .empty) ⟨3,false,2,31⟩ .empty)))
def t57_84 : Tree := .node t57_70 ⟨2,false,6,28⟩ t71_84
def t85_98 : Tree := (.node (.node (.node (.node .empty ⟨3,false,3,10⟩ .empty) ⟨3,false,3,11⟩ (.node .empty ⟨3,false,3,28⟩ .empty)) ⟨3,false,6,1⟩ (.node (.node .empty ⟨3,false,6,2⟩ .empty) ⟨3,false,6,22⟩ .empty)) ⟨3,false,6,24⟩ (.node (.node (.node .empty ⟨3,false,6,26⟩ .empty) ⟨3,false,6,34⟩ (.node .empty ⟨3,false,6,37⟩ .empty)) ⟨3,false,6,38⟩ (.node (.node .empty ⟨3,false,7,0⟩ .empty) ⟨3,false,7,1⟩ .empty)))
def t99_112 : Tree := (.node (.node (.node (.node .empty ⟨3,false,7,9⟩ .empty) ⟨3,false,7,22⟩ (.node .empty ⟨3,false,7,24⟩ .empty)) ⟨3,false,7,26⟩ (.node (.node .empty ⟨3,false,7,34⟩ .empty) ⟨3,false,7,37⟩ .empty)) ⟨3,false,7,38⟩ (.node (.node (.node .empty ⟨3,true,1,2⟩ .empty) ⟨3,true,1,15⟩ (.node .empty ⟨3,true,1,32⟩ .empty)) ⟨3,true,5,2⟩ (.node (.node .empty ⟨3,true,5,22⟩ .empty) ⟨3,true,5,24⟩ .empty)))
def t85_112 : Tree := .node t85_98 ⟨3,false,7,2⟩ t99_112
def t57_112 : Tree := .node t57_84 ⟨3,false,3,0⟩ t85_112
def t0_112 : Tree := .node t0_56 ⟨1,true,5,11⟩ t57_112
def t113_127 : Tree := (.node (.node (.node (.node .empty ⟨3,true,5,34⟩ .empty) ⟨3,true,5,37⟩ (.node .empty ⟨3,true,5,38⟩ .empty)) ⟨3,true,7,1⟩ (.node (.node .empty ⟨3,true,7,4⟩ .empty) ⟨3,true,7,7⟩ (.node .empty ⟨3,true,7,9⟩ .empty))) ⟨3,true,7,22⟩ (.node (.node (.node .empty ⟨3,true,7,25⟩ .empty) ⟨3,true,7,26⟩ (.node .empty ⟨3,true,7,31⟩ .empty)) ⟨3,true,7,36⟩ (.node (.node .empty ⟨3,true,7,37⟩ .empty) ⟨3,true,9,2⟩ .empty)))
def t128_141 : Tree := (.node (.node (.node (.node .empty ⟨3,true,9,24⟩ .empty) ⟨3,true,9,26⟩ (.node .empty ⟨3,true,9,34⟩ .empty)) ⟨3,true,9,37⟩ (.node (.node .empty ⟨3,true,9,38⟩ .empty) ⟨4,true,2,1⟩ .empty)) ⟨4,true,2,14⟩ (.node (.node (.node .empty ⟨4,true,2,31⟩ .empty) ⟨4,true,6,1⟩ (.node .empty ⟨4,true,6,2⟩ .empty)) ⟨4,true,6,9⟩ (.node (.node .empty ⟨4,true,6,22⟩ .empty) ⟨4,true,6,24⟩ .empty)))
def t113_141 : Tree := .node t113_127 ⟨3,true,9,22⟩ t128_141
def t142_155 : Tree := (.node (.node (.node (.node .empty ⟨4,true,6,34⟩ .empty) ⟨4,true,6,37⟩ (.node .empty ⟨4,true,6,38⟩ .empty)) ⟨4,true,8,0⟩ (.node (.node .empty ⟨4,true,8,2⟩ .empty) ⟨4,true,8,3⟩ .empty)) ⟨4,true,8,5⟩ (.node (.node (.node .empty ⟨4,true,8,8⟩ .empty) ⟨4,true,8,23⟩ (.node .empty ⟨4,true,8,24⟩ .empty)) ⟨4,true,8,27⟩ (.node (.node .empty ⟨4,true,8,28⟩ .empty) ⟨4,true,8,32⟩ .empty)))
def t156_169 : Tree := (.node (.node (.node (.node .empty ⟨4,true,8,35⟩ .empty) ⟨4,true,8,38⟩ (.node .empty ⟨4,true,8,39⟩ .empty)) ⟨5,false,0,5⟩ (.node (.node .empty ⟨5,false,0,9⟩ .empty) ⟨5,false,0,18⟩ .empty)) ⟨5,false,0,26⟩ (.node (.node (.node .empty ⟨5,false,6,1⟩ .empty) ⟨5,false,6,14⟩ (.node .empty ⟨5,false,6,20⟩ .empty)) ⟨5,false,6,25⟩ (.node (.node .empty ⟨5,false,6,31⟩ .empty) ⟨5,true,0,4⟩ .empty)))
def t142_169 : Tree := .node t142_155 ⟨4,true,8,34⟩ t156_169
def t113_169 : Tree := .node t113_141 ⟨4,true,6,26⟩ t142_169
def t170_183 : Tree := (.node (.node (.node (.node .empty ⟨5,true,0,17⟩ .empty) ⟨5,true,0,24⟩ (.node .empty ⟨5,true,1,3⟩ .empty)) ⟨5,true,1,7⟩ (.node (.node .empty ⟨5,true,1,9⟩ .empty) ⟨5,true,1,16⟩ .empty)) ⟨5,true,1,26⟩ (.node (.node (.node .empty ⟨5,true,2,5⟩ .empty) ⟨5,true,2,8⟩ (.node .empty ⟨5,true,2,24⟩ .empty)) ⟨5,true,2,27⟩ (.node (.node .empty ⟨5,true,2,32⟩ .empty) ⟨5,true,4,4⟩ .empty)))
def t184_197 : Tree := (.node (.node (.node (.node .empty ⟨5,true,4,9⟩ .empty) ⟨5,true,4,25⟩ (.node .empty ⟨5,true,4,26⟩ .empty)) ⟨5,true,4,31⟩ (.node (.node .empty ⟨5,true,4,36⟩ .empty) ⟨5,true,5,3⟩ .empty)) ⟨5,true,5,5⟩ (.node (.node (.node .empty ⟨5,true,5,8⟩ .empty) ⟨5,true,5,23⟩ (.node .empty ⟨5,true,5,24⟩ .empty)) ⟨5,true,5,27⟩ (.node (.node .empty ⟨5,true,5,28⟩ .empty) ⟨5,true,5,32⟩ .empty)))
def t170_197 : Tree := .node t170_183 ⟨5,true,4,7⟩ t184_197
def t198_211 : Tree := (.node (.node (.node (.node .empty ⟨5,true,5,39⟩ .empty) ⟨5,true,6,4⟩ (.node .empty ⟨5,true,6,7⟩ .empty)) ⟨5,true,6,9⟩ (.node (.node .empty ⟨5,true,6,25⟩ .empty) ⟨5,true,6,26⟩ .empty)) ⟨5,true,6,31⟩ (.node (.node (.node .empty ⟨5,true,6,36⟩ .empty) ⟨5,true,7,0⟩ (.node .empty ⟨5,true,7,10⟩ .empty)) ⟨5,true,7,11⟩ (.node (.node .empty ⟨5,true,7,19⟩ .empty) ⟨5,true,7,23⟩ .empty)))
def t212_225 : Tree := (.node (.node (.node (.node .empty ⟨5,true,7,29⟩ .empty) ⟨5,true,7,33⟩ (.node .empty ⟨5,true,7,39⟩ .empty)) ⟨5,true,9,3⟩ (.node (.node .empty ⟨5,true,9,5⟩ .empty) ⟨5,true,9,8⟩ .empty)) ⟨5,true,9,23⟩ (.node (.node (.node .empty ⟨5,true,9,24⟩ .empty) ⟨5,true,9,27⟩ (.node .empty ⟨5,true,9,28⟩ .empty)) ⟨5,true,9,32⟩ (.node (.node .empty ⟨5,true,9,35⟩ .empty) ⟨5,true,9,39⟩ .empty)))
def t198_225 : Tree := .node t198_211 ⟨5,true,7,28⟩ t212_225
def t170_225 : Tree := .node t170_197 ⟨5,true,5,35⟩ t198_225
def t113_225 : Tree := .node t113_169 ⟨5,true,0,8⟩ t170_225
def t0_225 : Tree := .node t0_112 ⟨3,true,5,26⟩ t113_225
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 4, 0, 0, 0, 5, 0, 6, 7, 9, 0, 8, 0, 0, 0, 6],#[0, 1, 3, 2, 23, 22, 19, 4, 6, 5, 11, 7, 0, 0, 0, 8, 10, 9, 35, 24, 12, 14, 12, 14, 13, 0, 6, 0, 16, 15, 0, 0, 0, 17, 6, 18, 0, 0, 21, 20, 0, 0, 0, 0, 35, 34, 33, 25, 28, 26, 0, 27, 35, 24, 11, 7, 29, 31, 30, 20, 6, 0, 16, 32, 11, 7, 21, 20, 23, 37, 19, 36, 0, 27, 35, 38, 39, 37, 33, 31],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(true,2)],[(true,4)],[(true,5),(true,9)],[(false,6)],[(true,7)],[(true,6)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3)],[(true,4)],[(false,4),(false,13),(false,17),(false,30)],[(true,5),(true,27),(true,32)],[(true,7)],[(true,8)],[(false,8)],[(false,5),(false,27),(false,32)],[(false,10),(false,11)],[(false,12)],[(true,10),(true,11)],[(true,14)],[(false,14),(false,31)],[(true,16)],[(true,17)],[(false,3),(false,35)],[(true,19),(true,29),(true,33)],[(false,19),(false,33)],[(true,2)],[(false,2),(false,34)],[(true,9),(true,26)],[(true,23)],[(true,24)],[(true,25),(true,36)],[(false,24)],[(false,28)],[(false,29)],[(true,28),(true,39)],[(true,31)],[(false,23),(false,39)],[(true,22)],[(false,9),(false,22),(false,26),(false,37)],[(true,35)],[(true,34),(true,38)],[(true,37)],[(false,38)]],
  t0_225⟩
theorem check0_14 : t0_14.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check15_28 : t15_28.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node14 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,0,8⟩ = true := by decide
theorem check0_28 : t0_28.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node14 check0_14 check15_28
theorem check29_42 : t29_42.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check43_56 : t43_56.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node42 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,1,17⟩ = true := by decide
theorem check29_56 : t29_56.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node42 check29_42 check43_56
theorem node28 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,4,32⟩ = true := by decide
theorem check0_56 : t0_56.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node28 check0_28 check29_56
theorem check57_70 : t57_70.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check71_84 : t71_84.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node70 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,6,28⟩ = true := by decide
theorem check57_84 : t57_84.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node70 check57_70 check71_84
theorem check85_98 : t85_98.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check99_112 : t99_112.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node98 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,7,2⟩ = true := by decide
theorem check85_112 : t85_112.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node98 check85_98 check99_112
theorem node84 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,3,0⟩ = true := by decide
theorem check57_112 : t57_112.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node84 check57_84 check85_112
theorem node56 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,5,11⟩ = true := by decide
theorem check0_112 : t0_112.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node56 check0_56 check57_112
theorem check113_127 : t113_127.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check128_141 : t128_141.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node127 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,9,22⟩ = true := by decide
theorem check113_141 : t113_141.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node127 check113_127 check128_141
theorem check142_155 : t142_155.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check156_169 : t156_169.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node155 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,8,34⟩ = true := by decide
theorem check142_169 : t142_169.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node155 check142_155 check156_169
theorem node141 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,6,26⟩ = true := by decide
theorem check113_169 : t113_169.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node141 check113_141 check142_169
theorem check170_183 : t170_183.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check184_197 : t184_197.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node183 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,4,7⟩ = true := by decide
theorem check170_197 : t170_197.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node183 check170_183 check184_197
theorem check198_211 : t198_211.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check212_225 : t212_225.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node211 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,7,28⟩ = true := by decide
theorem check198_225 : t198_225.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node211 check198_211 check212_225
theorem node197 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,5,35⟩ = true := by decide
theorem check170_225 : t170_225.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node197 check170_197 check198_225
theorem node169 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,0,8⟩ = true := by decide
theorem check113_225 : t113_225.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node169 check113_169 check170_225
theorem node112 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,5,26⟩ = true := by decide
theorem check0_225 : t0_225.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node112 check0_112 check113_225
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_225
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M088
