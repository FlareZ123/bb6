import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M086
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def t0_14 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,6⟩ (.node .empty ⟨0,false,0,12⟩ .empty)) ⟨0,false,2,3⟩ (.node (.node .empty ⟨0,false,2,9⟩ .empty) ⟨0,false,2,11⟩ (.node .empty ⟨0,false,2,20⟩ .empty))) ⟨0,false,5,0⟩ (.node (.node (.node .empty ⟨0,false,5,15⟩ .empty) ⟨0,false,5,32⟩ (.node .empty ⟨0,false,5,43⟩ .empty)) ⟨0,false,7,0⟩ (.node (.node .empty ⟨0,false,7,15⟩ .empty) ⟨0,false,7,25⟩ .empty)))
def t15_28 : Tree := (.node (.node (.node (.node .empty ⟨0,false,7,33⟩ .empty) ⟨0,false,7,35⟩ (.node .empty ⟨0,false,7,43⟩ .empty)) ⟨0,false,7,44⟩ (.node (.node .empty ⟨0,true,0,4⟩ .empty) ⟨0,true,0,10⟩ .empty)) ⟨0,true,0,17⟩ (.node (.node (.node .empty ⟨0,true,0,21⟩ .empty) ⟨0,true,0,27⟩ (.node .empty ⟨0,true,1,16⟩ .empty)) ⟨0,true,1,33⟩ (.node (.node .empty ⟨0,true,2,15⟩ .empty) ⟨0,true,2,32⟩ .empty)))
def t0_28 : Tree := .node t0_14 ⟨0,false,7,32⟩ t15_28
def t29_42 : Tree := (.node (.node (.node (.node .empty ⟨0,true,4,14⟩ .empty) ⟨0,true,4,31⟩ (.node .empty ⟨0,true,5,5⟩ .empty)) ⟨0,true,5,9⟩ (.node (.node .empty ⟨0,true,5,11⟩ .empty) ⟨0,true,5,30⟩ .empty)) ⟨0,true,8,0⟩ (.node (.node (.node .empty ⟨0,true,8,7⟩ .empty) ⟨0,true,8,13⟩ (.node .empty ⟨0,true,8,14⟩ .empty)) ⟨0,true,8,28⟩ (.node (.node .empty ⟨0,true,8,31⟩ .empty) ⟨0,true,8,32⟩ .empty)))
def t43_56 : Tree := (.node (.node (.node (.node .empty ⟨0,true,8,39⟩ .empty) ⟨0,true,8,42⟩ (.node .empty ⟨0,true,8,43⟩ .empty)) ⟨1,false,1,0⟩ (.node (.node .empty ⟨1,false,1,4⟩ .empty) ⟨1,false,1,10⟩ .empty)) ⟨1,false,1,17⟩ (.node (.node (.node .empty ⟨1,false,1,21⟩ .empty) ⟨1,false,1,27⟩ (.node .empty ⟨1,false,4,1⟩ .empty)) ⟨1,false,4,18⟩ (.node (.node .empty ⟨1,false,4,34⟩ .empty) ⟨1,false,6,0⟩ .empty)))
def t29_56 : Tree := .node t29_42 ⟨0,true,8,35⟩ t43_56
def t0_56 : Tree := .node t0_28 ⟨0,true,4,13⟩ t29_56
def t57_70 : Tree := (.node (.node (.node (.node .empty ⟨1,false,6,13⟩ .empty) ⟨1,false,6,14⟩ (.node .empty ⟨1,false,6,28⟩ .empty)) ⟨1,false,6,31⟩ (.node (.node .empty ⟨1,false,6,32⟩ .empty) ⟨1,false,6,35⟩ .empty)) ⟨1,false,6,39⟩ (.node (.node (.node .empty ⟨1,false,6,42⟩ .empty) ⟨1,false,6,43⟩ (.node .empty ⟨1,true,1,7⟩ .empty)) ⟨1,true,1,13⟩ (.node (.node .empty ⟨1,true,1,23⟩ .empty) ⟨1,true,1,31⟩ .empty)))
def t71_84 : Tree := (.node (.node (.node (.node .empty ⟨1,true,4,8⟩ .empty) ⟨1,true,4,10⟩ (.node .empty ⟨1,true,4,16⟩ .empty)) ⟨1,true,4,27⟩ (.node (.node .empty ⟨1,true,4,33⟩ .empty) ⟨1,true,4,44⟩ .empty)) ⟨2,false,2,0⟩ (.node (.node (.node .empty ⟨2,false,2,16⟩ .empty) ⟨2,false,2,33⟩ (.node .empty ⟨2,false,7,0⟩ .empty)) ⟨2,false,7,2⟩ (.node (.node .empty ⟨2,false,7,3⟩ .empty) ⟨2,false,7,5⟩ .empty)))
def t57_84 : Tree := .node t57_70 ⟨1,true,4,0⟩ t71_84
def t85_98 : Tree := (.node (.node (.node (.node .empty ⟨2,false,7,11⟩ .empty) ⟨2,false,7,12⟩ (.node .empty ⟨2,false,7,28⟩ .empty)) ⟨2,false,7,30⟩ (.node (.node .empty ⟨2,false,7,31⟩ .empty) ⟨2,false,7,36⟩ .empty)) ⟨2,false,7,37⟩ (.node (.node (.node .empty ⟨2,false,7,41⟩ .empty) ⟨2,false,7,42⟩ (.node .empty ⟨2,true,2,3⟩ .empty)) ⟨2,true,2,9⟩ (.node (.node .empty ⟨2,true,2,11⟩ .empty) ⟨2,true,2,20⟩ .empty)))
def t99_112 : Tree := (.node (.node (.node (.node .empty ⟨2,true,5,15⟩ .empty) ⟨2,true,5,32⟩ (.node .empty ⟨2,true,5,43⟩ .empty)) ⟨3,false,2,1⟩ (.node (.node .empty ⟨3,false,2,18⟩ .empty) ⟨3,false,2,34⟩ .empty)) ⟨3,false,3,0⟩ (.node (.node (.node .empty ⟨3,false,3,15⟩ .empty) ⟨3,false,3,32⟩ (.node .empty ⟨3,false,7,1⟩ .empty)) ⟨3,false,7,2⟩ (.node (.node .empty ⟨3,false,7,11⟩ .empty) ⟨3,false,7,26⟩ .empty)))
def t85_112 : Tree := .node t85_98 ⟨2,true,5,0⟩ t99_112
def t57_112 : Tree := .node t57_84 ⟨2,false,7,9⟩ t85_112
def t0_112 : Tree := .node t0_56 ⟨1,false,6,7⟩ t57_112
def t113_127 : Tree := (.node (.node (.node (.node .empty ⟨3,false,7,36⟩ .empty) ⟨3,false,7,40⟩ (.node .empty ⟨3,false,7,41⟩ .empty)) ⟨3,false,8,0⟩ (.node (.node .empty ⟨3,false,8,1⟩ .empty) ⟨3,false,8,2⟩ (.node .empty ⟨3,false,8,10⟩ .empty))) ⟨3,false,8,11⟩ (.node (.node (.node .empty ⟨3,false,8,26⟩ .empty) ⟨3,false,8,27⟩ (.node .empty ⟨3,false,8,36⟩ .empty)) ⟨3,false,8,40⟩ (.node (.node .empty ⟨3,false,8,41⟩ .empty) ⟨3,true,1,2⟩ .empty)))
def t128_141 : Tree := (.node (.node (.node (.node .empty ⟨3,true,6,2⟩ .empty) ⟨3,true,6,11⟩ (.node .empty ⟨3,true,6,26⟩ .empty)) ⟨3,true,6,27⟩ (.node (.node .empty ⟨3,true,6,36⟩ .empty) ⟨3,true,6,40⟩ .empty)) ⟨3,true,6,41⟩ (.node (.node (.node .empty ⟨3,true,8,1⟩ .empty) ⟨3,true,8,4⟩ (.node .empty ⟨3,true,8,8⟩ .empty)) ⟨3,true,8,10⟩ (.node (.node .empty ⟨3,true,8,26⟩ .empty) ⟨3,true,8,27⟩ .empty)))
def t113_141 : Tree := .node t113_127 ⟨3,true,1,19⟩ t128_141
def t142_155 : Tree := (.node (.node (.node (.node .empty ⟨3,true,8,38⟩ .empty) ⟨3,true,8,40⟩ (.node .empty ⟨4,true,2,1⟩ .empty)) ⟨4,true,2,18⟩ (.node (.node .empty ⟨4,true,2,34⟩ .empty) ⟨4,true,7,1⟩ .empty)) ⟨4,true,7,2⟩ (.node (.node (.node .empty ⟨4,true,7,10⟩ .empty) ⟨4,true,7,11⟩ (.node .empty ⟨4,true,7,26⟩ .empty)) ⟨4,true,7,27⟩ (.node (.node .empty ⟨4,true,7,36⟩ .empty) ⟨4,true,7,40⟩ .empty)))
def t156_169 : Tree := (.node (.node (.node (.node .empty ⟨4,true,9,0⟩ .empty) ⟨4,true,9,2⟩ (.node .empty ⟨4,true,9,3⟩ .empty)) ⟨4,true,9,5⟩ (.node (.node .empty ⟨4,true,9,9⟩ .empty) ⟨4,true,9,11⟩ .empty)) ⟨4,true,9,12⟩ (.node (.node (.node .empty ⟨4,true,9,28⟩ .empty) ⟨4,true,9,30⟩ (.node .empty ⟨4,true,9,31⟩ .empty)) ⟨4,true,9,36⟩ (.node (.node .empty ⟨4,true,9,37⟩ .empty) ⟨4,true,9,41⟩ .empty)))
def t142_169 : Tree := .node t142_155 ⟨4,true,7,41⟩ t156_169
def t113_169 : Tree := .node t113_141 ⟨3,true,8,29⟩ t142_169
def t170_183 : Tree := (.node (.node (.node (.node .empty ⟨5,false,0,5⟩ .empty) ⟨5,false,0,11⟩ (.node .empty ⟨5,false,0,22⟩ .empty)) ⟨5,false,7,1⟩ (.node (.node .empty ⟨5,false,7,24⟩ .empty) ⟨5,false,7,29⟩ .empty)) ⟨5,false,7,34⟩ (.node (.node (.node .empty ⟨5,true,0,4⟩ .empty) ⟨5,true,0,10⟩ (.node .empty ⟨5,true,0,21⟩ .empty)) ⟨5,true,0,27⟩ (.node (.node .empty ⟨5,true,1,3⟩ .empty) ⟨5,true,1,9⟩ .empty)))
def t184_197 : Tree := (.node (.node (.node (.node .empty ⟨5,true,1,20⟩ .empty) ⟨5,true,2,8⟩ (.node .empty ⟨5,true,2,10⟩ .empty)) ⟨5,true,2,27⟩ (.node (.node .empty ⟨5,true,4,5⟩ .empty) ⟨5,true,4,9⟩ .empty)) ⟨5,true,4,11⟩ (.node (.node (.node .empty ⟨5,true,4,30⟩ .empty) ⟨5,true,5,4⟩ (.node .empty ⟨5,true,5,8⟩ .empty)) ⟨5,true,5,10⟩ (.node (.node .empty ⟨5,true,5,27⟩ .empty) ⟨5,true,5,29⟩ .empty)))
def t170_197 : Tree := .node t170_183 ⟨5,true,1,11⟩ t184_197
def t198_211 : Tree := (.node (.node (.node (.node .empty ⟨5,true,6,3⟩ .empty) ⟨5,true,6,5⟩ (.node .empty ⟨5,true,6,9⟩ .empty)) ⟨5,true,6,11⟩ (.node (.node .empty ⟨5,true,6,12⟩ .empty) ⟨5,true,6,28⟩ .empty)) ⟨5,true,6,30⟩ (.node (.node (.node .empty ⟨5,true,6,31⟩ .empty) ⟨5,true,6,37⟩ (.node .empty ⟨5,true,6,42⟩ .empty)) ⟨5,true,7,4⟩ (.node (.node .empty ⟨5,true,7,8⟩ .empty) ⟨5,true,7,10⟩ .empty)))
def t212_225 : Tree := (.node (.node (.node (.node .empty ⟨5,true,7,29⟩ .empty) ⟨5,true,7,38⟩ (.node .empty ⟨5,true,8,0⟩ .empty)) ⟨5,true,8,7⟩ (.node (.node .empty ⟨5,true,8,13⟩ .empty) ⟨5,true,8,14⟩ .empty)) ⟨5,true,8,28⟩ (.node (.node (.node .empty ⟨5,true,8,31⟩ .empty) ⟨5,true,8,32⟩ (.node .empty ⟨5,true,8,35⟩ .empty)) ⟨5,true,8,39⟩ (.node (.node .empty ⟨5,true,8,42⟩ .empty) ⟨5,true,8,43⟩ .empty)))
def t198_225 : Tree := .node t198_211 ⟨5,true,7,27⟩ t212_225
def t170_225 : Tree := .node t170_197 ⟨5,true,5,38⟩ t198_225
def t113_225 : Tree := .node t113_169 ⟨4,true,9,42⟩ t170_225
def t0_225 : Tree := .node t0_112 ⟨3,false,7,27⟩ t113_225
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 4, 0, 0, 0, 5, 0, 6, 0, 7, 8, 6, 0, 9, 0, 0],#[0, 1, 3, 2, 28, 26, 7, 4, 6, 5, 14, 8, 0, 0, 25, 24, 0, 9, 13, 10, 12, 11, 31, 27, 39, 38, 15, 24, 15, 24, 16, 18, 17, 0, 6, 0, 20, 19, 0, 0, 23, 21, 6, 22, 0, 0, 0, 0, 0, 0, 0, 0, 37, 36, 12, 11, 35, 29, 0, 30, 14, 8, 32, 29, 33, 34, 17, 0, 20, 19, 25, 24, 28, 40, 39, 38, 0, 30, 25, 24, 37, 41, 42, 40, 43, 29, 44, 34, 0, 0],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(true,2)],[(true,4)],[(true,5),(true,7)],[(true,6)],[(false,7)],[(true,8)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3)],[(true,4)],[(false,4),(false,17),(false,21)],[(false,3)],[(true,5),(true,30)],[(true,8)],[(true,9)],[(true,10),(true,27)],[(false,10),(false,27)],[(false,9)],[(false,5),(false,30)],[(false,13),(false,14)],[(false,15)],[(false,16),(false,33)],[(true,15)],[(true,18),(true,34)],[(false,18),(false,34)],[(true,20)],[(true,21)],[(false,20)],[(true,7),(true,13),(true,14),(true,35),(true,39)],[(false,7),(false,35),(false,39)],[(true,2)],[(true,11)],[(false,2),(false,36)],[(true,28),(true,31),(true,42)],[(true,29),(true,38)],[(false,11)],[(false,31)],[(false,32)],[(true,32),(true,43)],[(false,28)],[(true,26)],[(false,26),(false,40)],[(true,12),(true,37)],[(false,12),(false,37)],[(true,36),(true,41)],[(true,40)],[(false,41)],[(false,42)],[(false,43)]],
  t0_225⟩
theorem check0_14 : t0_14.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check15_28 : t15_28.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node14 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,7,32⟩ = true := by decide
theorem check0_28 : t0_28.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node14 check0_14 check15_28
theorem check29_42 : t29_42.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check43_56 : t43_56.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node42 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,8,35⟩ = true := by decide
theorem check29_56 : t29_56.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node42 check29_42 check43_56
theorem node28 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,4,13⟩ = true := by decide
theorem check0_56 : t0_56.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node28 check0_28 check29_56
theorem check57_70 : t57_70.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check71_84 : t71_84.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node70 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,4,0⟩ = true := by decide
theorem check57_84 : t57_84.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node70 check57_70 check71_84
theorem check85_98 : t85_98.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check99_112 : t99_112.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node98 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,5,0⟩ = true := by decide
theorem check85_112 : t85_112.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node98 check85_98 check99_112
theorem node84 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,7,9⟩ = true := by decide
theorem check57_112 : t57_112.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node84 check57_84 check85_112
theorem node56 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,6,7⟩ = true := by decide
theorem check0_112 : t0_112.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node56 check0_56 check57_112
theorem check113_127 : t113_127.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check128_141 : t128_141.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node127 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,1,19⟩ = true := by decide
theorem check113_141 : t113_141.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node127 check113_127 check128_141
theorem check142_155 : t142_155.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check156_169 : t156_169.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node155 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,7,41⟩ = true := by decide
theorem check142_169 : t142_169.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node155 check142_155 check156_169
theorem node141 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,8,29⟩ = true := by decide
theorem check113_169 : t113_169.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node141 check113_141 check142_169
theorem check170_183 : t170_183.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check184_197 : t184_197.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node183 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,1,11⟩ = true := by decide
theorem check170_197 : t170_197.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node183 check170_183 check184_197
theorem check198_211 : t198_211.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check212_225 : t212_225.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node211 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,7,27⟩ = true := by decide
theorem check198_225 : t198_225.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node211 check198_211 check212_225
theorem node197 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,5,38⟩ = true := by decide
theorem check170_225 : t170_225.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node197 check170_197 check198_225
theorem node169 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,9,42⟩ = true := by decide
theorem check113_225 : t113_225.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node169 check113_169 check170_225
theorem node112 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,7,27⟩ = true := by decide
theorem check0_225 : t0_225.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node112 check0_112 check113_225
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_225
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M086
