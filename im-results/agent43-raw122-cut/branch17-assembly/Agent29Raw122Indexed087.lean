import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M087
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def t0_12 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,6⟩ (.node .empty ⟨0,false,0,11⟩ .empty)) ⟨0,false,7,0⟩ (.node (.node .empty ⟨0,false,7,13⟩ .empty) ⟨0,false,7,23⟩ .empty)) ⟨0,false,7,30⟩ (.node (.node (.node .empty ⟨0,false,7,31⟩ .empty) ⟨0,false,7,33⟩ .empty) ⟨0,false,7,40⟩ (.node (.node .empty ⟨0,true,0,4⟩ .empty) ⟨0,true,0,9⟩ .empty)))
def t13_25 : Tree := (.node (.node (.node (.node .empty ⟨0,true,0,19⟩ .empty) ⟨0,true,0,25⟩ (.node .empty ⟨0,true,1,14⟩ .empty)) ⟨0,true,1,31⟩ (.node (.node .empty ⟨0,true,2,13⟩ .empty) ⟨0,true,2,30⟩ .empty)) ⟨0,true,4,12⟩ (.node (.node (.node .empty ⟨0,true,4,29⟩ .empty) ⟨0,true,5,5⟩ .empty) ⟨0,true,5,8⟩ (.node (.node .empty ⟨0,true,5,10⟩ .empty) ⟨0,true,5,28⟩ .empty)))
def t0_25 : Tree := .node t0_12 ⟨0,true,0,15⟩ t13_25
def t26_38 : Tree := (.node (.node (.node (.node .empty ⟨0,true,8,12⟩ .empty) ⟨0,true,8,21⟩ (.node .empty ⟨0,true,8,26⟩ .empty)) ⟨0,true,8,29⟩ (.node (.node .empty ⟨0,true,8,30⟩ .empty) ⟨0,true,8,33⟩ .empty)) ⟨0,true,8,39⟩ (.node (.node (.node .empty ⟨0,true,8,40⟩ .empty) ⟨1,false,1,0⟩ .empty) ⟨1,false,1,4⟩ (.node (.node .empty ⟨1,false,1,9⟩ .empty) ⟨1,false,1,15⟩ .empty)))
def t39_50 : Tree := (.node (.node (.node (.node .empty ⟨1,false,1,25⟩ .empty) ⟨1,false,4,1⟩ .empty) ⟨1,false,4,16⟩ (.node (.node .empty ⟨1,false,4,32⟩ .empty) ⟨1,false,6,0⟩ .empty)) ⟨1,false,6,12⟩ (.node (.node (.node .empty ⟨1,false,6,21⟩ .empty) ⟨1,false,6,26⟩ .empty) ⟨1,false,6,29⟩ (.node (.node .empty ⟨1,false,6,30⟩ .empty) ⟨1,false,6,33⟩ .empty)))
def t26_50 : Tree := .node t26_38 ⟨1,false,1,19⟩ t39_50
def t0_50 : Tree := .node t0_25 ⟨0,true,8,0⟩ t26_50
def t51_63 : Tree := (.node (.node (.node (.node .empty ⟨1,false,6,40⟩ .empty) ⟨1,true,4,7⟩ (.node .empty ⟨1,true,4,9⟩ .empty)) ⟨1,true,4,25⟩ (.node (.node .empty ⟨2,false,2,0⟩ .empty) ⟨2,false,2,14⟩ .empty)) ⟨2,false,2,31⟩ (.node (.node (.node .empty ⟨2,false,7,0⟩ .empty) ⟨2,false,7,2⟩ .empty) ⟨2,false,7,3⟩ (.node (.node .empty ⟨2,false,7,5⟩ .empty) ⟨2,false,7,8⟩ .empty)))
def t64_75 : Tree := (.node (.node (.node (.node .empty ⟨2,false,7,11⟩ .empty) ⟨2,false,7,26⟩ .empty) ⟨2,false,7,28⟩ (.node (.node .empty ⟨2,false,7,29⟩ .empty) ⟨2,false,7,34⟩ .empty)) ⟨2,false,7,35⟩ (.node (.node (.node .empty ⟨2,false,7,38⟩ .empty) ⟨2,false,7,39⟩ .empty) ⟨2,true,2,3⟩ (.node (.node .empty ⟨2,true,2,8⟩ .empty) ⟨2,true,2,10⟩ .empty)))
def t51_75 : Tree := .node t51_63 ⟨2,false,7,10⟩ t64_75
def t76_88 : Tree := (.node (.node (.node (.node .empty ⟨2,true,5,0⟩ .empty) ⟨2,true,5,13⟩ (.node .empty ⟨2,true,5,30⟩ .empty)) ⟨2,true,5,40⟩ (.node (.node .empty ⟨3,false,2,1⟩ .empty) ⟨3,false,2,16⟩ .empty)) ⟨3,false,2,32⟩ (.node (.node (.node .empty ⟨3,false,3,0⟩ .empty) ⟨3,false,3,13⟩ .empty) ⟨3,false,3,30⟩ (.node (.node .empty ⟨3,false,7,1⟩ .empty) ⟨3,false,7,2⟩ .empty)))
def t89_100 : Tree := (.node (.node (.node (.node .empty ⟨3,false,7,24⟩ .empty) ⟨3,false,7,25⟩ .empty) ⟨3,false,7,34⟩ (.node (.node .empty ⟨3,false,7,37⟩ .empty) ⟨3,false,7,38⟩ .empty)) ⟨3,false,8,0⟩ (.node (.node (.node .empty ⟨3,false,8,1⟩ .empty) ⟨3,false,8,2⟩ .empty) ⟨3,false,8,9⟩ (.node (.node .empty ⟨3,false,8,10⟩ .empty) ⟨3,false,8,24⟩ .empty)))
def t76_100 : Tree := .node t76_88 ⟨3,false,7,10⟩ t89_100
def t51_100 : Tree := .node t51_75 ⟨2,true,2,18⟩ t76_100
def t0_100 : Tree := .node t0_50 ⟨1,false,6,39⟩ t51_100
def t101_113 : Tree := (.node (.node (.node (.node .empty ⟨3,false,8,34⟩ .empty) ⟨3,false,8,37⟩ (.node .empty ⟨3,false,8,38⟩ .empty)) ⟨3,true,1,2⟩ (.node (.node .empty ⟨3,true,1,17⟩ .empty) ⟨3,true,6,2⟩ .empty)) ⟨3,true,6,10⟩ (.node (.node (.node .empty ⟨3,true,6,24⟩ .empty) ⟨3,true,6,25⟩ .empty) ⟨3,true,6,34⟩ (.node (.node .empty ⟨3,true,6,37⟩ .empty) ⟨3,true,6,38⟩ .empty)))
def t114_126 : Tree := (.node (.node (.node (.node .empty ⟨3,true,8,4⟩ .empty) ⟨3,true,8,7⟩ (.node .empty ⟨3,true,8,9⟩ .empty)) ⟨3,true,8,24⟩ (.node (.node .empty ⟨3,true,8,25⟩ .empty) ⟨3,true,8,27⟩ .empty)) ⟨3,true,8,36⟩ (.node (.node (.node .empty ⟨3,true,8,37⟩ .empty) ⟨4,true,2,1⟩ .empty) ⟨4,true,2,16⟩ (.node (.node .empty ⟨4,true,2,32⟩ .empty) ⟨4,true,7,1⟩ .empty)))
def t101_126 : Tree := .node t101_113 ⟨3,true,8,1⟩ t114_126
def t127_139 : Tree := (.node (.node (.node (.node .empty ⟨4,true,7,9⟩ .empty) ⟨4,true,7,10⟩ (.node .empty ⟨4,true,7,24⟩ .empty)) ⟨4,true,7,25⟩ (.node (.node .empty ⟨4,true,7,34⟩ .empty) ⟨4,true,7,37⟩ .empty)) ⟨4,true,7,38⟩ (.node (.node (.node .empty ⟨4,true,9,0⟩ .empty) ⟨4,true,9,2⟩ .empty) ⟨4,true,9,3⟩ (.node (.node .empty ⟨4,true,9,5⟩ .empty) ⟨4,true,9,8⟩ .empty)))
def t140_151 : Tree := (.node (.node (.node (.node .empty ⟨4,true,9,11⟩ .empty) ⟨4,true,9,26⟩ .empty) ⟨4,true,9,28⟩ (.node (.node .empty ⟨4,true,9,29⟩ .empty) ⟨4,true,9,34⟩ .empty)) ⟨4,true,9,35⟩ (.node (.node (.node .empty ⟨4,true,9,38⟩ .empty) ⟨4,true,9,39⟩ .empty) ⟨5,false,0,5⟩ (.node (.node .empty ⟨5,false,0,10⟩ .empty) ⟨5,false,0,20⟩ .empty)))
def t127_151 : Tree := .node t127_139 ⟨4,true,9,10⟩ t140_151
def t101_151 : Tree := .node t101_126 ⟨4,true,7,2⟩ t127_151
def t152_164 : Tree := (.node (.node (.node (.node .empty ⟨5,false,7,22⟩ .empty) ⟨5,false,7,27⟩ (.node .empty ⟨5,false,7,32⟩ .empty)) ⟨5,true,0,4⟩ (.node (.node .empty ⟨5,true,0,9⟩ .empty) ⟨5,true,0,19⟩ .empty)) ⟨5,true,0,25⟩ (.node (.node (.node .empty ⟨5,true,1,3⟩ .empty) ⟨5,true,1,8⟩ .empty) ⟨5,true,1,10⟩ (.node (.node .empty ⟨5,true,1,18⟩ .empty) ⟨5,true,2,7⟩ .empty)))
def t165_176 : Tree := (.node (.node (.node (.node .empty ⟨5,true,2,25⟩ .empty) ⟨5,true,4,5⟩ .empty) ⟨5,true,4,8⟩ (.node (.node .empty ⟨5,true,4,10⟩ .empty) ⟨5,true,4,28⟩ .empty)) ⟨5,true,5,4⟩ (.node (.node (.node .empty ⟨5,true,5,7⟩ .empty) ⟨5,true,5,9⟩ .empty) ⟨5,true,5,25⟩ (.node (.node .empty ⟨5,true,5,27⟩ .empty) ⟨5,true,5,36⟩ .empty)))
def t152_176 : Tree := .node t152_164 ⟨5,true,2,9⟩ t165_176
def t177_189 : Tree := (.node (.node (.node (.node .empty ⟨5,true,6,5⟩ .empty) ⟨5,true,6,8⟩ (.node .empty ⟨5,true,6,10⟩ .empty)) ⟨5,true,6,11⟩ (.node (.node .empty ⟨5,true,6,26⟩ .empty) ⟨5,true,6,28⟩ .empty)) ⟨5,true,6,29⟩ (.node (.node (.node .empty ⟨5,true,6,35⟩ .empty) ⟨5,true,6,39⟩ .empty) ⟨5,true,7,4⟩ (.node (.node .empty ⟨5,true,7,7⟩ .empty) ⟨5,true,7,9⟩ .empty)))
def t190_201 : Tree := (.node (.node (.node (.node .empty ⟨5,true,7,27⟩ .empty) ⟨5,true,7,36⟩ .empty) ⟨5,true,8,0⟩ (.node (.node .empty ⟨5,true,8,12⟩ .empty) ⟨5,true,8,21⟩ .empty)) ⟨5,true,8,26⟩ (.node (.node (.node .empty ⟨5,true,8,29⟩ .empty) ⟨5,true,8,30⟩ .empty) ⟨5,true,8,33⟩ (.node (.node .empty ⟨5,true,8,39⟩ .empty) ⟨5,true,8,40⟩ .empty)))
def t177_201 : Tree := .node t177_189 ⟨5,true,7,25⟩ t190_201
def t152_201 : Tree := .node t152_176 ⟨5,true,6,3⟩ t177_201
def t101_201 : Tree := .node t101_151 ⟨5,false,7,1⟩ t152_201
def t0_201 : Tree := .node t0_100 ⟨3,false,8,25⟩ t101_201
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 4, 0, 0, 0, 5, 0, 6, 0, 7, 8, 6, 0, 9, 0, 0],#[0, 1, 3, 2, 26, 24, 21, 4, 6, 5, 12, 7, 0, 0, 0, 8, 12, 9, 11, 10, 29, 25, 21, 36, 13, 22, 14, 16, 15, 0, 6, 0, 18, 17, 0, 0, 0, 19, 6, 20, 0, 0, 23, 22, 0, 0, 0, 0, 35, 34, 11, 10, 33, 27, 0, 28, 12, 7, 30, 27, 31, 32, 15, 0, 18, 17, 23, 22, 26, 37, 21, 36, 0, 28, 35, 38, 39, 37, 40, 27, 23, 32],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(true,2)],[(true,4)],[(true,5),(true,7)],[(true,6)],[(false,7)],[(true,8)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3)],[(true,4)],[(false,4),(false,15),(false,19)],[(true,5),(true,28)],[(true,7)],[(true,8)],[(true,9),(true,25)],[(false,9),(false,25)],[(false,5),(false,8),(false,28)],[(false,12)],[(false,13)],[(false,14),(false,31)],[(true,13)],[(true,16),(true,32)],[(false,16),(false,32)],[(true,18)],[(true,19)],[(false,3),(false,11),(false,35)],[(true,12),(true,21),(true,33)],[(false,21),(false,33),(false,40)],[(true,2)],[(true,10)],[(false,2),(false,34)],[(true,26),(true,29),(true,39)],[(true,27),(true,36)],[(false,10)],[(false,29)],[(false,30)],[(true,30),(true,40)],[(false,26)],[(true,24)],[(false,24),(false,37)],[(true,11),(true,35)],[(true,34),(true,38)],[(true,37)],[(false,38)],[(false,39)]],
  t0_201⟩
theorem check0_12 : t0_12.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check13_25 : t13_25.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node12 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,0,15⟩ = true := by decide
theorem check0_25 : t0_25.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node12 check0_12 check13_25
theorem check26_38 : t26_38.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check39_50 : t39_50.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node38 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,1,19⟩ = true := by decide
theorem check26_50 : t26_50.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node38 check26_38 check39_50
theorem node25 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,8,0⟩ = true := by decide
theorem check0_50 : t0_50.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node25 check0_25 check26_50
theorem check51_63 : t51_63.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check64_75 : t64_75.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node63 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,7,10⟩ = true := by decide
theorem check51_75 : t51_75.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node63 check51_63 check64_75
theorem check76_88 : t76_88.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check89_100 : t89_100.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node88 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,7,10⟩ = true := by decide
theorem check76_100 : t76_100.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node88 check76_88 check89_100
theorem node75 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,2,18⟩ = true := by decide
theorem check51_100 : t51_100.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node75 check51_75 check76_100
theorem node50 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,6,39⟩ = true := by decide
theorem check0_100 : t0_100.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node50 check0_50 check51_100
theorem check101_113 : t101_113.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check114_126 : t114_126.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node113 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,8,1⟩ = true := by decide
theorem check101_126 : t101_126.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node113 check101_113 check114_126
theorem check127_139 : t127_139.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check140_151 : t140_151.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node139 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,9,10⟩ = true := by decide
theorem check127_151 : t127_151.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node139 check127_139 check140_151
theorem node126 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,7,2⟩ = true := by decide
theorem check101_151 : t101_151.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node126 check101_126 check127_151
theorem check152_164 : t152_164.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check165_176 : t165_176.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node164 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,2,9⟩ = true := by decide
theorem check152_176 : t152_176.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node164 check152_164 check165_176
theorem check177_189 : t177_189.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check190_201 : t190_201.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node189 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,7,25⟩ = true := by decide
theorem check177_201 : t177_201.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node189 check177_189 check190_201
theorem node176 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,6,3⟩ = true := by decide
theorem check152_201 : t152_201.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node176 check152_176 check177_201
theorem node151 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,7,1⟩ = true := by decide
theorem check101_201 : t101_201.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node151 check101_151 check152_201
theorem node100 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,8,25⟩ = true := by decide
theorem check0_201 : t0_201.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node100 check0_100 check101_201
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_201
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M087
