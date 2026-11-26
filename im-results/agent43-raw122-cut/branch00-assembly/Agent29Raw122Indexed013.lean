import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M013
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_12 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,1,4⟩ (.node .empty ⟨0,false,1,14⟩ .empty)) ⟨0,false,1,19⟩ (.node (.node .empty ⟨0,false,1,35⟩ .empty) ⟨0,false,1,45⟩ .empty)) ⟨0,false,1,48⟩ (.node (.node (.node .empty ⟨0,false,4,7⟩ .empty) ⟨0,false,4,29⟩ .empty) ⟨0,false,6,25⟩ (.node (.node .empty ⟨0,false,7,0⟩ .empty) ⟨0,false,7,8⟩ .empty)))
def t13_25 : Tree := (.node (.node (.node (.node .empty ⟨0,false,7,39⟩ .empty) ⟨0,false,7,49⟩ (.node .empty ⟨0,false,7,52⟩ .empty)) ⟨0,false,8,4⟩ (.node (.node .empty ⟨0,false,8,14⟩ .empty) ⟨0,false,8,19⟩ .empty)) ⟨0,false,8,35⟩ (.node (.node (.node .empty ⟨0,false,8,45⟩ .empty) ⟨0,false,8,48⟩ .empty) ⟨0,false,9,29⟩ (.node (.node .empty ⟨0,false,9,37⟩ .empty) ⟨0,true,0,4⟩ .empty)))
def t0_25 : Tree := .node t0_12 ⟨0,false,7,30⟩ t13_25
def t26_38 : Tree := (.node (.node (.node (.node .empty ⟨0,true,1,14⟩ .empty) ⟨0,true,1,19⟩ (.node .empty ⟨0,true,1,35⟩ .empty)) ⟨0,true,1,45⟩ (.node (.node .empty ⟨0,true,1,48⟩ .empty) ⟨0,true,4,11⟩ .empty)) ⟨0,true,4,32⟩ (.node (.node (.node .empty ⟨0,true,5,29⟩ .empty) ⟨0,true,5,37⟩ .empty) ⟨0,true,6,25⟩ (.node (.node .empty ⟨0,true,7,4⟩ .empty) ⟨0,true,7,14⟩ .empty)))
def t39_51 : Tree := (.node (.node (.node (.node .empty ⟨0,true,8,19⟩ .empty) ⟨0,true,8,35⟩ (.node .empty ⟨0,true,8,45⟩ .empty)) ⟨0,true,8,48⟩ (.node (.node .empty ⟨0,true,9,11⟩ .empty) ⟨0,true,9,32⟩ .empty)) ⟨0,true,9,42⟩ (.node (.node (.node .empty ⟨0,true,9,51⟩ .empty) ⟨0,true,9,54⟩ .empty) ⟨1,false,1,0⟩ (.node (.node .empty ⟨1,false,2,3⟩ .empty) ⟨1,false,2,13⟩ .empty)))
def t26_51 : Tree := .node t26_38 ⟨0,true,8,14⟩ t39_51
def t0_51 : Tree := .node t0_25 ⟨0,true,0,14⟩ t26_51
def t52_64 : Tree := (.node (.node (.node (.node .empty ⟨1,false,2,34⟩ .empty) ⟨1,false,2,44⟩ (.node .empty ⟨1,false,2,47⟩ .empty)) ⟨1,false,7,24⟩ (.node (.node .empty ⟨1,false,8,0⟩ .empty) ⟨1,false,9,6⟩ .empty)) ⟨1,false,9,28⟩ (.node (.node (.node .empty ⟨1,false,10,21⟩ .empty) ⟨1,false,10,28⟩ .empty) ⟨1,true,8,4⟩ (.node (.node .empty ⟨1,true,8,14⟩ .empty) ⟨1,true,8,19⟩ .empty)))
def t65_77 : Tree := (.node (.node (.node (.node .empty ⟨1,true,8,45⟩ .empty) ⟨1,true,8,48⟩ (.node .empty ⟨2,false,2,0⟩ .empty)) ⟨2,false,4,1⟩ (.node (.node .empty ⟨2,false,4,12⟩ .empty) ⟨2,false,4,16⟩ .empty)) ⟨2,false,4,33⟩ (.node (.node (.node .empty ⟨2,false,4,43⟩ .empty) ⟨2,false,4,46⟩ .empty) ⟨2,false,8,22⟩ (.node (.node .empty ⟨2,false,10,5⟩ .empty) ⟨2,false,10,15⟩ .empty)))
def t52_77 : Tree := .node t52_64 ⟨1,true,8,35⟩ t65_77
def t78_90 : Tree := (.node (.node (.node (.node .empty ⟨2,false,12,13⟩ .empty) ⟨2,false,12,18⟩ (.node .empty ⟨2,false,12,34⟩ .empty)) ⟨2,false,12,44⟩ (.node (.node .empty ⟨2,false,12,47⟩ .empty) ⟨2,false,15,15⟩ .empty)) ⟨2,false,15,20⟩ (.node (.node (.node .empty ⟨3,false,2,1⟩ .empty) ⟨3,false,3,0⟩ .empty) ⟨3,false,4,16⟩ (.node (.node .empty ⟨3,false,4,33⟩ .empty) ⟨3,false,4,46⟩ .empty)))
def t91_102 : Tree := (.node (.node (.node (.node .empty ⟨3,false,5,32⟩ .empty) ⟨3,false,5,42⟩ .empty) ⟨3,false,5,51⟩ (.node (.node .empty ⟨3,false,5,54⟩ .empty) ⟨3,false,8,22⟩ .empty)) ⟨3,false,10,8⟩ (.node (.node (.node .empty ⟨3,false,10,30⟩ .empty) ⟨3,false,11,4⟩ .empty) ⟨3,false,11,14⟩ (.node (.node .empty ⟨3,false,12,2⟩ .empty) ⟨3,false,12,17⟩ .empty)))
def t78_102 : Tree := .node t78_90 ⟨3,false,5,11⟩ t91_102
def t52_102 : Tree := .node t52_77 ⟨2,false,12,3⟩ t78_102
def t0_102 : Tree := .node t0_51 ⟨1,false,2,18⟩ t52_102
def t103_115 : Tree := (.node (.node (.node (.node .empty ⟨3,false,13,1⟩ .empty) ⟨3,false,13,12⟩ (.node .empty ⟨3,false,13,16⟩ .empty)) ⟨3,false,13,33⟩ (.node (.node .empty ⟨3,false,13,43⟩ .empty) ⟨3,false,13,46⟩ .empty)) ⟨3,false,15,8⟩ (.node (.node (.node .empty ⟨3,false,15,30⟩ .empty) ⟨3,false,15,39⟩ .empty) ⟨3,false,15,49⟩ (.node (.node .empty ⟨3,false,15,52⟩ .empty) ⟨3,false,16,14⟩ .empty)))
def t116_128 : Tree := (.node (.node (.node (.node .empty ⟨3,false,16,35⟩ .empty) ⟨3,false,16,45⟩ (.node .empty ⟨3,false,16,48⟩ .empty)) ⟨3,true,1,2⟩ (.node (.node .empty ⟨3,true,2,17⟩ .empty) ⟨3,true,5,0⟩ .empty)) ⟨3,true,5,11⟩ (.node (.node (.node .empty ⟨3,true,5,32⟩ .empty) ⟨3,true,5,42⟩ .empty) ⟨3,true,5,51⟩ (.node (.node .empty ⟨3,true,5,54⟩ .empty) ⟨3,true,7,23⟩ .empty)))
def t103_128 : Tree := .node t103_115 ⟨3,false,16,19⟩ t116_128
def t129_141 : Tree := (.node (.node (.node (.node .empty ⟨3,true,9,9⟩ .empty) ⟨3,true,10,9⟩ (.node .empty ⟨3,true,10,40⟩ .empty)) ⟨3,true,12,2⟩ (.node (.node .empty ⟨3,true,12,17⟩ .empty) ⟨3,true,12,36⟩ .empty)) ⟨4,false,0,5⟩ (.node (.node (.node .empty ⟨4,false,0,15⟩ .empty) ⟨4,false,0,20⟩ .empty) ⟨4,false,4,38⟩ (.node (.node .empty ⟨4,false,5,26⟩ .empty) ⟨4,false,6,0⟩ .empty)))
def t142_153 : Tree := (.node (.node (.node (.node .empty ⟨4,false,6,31⟩ .empty) ⟨4,false,6,41⟩ .empty) ⟨4,false,6,50⟩ (.node (.node .empty ⟨4,false,6,53⟩ .empty) ⟨4,true,0,15⟩ .empty)) ⟨4,true,0,20⟩ (.node (.node (.node .empty ⟨4,true,2,1⟩ .empty) ⟨4,true,2,12⟩ .empty) ⟨4,true,4,12⟩ (.node (.node .empty ⟨4,true,4,16⟩ .empty) ⟨4,true,4,33⟩ .empty)))
def t129_153 : Tree := .node t129_141 ⟨4,false,6,10⟩ t142_153
def t103_153 : Tree := .node t103_128 ⟨3,true,8,2⟩ t129_153
def t154_166 : Tree := (.node (.node (.node (.node .empty ⟨4,true,4,46⟩ .empty) ⟨4,true,5,26⟩ (.node .empty ⟨4,true,6,5⟩ .empty)) ⟨4,true,6,15⟩ (.node (.node .empty ⟨4,true,7,15⟩ .empty) ⟨4,true,7,20⟩ .empty)) ⟨4,true,8,22⟩ (.node (.node (.node .empty ⟨4,true,10,8⟩ .empty) ⟨4,true,10,30⟩ .empty) ⟨4,true,14,1⟩ (.node (.node .empty ⟨4,true,14,12⟩ .empty) ⟨4,true,14,16⟩ .empty)))
def t167_179 : Tree := (.node (.node (.node (.node .empty ⟨4,true,14,43⟩ .empty) ⟨4,true,14,46⟩ (.node .empty ⟨4,true,15,8⟩ .empty)) ⟨4,true,15,30⟩ (.node (.node .empty ⟨4,true,15,39⟩ .empty) ⟨4,true,15,49⟩ .empty)) ⟨4,true,15,52⟩ (.node (.node (.node .empty ⟨5,false,0,21⟩ .empty) ⟨5,false,0,28⟩ .empty) ⟨5,false,4,27⟩ (.node (.node .empty ⟨5,true,1,3⟩ .empty) ⟨5,true,1,13⟩ .empty)))
def t154_179 : Tree := .node t154_166 ⟨4,true,14,33⟩ t167_179
def t180_192 : Tree := (.node (.node (.node (.node .empty ⟨5,true,2,18⟩ .empty) ⟨5,true,2,34⟩ (.node .empty ⟨5,true,2,44⟩ .empty)) ⟨5,true,2,47⟩ (.node (.node .empty ⟨5,true,5,6⟩ .empty) ⟨5,true,5,28⟩ .empty)) ⟨5,true,6,21⟩ (.node (.node (.node .empty ⟨5,true,6,28⟩ .empty) ⟨5,true,7,24⟩ .empty) ⟨5,true,8,3⟩ (.node (.node .empty ⟨5,true,8,13⟩ .empty) ⟨5,true,9,10⟩ .empty)))
def t193_204 : Tree := (.node (.node (.node (.node .empty ⟨5,true,10,10⟩ .empty) ⟨5,true,10,31⟩ .empty) ⟨5,true,10,41⟩ (.node (.node .empty ⟨5,true,10,50⟩ .empty) ⟨5,true,10,53⟩ .empty)) ⟨5,true,12,3⟩ (.node (.node (.node .empty ⟨5,true,12,13⟩ .empty) ⟨5,true,12,18⟩ .empty) ⟨5,true,12,34⟩ (.node (.node .empty ⟨5,true,12,44⟩ .empty) ⟨5,true,12,47⟩ .empty)))
def t180_204 : Tree := .node t180_192 ⟨5,true,9,31⟩ t193_204
def t154_204 : Tree := .node t154_179 ⟨5,true,2,13⟩ t180_204
def t103_204 : Tree := .node t103_153 ⟨4,true,4,43⟩ t154_204
def t0_204 : Tree := .node t0_102 ⟨3,false,12,36⟩ t103_204
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 4, 0, 0, 5, 9, 0, 6, 0, 7, 0, 8, 12, 2, 0, 10, 11, 15, 0, 0, 13, 14, 0, 0, 0, 0, 16, 0, 0, 0],#[0, 1, 3, 2, 0, 22, 4, 0, 5, 8, 6, 0, 7, 0, 0, 0, 10, 9, 0, 0, 11, 0, 12, 16, 13, 36, 14, 0, 15, 30, 28, 0, 18, 17, 0, 22, 19, 0, 20, 39, 21, 0, 37, 0, 24, 23, 0, 0, 25, 0, 26, 0, 27, 0, 0, 0, 29, 0, 38, 0, 31, 9, 32, 0, 12, 33, 34, 17, 35, 0, 20, 52, 0, 22, 38, 0, 0, 0, 41, 40, 0, 0, 42, 0, 43, 46, 44, 36, 45, 0, 20, 49, 47, 17, 48, 0, 20, 8, 50, 40, 51, 0, 12, 33, 53, 40, 54, 0, 43, 33],
  #[[(false,0)],[(true,0)],[(true,1),(true,8)],[(false,2)],[(true,2)],[(false,4)],[(true,5)],[(true,6)],[(true,7)],[(true,4)],[(true,9)],[(false,10)],[(false,8)],[(false,12)],[(true,12)],[(true,10)],[(false,15)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(false,4)],[(false,5)],[(false,6)],[(true,4),(true,48)],[(true,8),(true,30)],[(false,8)],[(false,10)],[(false,11),(false,32),(false,51)],[(false,12)],[(false,13)],[(false,14)],[(true,11)],[(true,16),(true,33),(true,46)],[(false,16)],[(false,18)],[(false,19),(false,35),(false,45),(false,48)],[(false,20)],[(true,2),(true,17),(true,36)],[(true,22)],[(false,22)],[(false,24)],[(false,25)],[(false,26)],[(false,15)],[(false,28)],[(true,14)],[(false,30)],[(false,31)],[(true,32),(true,51),(true,54)],[(false,33)],[(false,34)],[(true,12),(true,43)],[(false,21)],[(false,29),(false,37)],[(true,19)],[(true,39),(true,49),(true,52)],[(false,39)],[(false,41)],[(false,42),(false,54)],[(false,43)],[(false,44)],[(true,42)],[(false,46)],[(false,47)],[(true,45)],[(false,49)],[(false,50)],[(true,35)],[(false,52)],[(false,53)]],
  t0_204⟩
theorem check0_12 : t0_12.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check13_25 : t13_25.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node12 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,7,30⟩ = true := by decide
theorem check0_25 : t0_25.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node12 check0_12 check13_25
theorem check26_38 : t26_38.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check39_51 : t39_51.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node38 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,8,14⟩ = true := by decide
theorem check26_51 : t26_51.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node38 check26_38 check39_51
theorem node25 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,0,14⟩ = true := by decide
theorem check0_51 : t0_51.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node25 check0_25 check26_51
theorem check52_64 : t52_64.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check65_77 : t65_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node64 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,8,35⟩ = true := by decide
theorem check52_77 : t52_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node64 check52_64 check65_77
theorem check78_90 : t78_90.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check91_102 : t91_102.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node90 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,5,11⟩ = true := by decide
theorem check78_102 : t78_102.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node90 check78_90 check91_102
theorem node77 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,12,3⟩ = true := by decide
theorem check52_102 : t52_102.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node77 check52_77 check78_102
theorem node51 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,2,18⟩ = true := by decide
theorem check0_102 : t0_102.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node51 check0_51 check52_102
theorem check103_115 : t103_115.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check116_128 : t116_128.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node115 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,16,19⟩ = true := by decide
theorem check103_128 : t103_128.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node115 check103_115 check116_128
theorem check129_141 : t129_141.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check142_153 : t142_153.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node141 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,6,10⟩ = true := by decide
theorem check129_153 : t129_153.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node141 check129_141 check142_153
theorem node128 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,8,2⟩ = true := by decide
theorem check103_153 : t103_153.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node128 check103_128 check129_153
theorem check154_166 : t154_166.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check167_179 : t167_179.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node166 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,14,33⟩ = true := by decide
theorem check154_179 : t154_179.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node166 check154_166 check167_179
theorem check180_192 : t180_192.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check193_204 : t193_204.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node192 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,9,31⟩ = true := by decide
theorem check180_204 : t180_204.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node192 check180_192 check193_204
theorem node179 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,2,13⟩ = true := by decide
theorem check154_204 : t154_204.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node179 check154_179 check180_204
theorem node153 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,4,43⟩ = true := by decide
theorem check103_204 : t103_204.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node153 check103_153 check154_204
theorem node102 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,12,36⟩ = true := by decide
theorem check0_204 : t0_204.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node102 check0_102 check103_204
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_204
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M013
