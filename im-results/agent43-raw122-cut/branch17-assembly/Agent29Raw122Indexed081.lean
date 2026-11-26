import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M081
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def t0_12 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,6⟩ (.node .empty ⟨0,false,0,13⟩ .empty)) ⟨0,false,0,16⟩ (.node (.node .empty ⟨0,false,3,7⟩ .empty) ⟨0,false,3,9⟩ .empty)) ⟨0,false,3,16⟩ (.node (.node (.node .empty ⟨0,false,11,7⟩ .empty) ⟨0,false,11,9⟩ .empty) ⟨0,false,11,16⟩ (.node (.node .empty ⟨0,true,1,13⟩ .empty) ⟨0,true,1,19⟩ .empty)))
def t13_24 : Tree := (.node (.node (.node (.node .empty ⟨0,true,13,7⟩ .empty) ⟨1,false,1,0⟩ .empty) ⟨1,false,1,5⟩ (.node (.node .empty ⟨1,false,1,12⟩ .empty) ⟨1,false,1,15⟩ .empty)) ⟨1,false,1,23⟩ (.node (.node (.node .empty ⟨1,false,7,0⟩ .empty) ⟨1,false,10,4⟩ .empty) ⟨1,false,10,8⟩ (.node (.node .empty ⟨1,false,10,11⟩ .empty) ⟨1,false,10,15⟩ .empty)))
def t0_24 : Tree := .node t0_12 ⟨0,true,5,7⟩ t13_24
def t25_36 : Tree := (.node (.node (.node (.node .empty ⟨1,false,10,23⟩ .empty) ⟨2,false,2,0⟩ .empty) ⟨2,false,3,3⟩ (.node (.node .empty ⟨2,false,3,6⟩ .empty) ⟨2,false,3,13⟩ .empty)) ⟨2,false,3,19⟩ (.node (.node (.node .empty ⟨2,false,3,26⟩ .empty) ⟨2,false,4,1⟩ .empty) ⟨2,false,4,5⟩ (.node (.node .empty ⟨2,false,4,12⟩ .empty) ⟨2,false,4,17⟩ .empty)))
def t37_48 : Tree := (.node (.node (.node (.node .empty ⟨2,false,8,0⟩ .empty) ⟨2,false,11,7⟩ .empty) ⟨2,false,12,1⟩ (.node (.node .empty ⟨2,false,12,3⟩ .empty) ⟨2,false,12,5⟩ .empty)) ⟨2,false,12,6⟩ (.node (.node (.node .empty ⟨2,false,12,12⟩ .empty) ⟨2,false,12,13⟩ .empty) ⟨2,false,12,17⟩ (.node (.node .empty ⟨2,false,12,19⟩ .empty) ⟨2,false,12,24⟩ .empty)))
def t25_48 : Tree := .node t25_36 ⟨2,false,4,24⟩ t37_48
def t0_48 : Tree := .node t0_24 ⟨1,false,10,20⟩ t25_48
def t49_60 : Tree := (.node (.node (.node (.node .empty ⟨2,true,2,4⟩ .empty) ⟨2,true,2,11⟩ .empty) ⟨2,true,2,14⟩ (.node (.node .empty ⟨2,true,2,20⟩ .empty) ⟨2,true,2,21⟩ .empty)) ⟨2,true,2,22⟩ (.node (.node (.node .empty ⟨2,true,3,3⟩ .empty) ⟨2,true,3,6⟩ .empty) ⟨2,true,3,13⟩ (.node (.node .empty ⟨2,true,3,19⟩ .empty) ⟨2,true,3,26⟩ .empty)))
def t61_72 : Tree := (.node (.node (.node (.node .empty ⟨2,true,11,6⟩ .empty) ⟨2,true,11,13⟩ .empty) ⟨2,true,11,14⟩ (.node (.node .empty ⟨2,true,11,19⟩ .empty) ⟨2,true,11,21⟩ .empty)) ⟨2,true,11,22⟩ (.node (.node (.node .empty ⟨2,true,11,26⟩ .empty) ⟨3,false,2,1⟩ .empty) ⟨3,false,2,17⟩ (.node (.node .empty ⟨3,false,2,24⟩ .empty) ⟨3,false,3,0⟩ .empty)))
def t49_72 : Tree := .node t49_60 ⟨2,true,11,3⟩ t61_72
def t73_84 : Tree := (.node (.node (.node (.node .empty ⟨3,false,3,10⟩ .empty) ⟨3,false,3,18⟩ .empty) ⟨3,false,3,25⟩ (.node (.node .empty ⟨3,false,4,1⟩ .empty) ⟨3,false,4,5⟩ .empty)) ⟨3,false,4,12⟩ (.node (.node (.node .empty ⟨3,false,4,17⟩ .empty) ⟨3,false,4,24⟩ .empty) ⟨3,false,8,1⟩ (.node (.node .empty ⟨3,false,9,0⟩ .empty) ⟨3,false,11,5⟩ .empty)))
def t85_96 : Tree := (.node (.node (.node (.node .empty ⟨3,false,11,24⟩ .empty) ⟨3,false,12,2⟩ .empty) ⟨3,false,12,4⟩ (.node (.node .empty ⟨3,false,12,10⟩ .empty) ⟨3,false,12,18⟩ .empty)) ⟨3,false,12,25⟩ (.node (.node (.node .empty ⟨3,false,13,1⟩ .empty) ⟨3,false,13,5⟩ .empty) ⟨3,false,13,12⟩ (.node (.node .empty ⟨3,false,13,17⟩ .empty) ⟨3,false,13,24⟩ .empty)))
def t73_96 : Tree := .node t73_84 ⟨3,false,11,17⟩ t85_96
def t49_96 : Tree := .node t49_72 ⟨3,false,3,2⟩ t73_96
def t0_96 : Tree := .node t0_48 ⟨2,false,12,26⟩ t49_96
def t97_109 : Tree := (.node (.node (.node (.node .empty ⟨3,true,1,18⟩ .empty) ⟨3,true,1,25⟩ (.node .empty ⟨3,true,5,0⟩ .empty)) ⟨3,true,5,2⟩ (.node (.node .empty ⟨3,true,5,4⟩ .empty) ⟨3,true,5,10⟩ .empty)) ⟨3,true,5,11⟩ (.node (.node (.node .empty ⟨3,true,5,18⟩ .empty) ⟨3,true,5,20⟩ .empty) ⟨3,true,5,25⟩ (.node (.node .empty ⟨3,true,7,2⟩ .empty) ⟨3,true,10,10⟩ .empty)))
def t110_121 : Tree := (.node (.node (.node (.node .empty ⟨3,true,10,25⟩ .empty) ⟨3,true,13,0⟩ .empty) ⟨3,true,13,2⟩ (.node (.node .empty ⟨3,true,13,4⟩ .empty) ⟨3,true,13,10⟩ .empty)) ⟨3,true,13,11⟩ (.node (.node (.node .empty ⟨3,true,13,18⟩ .empty) ⟨3,true,13,20⟩ .empty) ⟨3,true,13,25⟩ (.node (.node .empty ⟨4,false,6,0⟩ .empty) ⟨4,true,2,1⟩ .empty)))
def t97_121 : Tree := .node t97_109 ⟨3,true,10,18⟩ t110_121
def t122_133 : Tree := (.node (.node (.node (.node .empty ⟨4,true,2,24⟩ .empty) ⟨4,true,6,1⟩ .empty) ⟨4,true,6,3⟩ (.node (.node .empty ⟨4,true,6,5⟩ .empty) ⟨4,true,6,6⟩ .empty)) ⟨4,true,6,12⟩ (.node (.node (.node .empty ⟨4,true,6,13⟩ .empty) ⟨4,true,6,17⟩ .empty) ⟨4,true,6,19⟩ (.node (.node .empty ⟨4,true,6,24⟩ .empty) ⟨4,true,6,26⟩ .empty)))
def t134_145 : Tree := (.node (.node (.node (.node .empty ⟨4,true,11,5⟩ .empty) ⟨4,true,11,12⟩ .empty) ⟨4,true,11,17⟩ (.node (.node .empty ⟨4,true,11,24⟩ .empty) ⟨5,false,0,5⟩ .empty)) ⟨5,false,0,12⟩ (.node (.node (.node .empty ⟨5,false,0,15⟩ .empty) ⟨5,false,2,12⟩ .empty) ⟨5,false,2,17⟩ (.node (.node .empty ⟨5,false,4,4⟩ .empty) ⟨5,false,4,8⟩ .empty)))
def t122_145 : Tree := .node t122_133 ⟨4,true,8,1⟩ t134_145
def t97_145 : Tree := .node t97_121 ⟨4,true,2,17⟩ t122_145
def t146_157 : Tree := (.node (.node (.node (.node .empty ⟨5,false,4,15⟩ .empty) ⟨5,false,4,20⟩ .empty) ⟨5,false,4,23⟩ (.node (.node .empty ⟨5,false,6,4⟩ .empty) ⟨5,false,12,4⟩ .empty)) ⟨5,false,12,8⟩ (.node (.node (.node .empty ⟨5,false,12,11⟩ .empty) ⟨5,false,12,15⟩ .empty) ⟨5,false,12,20⟩ (.node (.node .empty ⟨5,false,12,23⟩ .empty) ⟨5,true,0,4⟩ .empty)))
def t158_169 : Tree := (.node (.node (.node (.node .empty ⟨5,true,0,20⟩ .empty) ⟨5,true,1,3⟩ .empty) ⟨5,true,1,19⟩ (.node (.node .empty ⟨5,true,1,26⟩ .empty) ⟨5,true,3,10⟩ .empty)) ⟨5,true,3,11⟩ (.node (.node (.node .empty ⟨5,true,3,18⟩ .empty) ⟨5,true,3,20⟩ .empty) ⟨5,true,5,3⟩ (.node (.node .empty ⟨5,true,5,6⟩ .empty) ⟨5,true,5,13⟩ .empty)))
def t146_169 : Tree := .node t146_157 ⟨5,true,0,14⟩ t158_169
def t170_181 : Tree := (.node (.node (.node (.node .empty ⟨5,true,5,19⟩ .empty) ⟨5,true,5,21⟩ .empty) ⟨5,true,5,22⟩ (.node (.node .empty ⟨5,true,5,26⟩ .empty) ⟨5,true,7,3⟩ .empty)) ⟨5,true,10,6⟩ (.node (.node (.node .empty ⟨5,true,10,12⟩ .empty) ⟨5,true,10,13⟩ .empty) ⟨5,true,10,17⟩ (.node (.node .empty ⟨5,true,10,19⟩ .empty) ⟨5,true,10,26⟩ .empty)))
def t182_193 : Tree := (.node (.node (.node (.node .empty ⟨5,true,11,11⟩ .empty) ⟨5,true,11,18⟩ .empty) ⟨5,true,11,20⟩ (.node (.node .empty ⟨5,true,13,3⟩ .empty) ⟨5,true,13,6⟩ .empty)) ⟨5,true,13,13⟩ (.node (.node (.node .empty ⟨5,true,13,14⟩ .empty) ⟨5,true,13,19⟩ .empty) ⟨5,true,13,21⟩ (.node (.node .empty ⟨5,true,13,22⟩ .empty) ⟨5,true,13,26⟩ .empty)))
def t170_193 : Tree := .node t170_181 ⟨5,true,11,10⟩ t182_193
def t146_193 : Tree := .node t146_169 ⟨5,true,5,14⟩ t170_193
def t97_193 : Tree := .node t97_145 ⟨5,false,4,11⟩ t146_193
def t0_193 : Tree := .node t0_96 ⟨3,true,1,2⟩ t97_193
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 0, 4, 10, 5, 0, 0, 6, 7, 0, 0, 8, 9, 0, 0, 0, 0, 11, 12, 10, 13, 0, 0, 6],#[0, 1, 3, 2, 0, 24, 21, 4, 7, 5, 6, 10, 22, 11, 8, 0, 9, 0, 0, 0, 0, 17, 9, 12, 13, 10, 14, 11, 0, 15, 16, 0, 0, 0, 19, 18, 0, 17, 14, 20, 9, 12, 0, 15, 0, 23, 16, 0, 26, 25, 0, 24, 22, 20],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,3)],[(false,4)],[(true,5),(true,13)],[(false,6)],[(true,7)],[(false,8)],[(true,3),(true,11)],[(true,10)],[(false,11)],[(false,12)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3)],[(true,4)],[(false,5)],[(false,4)],[(false,7)],[(false,8),(false,11),(false,20)],[(true,5),(true,12)],[(true,6),(true,13)],[(true,11),(true,20)],[(false,12)],[(false,13),(false,19)],[(true,14),(true,21)],[(false,15),(false,23)],[(true,10),(true,18)],[(true,17)],[(false,17)],[(true,19),(true,26)],[(false,3)],[(false,6),(false,26)],[(true,22)],[(true,2),(true,25)],[(true,24)],[(false,24)]],
  t0_193⟩
theorem check0_12 : t0_12.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check13_24 : t13_24.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node12 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,5,7⟩ = true := by decide
theorem check0_24 : t0_24.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node12 check0_12 check13_24
theorem check25_36 : t25_36.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check37_48 : t37_48.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node36 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,4,24⟩ = true := by decide
theorem check25_48 : t25_48.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node36 check25_36 check37_48
theorem node24 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,10,20⟩ = true := by decide
theorem check0_48 : t0_48.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node24 check0_24 check25_48
theorem check49_60 : t49_60.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check61_72 : t61_72.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node60 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,11,3⟩ = true := by decide
theorem check49_72 : t49_72.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node60 check49_60 check61_72
theorem check73_84 : t73_84.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check85_96 : t85_96.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node84 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,11,17⟩ = true := by decide
theorem check73_96 : t73_96.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node84 check73_84 check85_96
theorem node72 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,3,2⟩ = true := by decide
theorem check49_96 : t49_96.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node72 check49_72 check73_96
theorem node48 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,12,26⟩ = true := by decide
theorem check0_96 : t0_96.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node48 check0_48 check49_96
theorem check97_109 : t97_109.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check110_121 : t110_121.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node109 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,10,18⟩ = true := by decide
theorem check97_121 : t97_121.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node109 check97_109 check110_121
theorem check122_133 : t122_133.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check134_145 : t134_145.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node133 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,8,1⟩ = true := by decide
theorem check122_145 : t122_145.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node133 check122_133 check134_145
theorem node121 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,2,17⟩ = true := by decide
theorem check97_145 : t97_145.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node121 check97_121 check122_145
theorem check146_157 : t146_157.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check158_169 : t158_169.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node157 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,0,14⟩ = true := by decide
theorem check146_169 : t146_169.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node157 check146_157 check158_169
theorem check170_181 : t170_181.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check182_193 : t182_193.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node181 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,11,10⟩ = true := by decide
theorem check170_193 : t170_193.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node181 check170_181 check182_193
theorem node169 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,5,14⟩ = true := by decide
theorem check146_193 : t146_193.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node169 check146_169 check170_193
theorem node145 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,4,11⟩ = true := by decide
theorem check97_193 : t97_193.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node145 check97_145 check146_193
theorem node96 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,1,2⟩ = true := by decide
theorem check0_193 : t0_193.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node96 check0_96 check97_193
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_193
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M081
