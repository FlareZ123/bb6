import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M098
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
  | 5,false => some (some ⟨true,true,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def t0_12 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,12⟩ (.node .empty ⟨0,false,4,1⟩ .empty)) ⟨0,false,4,13⟩ (.node (.node .empty ⟨0,false,4,28⟩ .empty) ⟨0,true,0,11⟩ .empty)) ⟨0,true,1,10⟩ (.node (.node (.node .empty ⟨0,true,1,27⟩ .empty) ⟨0,true,2,9⟩ .empty) ⟨0,true,2,26⟩ (.node (.node .empty ⟨0,true,4,5⟩ .empty) ⟨0,true,4,7⟩ .empty)))
def t13_24 : Tree := (.node (.node (.node (.node .empty ⟨0,true,4,25⟩ .empty) ⟨0,true,4,29⟩ .empty) ⟨1,false,1,0⟩ (.node (.node .empty ⟨1,false,1,11⟩ .empty) ⟨1,true,1,4⟩ .empty)) ⟨1,true,1,7⟩ (.node (.node (.node .empty ⟨1,true,1,16⟩ .empty) ⟨1,true,1,22⟩ .empty) ⟨1,true,5,0⟩ (.node (.node .empty ⟨1,true,5,9⟩ .empty) ⟨1,true,5,26⟩ .empty)))
def t0_24 : Tree := .node t0_12 ⟨0,true,4,22⟩ t13_24
def t25_36 : Tree := (.node (.node (.node (.node .empty ⟨1,true,9,0⟩ .empty) ⟨1,true,9,9⟩ .empty) ⟨1,true,9,18⟩ (.node (.node .empty ⟨1,true,9,21⟩ .empty) ⟨1,true,9,26⟩ .empty)) ⟨1,true,9,27⟩ (.node (.node (.node .empty ⟨1,true,9,35⟩ .empty) ⟨2,false,2,0⟩ .empty) ⟨2,false,2,10⟩ (.node (.node .empty ⟨2,false,2,27⟩ .empty) ⟨2,false,6,0⟩ .empty)))
def t37_48 : Tree := (.node (.node (.node (.node .empty ⟨2,false,6,3⟩ .empty) ⟨2,false,6,5⟩ .empty) ⟨2,false,6,7⟩ (.node (.node .empty ⟨2,false,6,21⟩ .empty) ⟨2,false,6,22⟩ .empty)) ⟨2,false,6,25⟩ (.node (.node (.node .empty ⟨2,false,6,26⟩ .empty) ⟨2,false,6,29⟩ .empty) ⟨2,false,6,30⟩ (.node (.node .empty ⟨2,false,6,31⟩ .empty) ⟨2,false,6,34⟩ .empty)))
def t25_48 : Tree := .node t25_36 ⟨2,false,6,2⟩ t37_48
def t0_48 : Tree := .node t0_24 ⟨1,true,5,35⟩ t25_48
def t49_61 : Tree := (.node (.node (.node (.node .empty ⟨2,true,2,3⟩ .empty) ⟨2,true,2,6⟩ (.node .empty ⟨2,true,2,8⟩ .empty)) ⟨2,true,2,15⟩ (.node (.node .empty ⟨2,true,2,24⟩ .empty) ⟨3,false,2,1⟩ .empty)) ⟨3,false,2,13⟩ (.node (.node (.node .empty ⟨3,false,2,28⟩ .empty) ⟨3,false,3,0⟩ .empty) ⟨3,false,3,9⟩ (.node (.node .empty ⟨3,false,3,26⟩ .empty) ⟨3,false,6,1⟩ .empty)))
def t62_73 : Tree := (.node (.node (.node (.node .empty ⟨3,false,6,20⟩ .empty) ⟨3,false,6,22⟩ .empty) ⟨3,false,6,24⟩ (.node (.node .empty ⟨3,false,6,30⟩ .empty) ⟨3,false,6,33⟩ .empty)) ⟨3,false,6,34⟩ (.node (.node (.node .empty ⟨3,false,7,0⟩ .empty) ⟨3,false,7,1⟩ .empty) ⟨3,false,7,2⟩ (.node (.node .empty ⟨3,false,7,8⟩ .empty) ⟨3,false,7,20⟩ .empty)))
def t49_73 : Tree := .node t49_61 ⟨3,false,6,2⟩ t62_73
def t74_85 : Tree := (.node (.node (.node (.node .empty ⟨3,false,7,24⟩ .empty) ⟨3,false,7,30⟩ .empty) ⟨3,false,7,33⟩ (.node (.node .empty ⟨3,false,7,34⟩ .empty) ⟨3,true,1,2⟩ .empty)) ⟨3,true,1,14⟩ (.node (.node (.node .empty ⟨3,true,1,29⟩ .empty) ⟨3,true,5,2⟩ .empty) ⟨3,true,5,20⟩ (.node (.node .empty ⟨3,true,5,22⟩ .empty) ⟨3,true,5,24⟩ .empty)))
def t86_97 : Tree := (.node (.node (.node (.node .empty ⟨3,true,5,33⟩ .empty) ⟨3,true,5,34⟩ .empty) ⟨3,true,7,1⟩ (.node (.node .empty ⟨3,true,7,4⟩ .empty) ⟨3,true,7,6⟩ .empty)) ⟨3,true,7,8⟩ (.node (.node (.node .empty ⟨3,true,7,20⟩ .empty) ⟨3,true,7,23⟩ .empty) ⟨3,true,7,24⟩ (.node (.node .empty ⟨3,true,7,28⟩ .empty) ⟨3,true,7,32⟩ .empty)))
def t74_97 : Tree := .node t74_85 ⟨3,true,5,30⟩ t86_97
def t49_97 : Tree := .node t49_73 ⟨3,false,7,22⟩ t74_97
def t0_97 : Tree := .node t0_48 ⟨2,false,6,35⟩ t49_97
def t98_110 : Tree := (.node (.node (.node (.node .empty ⟨3,true,9,2⟩ .empty) ⟨3,true,9,20⟩ (.node .empty ⟨3,true,9,22⟩ .empty)) ⟨3,true,9,24⟩ (.node (.node .empty ⟨3,true,9,30⟩ .empty) ⟨3,true,9,33⟩ .empty)) ⟨3,true,9,34⟩ (.node (.node (.node .empty ⟨4,true,2,1⟩ .empty) ⟨4,true,2,13⟩ .empty) ⟨4,true,2,28⟩ (.node (.node .empty ⟨4,true,6,1⟩ .empty) ⟨4,true,6,2⟩ .empty)))
def t111_122 : Tree := (.node (.node (.node (.node .empty ⟨4,true,6,20⟩ .empty) ⟨4,true,6,22⟩ .empty) ⟨4,true,6,24⟩ (.node (.node .empty ⟨4,true,6,30⟩ .empty) ⟨4,true,6,33⟩ .empty)) ⟨4,true,6,34⟩ (.node (.node (.node .empty ⟨4,true,8,0⟩ .empty) ⟨4,true,8,2⟩ .empty) ⟨4,true,8,3⟩ (.node (.node .empty ⟨4,true,8,5⟩ .empty) ⟨4,true,8,7⟩ .empty)))
def t98_122 : Tree := .node t98_110 ⟨4,true,6,8⟩ t111_122
def t123_134 : Tree := (.node (.node (.node (.node .empty ⟨4,true,8,22⟩ .empty) ⟨4,true,8,25⟩ .empty) ⟨4,true,8,26⟩ (.node (.node .empty ⟨4,true,8,29⟩ .empty) ⟨4,true,8,30⟩ .empty)) ⟨4,true,8,31⟩ (.node (.node (.node .empty ⟨4,true,8,34⟩ .empty) ⟨4,true,8,35⟩ .empty) ⟨5,false,0,5⟩ (.node (.node .empty ⟨5,false,0,8⟩ .empty) ⟨5,false,0,17⟩ .empty)))
def t135_146 : Tree := (.node (.node (.node (.node .empty ⟨5,false,6,1⟩ .empty) ⟨5,false,6,13⟩ .empty) ⟨5,false,6,19⟩ (.node (.node .empty ⟨5,false,6,23⟩ .empty) ⟨5,false,6,28⟩ .empty)) ⟨5,true,0,4⟩ (.node (.node (.node .empty ⟨5,true,0,7⟩ .empty) ⟨5,true,0,16⟩ .empty) ⟨5,true,0,22⟩ (.node (.node .empty ⟨5,true,1,3⟩ .empty) ⟨5,true,1,6⟩ .empty)))
def t123_146 : Tree := .node t123_134 ⟨5,false,0,24⟩ t135_146
def t98_146 : Tree := .node t98_122 ⟨4,true,8,21⟩ t123_146
def t147_159 : Tree := (.node (.node (.node (.node .empty ⟨5,true,1,15⟩ .empty) ⟨5,true,1,24⟩ (.node .empty ⟨5,true,2,5⟩ .empty)) ⟨5,true,2,7⟩ (.node (.node .empty ⟨5,true,2,22⟩ .empty) ⟨5,true,2,25⟩ .empty)) ⟨5,true,2,29⟩ (.node (.node (.node .empty ⟨5,true,4,4⟩ .empty) ⟨5,true,4,6⟩ .empty) ⟨5,true,4,8⟩ (.node (.node .empty ⟨5,true,4,23⟩ .empty) ⟨5,true,4,24⟩ .empty)))
def t160_171 : Tree := (.node (.node (.node (.node .empty ⟨5,true,4,32⟩ .empty) ⟨5,true,5,3⟩ .empty) ⟨5,true,5,5⟩ (.node (.node .empty ⟨5,true,5,7⟩ .empty) ⟨5,true,5,21⟩ .empty)) ⟨5,true,5,22⟩ (.node (.node (.node .empty ⟨5,true,5,25⟩ .empty) ⟨5,true,5,26⟩ .empty) ⟨5,true,5,29⟩ (.node (.node .empty ⟨5,true,5,31⟩ .empty) ⟨5,true,5,35⟩ .empty)))
def t147_171 : Tree := .node t147_159 ⟨5,true,4,28⟩ t160_171
def t172_183 : Tree := (.node (.node (.node (.node .empty ⟨5,true,6,6⟩ .empty) ⟨5,true,6,8⟩ .empty) ⟨5,true,6,23⟩ (.node (.node .empty ⟨5,true,6,24⟩ .empty) ⟨5,true,6,28⟩ .empty)) ⟨5,true,6,32⟩ (.node (.node (.node .empty ⟨5,true,7,0⟩ .empty) ⟨5,true,7,9⟩ .empty) ⟨5,true,7,18⟩ (.node (.node .empty ⟨5,true,7,21⟩ .empty) ⟨5,true,7,26⟩ .empty)))
def t184_195 : Tree := (.node (.node (.node (.node .empty ⟨5,true,7,35⟩ .empty) ⟨5,true,9,3⟩ .empty) ⟨5,true,9,5⟩ (.node (.node .empty ⟨5,true,9,7⟩ .empty) ⟨5,true,9,21⟩ .empty)) ⟨5,true,9,22⟩ (.node (.node (.node .empty ⟨5,true,9,25⟩ .empty) ⟨5,true,9,26⟩ .empty) ⟨5,true,9,29⟩ (.node (.node .empty ⟨5,true,9,31⟩ .empty) ⟨5,true,9,35⟩ .empty)))
def t172_195 : Tree := .node t172_183 ⟨5,true,7,27⟩ t184_195
def t147_195 : Tree := .node t147_171 ⟨5,true,6,4⟩ t172_195
def t98_195 : Tree := .node t98_146 ⟨5,true,1,8⟩ t147_195
def t0_195 : Tree := .node t0_97 ⟨3,true,7,33⟩ t98_195
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 4, 0, 0, 0, 5, 0, 6, 7, 9, 0, 8, 0, 0, 0, 6],#[0, 1, 3, 2, 21, 20, 18, 4, 0, 5, 9, 6, 0, 7, 9, 8, 31, 22, 10, 13, 11, 0, 12, 0, 0, 0, 15, 14, 0, 0, 0, 16, 0, 17, 0, 0, 0, 19, 0, 0, 31, 30, 18, 23, 26, 24, 0, 25, 31, 22, 9, 6, 27, 28, 11, 19, 15, 29, 9, 6, 21, 33, 18, 32, 0, 25, 31, 34, 35, 33, 18, 28],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(true,2)],[(true,4)],[(true,5),(true,9)],[(false,6)],[(true,7)],[(true,6)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3)],[(true,4)],[(true,5),(true,25),(true,29)],[(true,6)],[(true,7)],[(false,5),(false,7),(false,25),(false,29)],[(false,9)],[(false,10),(false,27)],[(false,11)],[(true,9)],[(true,13)],[(false,13),(false,28)],[(true,15)],[(true,16)],[(false,3),(false,21),(false,31),(false,35)],[(true,18),(true,27)],[(true,2)],[(false,2),(false,30)],[(true,8),(true,24)],[(true,21)],[(true,22)],[(true,23),(true,32)],[(false,22)],[(false,26)],[(true,26),(true,35)],[(true,28)],[(true,20)],[(false,8),(false,20),(false,24),(false,33)],[(true,31)],[(true,30),(true,34)],[(true,33)],[(false,34)]],
  t0_195⟩
theorem check0_12 : t0_12.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check13_24 : t13_24.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node12 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,4,22⟩ = true := by decide
theorem check0_24 : t0_24.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node12 check0_12 check13_24
theorem check25_36 : t25_36.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check37_48 : t37_48.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node36 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,6,2⟩ = true := by decide
theorem check25_48 : t25_48.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node36 check25_36 check37_48
theorem node24 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,5,35⟩ = true := by decide
theorem check0_48 : t0_48.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node24 check0_24 check25_48
theorem check49_61 : t49_61.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check62_73 : t62_73.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node61 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,6,2⟩ = true := by decide
theorem check49_73 : t49_73.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node61 check49_61 check62_73
theorem check74_85 : t74_85.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check86_97 : t86_97.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node85 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,5,30⟩ = true := by decide
theorem check74_97 : t74_97.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node85 check74_85 check86_97
theorem node73 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,7,22⟩ = true := by decide
theorem check49_97 : t49_97.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node73 check49_73 check74_97
theorem node48 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,6,35⟩ = true := by decide
theorem check0_97 : t0_97.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node48 check0_48 check49_97
theorem check98_110 : t98_110.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check111_122 : t111_122.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node110 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,6,8⟩ = true := by decide
theorem check98_122 : t98_122.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node110 check98_110 check111_122
theorem check123_134 : t123_134.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check135_146 : t135_146.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node134 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,0,24⟩ = true := by decide
theorem check123_146 : t123_146.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node134 check123_134 check135_146
theorem node122 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,8,21⟩ = true := by decide
theorem check98_146 : t98_146.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node122 check98_122 check123_146
theorem check147_159 : t147_159.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check160_171 : t160_171.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node159 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,4,28⟩ = true := by decide
theorem check147_171 : t147_171.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node159 check147_159 check160_171
theorem check172_183 : t172_183.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check184_195 : t184_195.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node183 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,7,27⟩ = true := by decide
theorem check172_195 : t172_195.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node183 check172_183 check184_195
theorem node171 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,6,4⟩ = true := by decide
theorem check147_195 : t147_195.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node171 check147_171 check172_195
theorem node146 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,1,8⟩ = true := by decide
theorem check98_195 : t98_195.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node146 check98_146 check147_195
theorem node97 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,7,33⟩ = true := by decide
theorem check0_195 : t0_195.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node97 check0_97 check98_195
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_195
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M098
