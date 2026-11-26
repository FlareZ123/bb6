import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M015
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_9 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,11⟩ .empty) ⟨0,false,2,17⟩ (.node .empty ⟨0,false,6,22⟩ .empty)) ⟨0,false,10,0⟩ (.node (.node (.node .empty ⟨0,false,10,11⟩ .empty) ⟨0,false,10,32⟩ .empty) ⟨0,false,14,17⟩ (.node .empty ⟨0,true,0,4⟩ .empty)))
def t10_19 : Tree := (.node (.node (.node (.node .empty ⟨0,true,10,4⟩ .empty) ⟨0,true,17,24⟩ .empty) ⟨1,false,0,8⟩ (.node .empty ⟨1,false,1,0⟩ .empty)) ⟨1,false,1,10⟩ (.node (.node (.node .empty ⟨1,false,2,13⟩ .empty) ⟨1,false,5,16⟩ .empty) ⟨1,false,6,18⟩ (.node .empty ⟨1,false,9,21⟩ .empty)))
def t0_19 : Tree := .node t0_9 ⟨0,true,5,24⟩ t10_19
def t20_29 : Tree := (.node (.node (.node (.node .empty ⟨1,false,10,28⟩ .empty) ⟨1,false,13,0⟩ .empty) ⟨1,false,13,10⟩ (.node .empty ⟨1,false,13,31⟩ .empty)) ⟨1,false,14,13⟩ (.node (.node (.node .empty ⟨1,false,14,34⟩ .empty) ⟨1,false,17,16⟩ .empty) ⟨1,true,0,8⟩ (.node .empty ⟨1,true,0,15⟩ .empty)))
def t30_38 : Tree := (.node (.node (.node (.node .empty ⟨1,true,2,20⟩ .empty) ⟨1,true,6,18⟩ .empty) ⟨1,true,6,30⟩ (.node .empty ⟨1,true,10,8⟩ .empty)) ⟨1,true,10,15⟩ (.node (.node .empty ⟨1,true,10,28⟩ .empty) ⟨1,true,14,13⟩ (.node .empty ⟨1,true,14,20⟩ .empty)))
def t20_38 : Tree := .node t20_29 ⟨1,true,2,13⟩ t30_38
def t0_38 : Tree := .node t0_19 ⟨1,false,10,8⟩ t20_38
def t39_48 : Tree := (.node (.node (.node (.node .empty ⟨2,false,0,6⟩ .empty) ⟨2,false,0,9⟩ .empty) ⟨2,false,2,0⟩ (.node .empty ⟨2,false,2,7⟩ .empty)) ⟨2,false,2,14⟩ (.node (.node (.node .empty ⟨2,false,2,35⟩ .empty) ⟨2,false,6,12⟩ .empty) ⟨2,false,6,19⟩ (.node .empty ⟨2,false,6,33⟩ .empty)))
def t49_58 : Tree := (.node (.node (.node (.node .empty ⟨2,false,10,6⟩ .empty) ⟨2,false,10,9⟩ .empty) ⟨2,false,10,26⟩ (.node .empty ⟨2,false,10,29⟩ .empty)) ⟨2,false,14,0⟩ (.node (.node (.node .empty ⟨2,false,14,7⟩ .empty) ⟨2,false,14,14⟩ .empty) ⟨2,false,14,27⟩ (.node .empty ⟨2,false,14,35⟩ .empty)))
def t39_58 : Tree := .node t39_48 ⟨2,false,10,2⟩ t49_58
def t59_68 : Tree := (.node (.node (.node (.node .empty ⟨2,true,1,7⟩ .empty) ⟨2,true,1,14⟩ .empty) ⟨2,true,3,12⟩ (.node .empty ⟨2,true,5,12⟩ .empty)) ⟨2,true,5,19⟩ (.node (.node (.node .empty ⟨2,true,7,2⟩ .empty) ⟨2,true,7,6⟩ .empty) ⟨2,true,7,26⟩ (.node .empty ⟨2,true,9,2⟩ .empty)))
def t69_77 : Tree := (.node (.node (.node (.node .empty ⟨2,true,9,9⟩ .empty) ⟨2,true,9,26⟩ .empty) ⟨2,true,9,29⟩ (.node .empty ⟨2,true,11,7⟩ .empty)) ⟨2,true,11,27⟩ (.node (.node .empty ⟨2,true,13,7⟩ .empty) ⟨2,true,13,14⟩ (.node .empty ⟨2,true,13,27⟩ .empty)))
def t59_77 : Tree := .node t59_68 ⟨2,true,9,6⟩ t69_77
def t39_77 : Tree := .node t39_58 ⟨2,true,0,7⟩ t59_77
def t0_77 : Tree := .node t0_38 ⟨1,true,14,34⟩ t39_77
def t78_87 : Tree := (.node (.node (.node (.node .empty ⟨2,true,15,12⟩ .empty) ⟨2,true,15,33⟩ .empty) ⟨2,true,17,12⟩ (.node .empty ⟨2,true,17,19⟩ .empty)) ⟨2,true,17,33⟩ (.node (.node (.node .empty ⟨3,false,2,1⟩ .empty) ⟨3,false,3,0⟩ .empty) ⟨3,false,14,1⟩ (.node .empty ⟨3,false,15,0⟩ .empty)))
def t88_97 : Tree := (.node (.node (.node (.node .empty ⟨3,true,0,8⟩ .empty) ⟨3,true,0,15⟩ .empty) ⟨3,true,1,2⟩ (.node .empty ⟨3,true,3,4⟩ .empty)) ⟨3,true,3,13⟩ (.node (.node (.node .empty ⟨3,true,3,20⟩ .empty) ⟨3,true,3,34⟩ .empty) ⟨3,true,7,3⟩ (.node .empty ⟨3,true,7,18⟩ .empty)))
def t78_97 : Tree := .node t78_87 ⟨3,true,0,5⟩ t88_97
def t98_107 : Tree := (.node (.node (.node (.node .empty ⟨3,true,7,30⟩ .empty) ⟨3,true,11,1⟩ .empty) ⟨3,true,11,5⟩ (.node .empty ⟨3,true,11,8⟩ .empty)) ⟨3,true,11,15⟩ (.node (.node (.node .empty ⟨3,true,11,25⟩ .empty) ⟨3,true,11,28⟩ .empty) ⟨3,true,13,2⟩ (.node .empty ⟨3,true,15,4⟩ .empty)))
def t108_116 : Tree := (.node (.node (.node (.node .empty ⟨3,true,15,20⟩ .empty) ⟨3,true,15,24⟩ .empty) ⟨3,true,15,34⟩ (.node .empty ⟨4,false,0,5⟩ .empty)) ⟨4,false,1,4⟩ (.node (.node .empty ⟨4,false,4,3⟩ .empty) ⟨4,false,8,1⟩ (.node .empty ⟨4,false,8,5⟩ .empty)))
def t98_116 : Tree := .node t98_107 ⟨3,true,15,13⟩ t108_116
def t78_116 : Tree := .node t78_97 ⟨3,true,7,23⟩ t98_116
def t117_126 : Tree := (.node (.node (.node (.node .empty ⟨4,false,12,4⟩ .empty) ⟨4,false,12,24⟩ .empty) ⟨4,false,16,3⟩ (.node .empty ⟨4,false,16,23⟩ .empty)) ⟨4,true,1,7⟩ (.node (.node (.node .empty ⟨4,true,1,14⟩ .empty) ⟨4,true,1,35⟩ .empty) ⟨4,true,2,1⟩ (.node .empty ⟨4,true,2,25⟩ .empty)))
def t127_136 : Tree := (.node (.node (.node (.node .empty ⟨4,true,4,19⟩ .empty) ⟨4,true,4,33⟩ .empty) ⟨4,true,8,2⟩ (.node .empty ⟨4,true,8,6⟩ .empty)) ⟨4,true,8,9⟩ (.node (.node (.node .empty ⟨4,true,8,26⟩ .empty) ⟨4,true,8,29⟩ .empty) ⟨4,true,9,5⟩ (.node .empty ⟨4,true,12,0⟩ .empty)))
def t117_136 : Tree := .node t117_126 ⟨4,true,4,12⟩ t127_136
def t137_146 : Tree := (.node (.node (.node (.node .empty ⟨4,true,12,14⟩ .empty) ⟨4,true,12,27⟩ .empty) ⟨4,true,12,35⟩ (.node .empty ⟨4,true,14,1⟩ .empty)) ⟨4,true,14,25⟩ (.node (.node (.node .empty ⟨4,true,16,12⟩ .empty) ⟨4,true,16,19⟩ .empty) ⟨4,true,16,33⟩ (.node .empty ⟨5,true,0,10⟩ .empty)))
def t147_155 : Tree := (.node (.node (.node (.node .empty ⟨5,true,3,16⟩ .empty) ⟨5,true,6,23⟩ .empty) ⟨5,true,7,21⟩ (.node .empty ⟨5,true,11,0⟩ .empty)) ⟨5,true,11,10⟩ (.node (.node .empty ⟨5,true,11,31⟩ .empty) ⟨5,true,13,3⟩ (.node .empty ⟨5,true,15,16⟩ .empty)))
def t137_155 : Tree := .node t137_146 ⟨5,true,1,3⟩ t147_155
def t117_155 : Tree := .node t117_136 ⟨4,true,12,7⟩ t137_155
def t78_155 : Tree := .node t78_116 ⟨4,false,8,25⟩ t117_155
def t0_155 : Tree := .node t0_77 ⟨2,true,13,35⟩ t78_155
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 5, 0, 4, 0, 0, 0, 6, 7, 9, 0, 8, 0, 0, 0, 10, 11, 13, 0, 12, 0, 0, 0, 14, 15, 17, 0, 16, 0, 0, 0, 6],#[0, 1, 3, 2, 21, 18, 4, 12, 5, 7, 23, 6, 21, 18, 10, 8, 0, 9, 21, 30, 11, 0, 0, 0, 16, 13, 0, 14, 10, 15, 0, 9, 17, 0, 0, 0, 0, 19, 16, 20, 0, 14, 22, 0, 0, 0, 24, 33, 25, 27, 3, 26, 21, 18, 31, 28, 0, 29, 21, 30, 0, 19, 32, 0, 0, 0, 16, 34, 0, 35, 10, 15],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(true,3)],[(true,2)],[(true,5),(true,17)],[(false,6)],[(true,7)],[(true,6)],[(true,9)],[(false,10)],[(true,11)],[(true,10)],[(true,13)],[(false,14)],[(true,15)],[(true,14)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1),(false,25)],[(false,3)],[(false,4)],[(true,5)],[(true,4)],[(true,7)],[(true,8),(true,15)],[(false,7),(false,14),(false,35)],[(false,10)],[(true,3)],[(true,12)],[(true,13),(true,20)],[(true,14),(true,35)],[(false,12),(false,19),(false,33)],[(false,16)],[(true,2),(true,6),(true,26)],[(true,18),(true,30)],[(true,19)],[(false,2),(false,6),(false,9),(false,26),(false,29)],[(false,21)],[(false,5)],[(false,23)],[(false,24)],[(true,25)],[(true,24)],[(true,27)],[(true,28)],[(true,9),(true,29)],[(false,27)],[(false,31)],[(true,23)],[(true,33)],[(true,34)]],
  t0_155⟩
theorem check0_9 : t0_9.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check10_19 : t10_19.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node9 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,5,24⟩ = true := by decide
theorem check0_19 : t0_19.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node9 check0_9 check10_19
theorem check20_29 : t20_29.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check30_38 : t30_38.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node29 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,2,13⟩ = true := by decide
theorem check20_38 : t20_38.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node29 check20_29 check30_38
theorem node19 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,10,8⟩ = true := by decide
theorem check0_38 : t0_38.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node19 check0_19 check20_38
theorem check39_48 : t39_48.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check49_58 : t49_58.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node48 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,10,2⟩ = true := by decide
theorem check39_58 : t39_58.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node48 check39_48 check49_58
theorem check59_68 : t59_68.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check69_77 : t69_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node68 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,9,6⟩ = true := by decide
theorem check59_77 : t59_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node68 check59_68 check69_77
theorem node58 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,0,7⟩ = true := by decide
theorem check39_77 : t39_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node58 check39_58 check59_77
theorem node38 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,14,34⟩ = true := by decide
theorem check0_77 : t0_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node38 check0_38 check39_77
theorem check78_87 : t78_87.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check88_97 : t88_97.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node87 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,0,5⟩ = true := by decide
theorem check78_97 : t78_97.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node87 check78_87 check88_97
theorem check98_107 : t98_107.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check108_116 : t108_116.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node107 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,15,13⟩ = true := by decide
theorem check98_116 : t98_116.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node107 check98_107 check108_116
theorem node97 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,7,23⟩ = true := by decide
theorem check78_116 : t78_116.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node97 check78_97 check98_116
theorem check117_126 : t117_126.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check127_136 : t127_136.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node126 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,4,12⟩ = true := by decide
theorem check117_136 : t117_136.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node126 check117_126 check127_136
theorem check137_146 : t137_146.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check147_155 : t147_155.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node146 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,1,3⟩ = true := by decide
theorem check137_155 : t137_155.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node146 check137_146 check147_155
theorem node136 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,12,7⟩ = true := by decide
theorem check117_155 : t117_155.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node136 check117_136 check137_155
theorem node116 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,8,25⟩ = true := by decide
theorem check78_155 : t78_155.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node116 check78_116 check117_155
theorem node77 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,13,35⟩ = true := by decide
theorem check0_155 : t0_155.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node77 check0_77 check78_155
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_155
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M015
