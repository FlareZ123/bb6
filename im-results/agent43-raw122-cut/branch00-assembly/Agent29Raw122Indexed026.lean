import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M026
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_13 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,5⟩ (.node .empty ⟨0,false,0,10⟩ .empty)) ⟨0,false,0,20⟩ (.node (.node .empty ⟨0,false,0,23⟩ .empty) ⟨0,false,0,29⟩ .empty)) ⟨0,false,0,32⟩ (.node (.node (.node .empty ⟨0,false,2,10⟩ .empty) ⟨0,false,2,17⟩ (.node .empty ⟨0,false,2,20⟩ .empty)) ⟨0,false,2,28⟩ (.node (.node .empty ⟨0,false,2,32⟩ .empty) ⟨0,false,5,14⟩ .empty)))
def t14_26 : Tree := (.node (.node (.node (.node .empty ⟨0,false,6,10⟩ .empty) ⟨0,false,6,13⟩ (.node .empty ⟨0,false,6,28⟩ .empty)) ⟨0,false,12,0⟩ (.node (.node .empty ⟨0,false,12,17⟩ .empty) ⟨0,false,14,14⟩ .empty)) ⟨0,false,14,23⟩ (.node (.node (.node .empty ⟨0,false,20,10⟩ .empty) ⟨0,false,20,17⟩ .empty) ⟨0,false,20,20⟩ (.node (.node .empty ⟨0,false,20,28⟩ .empty) ⟨0,false,20,32⟩ .empty)))
def t0_26 : Tree := .node t0_13 ⟨0,false,5,23⟩ t14_26
def t27_39 : Tree := (.node (.node (.node (.node .empty ⟨0,false,22,23⟩ .empty) ⟨0,true,0,4⟩ (.node .empty ⟨0,true,0,22⟩ .empty)) ⟨0,true,0,26⟩ (.node (.node .empty ⟨0,true,0,30⟩ .empty) ⟨0,true,1,21⟩ .empty)) ⟨0,true,1,23⟩ (.node (.node (.node .empty ⟨0,true,1,29⟩ .empty) ⟨0,true,2,20⟩ .empty) ⟨0,true,2,22⟩ (.node (.node .empty ⟨0,true,2,26⟩ .empty) ⟨0,true,2,30⟩ .empty)))
def t40_52 : Tree := (.node (.node (.node (.node .empty ⟨0,true,6,22⟩ .empty) ⟨0,true,11,5⟩ (.node .empty ⟨0,true,11,21⟩ .empty)) ⟨0,true,12,4⟩ (.node (.node .empty ⟨0,true,12,20⟩ .empty) ⟨0,true,19,21⟩ .empty)) ⟨0,true,19,23⟩ (.node (.node (.node .empty ⟨0,true,19,29⟩ .empty) ⟨0,true,20,20⟩ .empty) ⟨0,true,20,22⟩ (.node (.node .empty ⟨0,true,20,26⟩ .empty) ⟨0,true,20,30⟩ .empty)))
def t27_52 : Tree := .node t27_39 ⟨0,true,6,8⟩ t40_52
def t0_52 : Tree := .node t0_26 ⟨0,false,22,14⟩ t27_52
def t53_65 : Tree := (.node (.node (.node (.node .empty ⟨1,false,1,9⟩ .empty) ⟨1,false,1,19⟩ (.node .empty ⟨1,false,1,31⟩ .empty)) ⟨1,false,11,9⟩ (.node (.node .empty ⟨1,false,11,12⟩ .empty) ⟨1,false,11,27⟩ .empty)) ⟨1,false,15,0⟩ (.node (.node (.node .empty ⟨1,false,15,16⟩ .empty) ⟨1,false,15,25⟩ .empty) ⟨1,false,19,9⟩ (.node (.node .empty ⟨1,false,19,16⟩ .empty) ⟨1,false,19,19⟩ .empty)))
def t66_78 : Tree := (.node (.node (.node (.node .empty ⟨1,false,19,27⟩ .empty) ⟨1,false,19,31⟩ (.node .empty ⟨1,true,1,4⟩ .empty)) ⟨1,true,1,22⟩ (.node (.node .empty ⟨1,true,1,26⟩ .empty) ⟨1,true,1,30⟩ .empty)) ⟨1,true,18,8⟩ (.node (.node (.node .empty ⟨1,true,18,22⟩ .empty) ⟨2,false,1,6⟩ .empty) ⟨2,false,1,24⟩ (.node (.node .empty ⟨2,false,2,0⟩ .empty) ⟨2,false,2,5⟩ .empty)))
def t53_78 : Tree := .node t53_65 ⟨1,false,19,25⟩ t66_78
def t79_91 : Tree := (.node (.node (.node (.node .empty ⟨2,false,2,23⟩ .empty) ⟨2,false,2,29⟩ (.node .empty ⟨2,false,6,1⟩ .empty)) ⟨2,false,6,14⟩ (.node (.node .empty ⟨2,false,6,23⟩ .empty) ⟨2,false,9,0⟩ .empty)) ⟨2,false,12,2⟩ (.node (.node (.node .empty ⟨2,false,12,5⟩ .empty) ⟨2,false,12,21⟩ .empty) ⟨2,false,16,0⟩ (.node (.node .empty ⟨2,false,16,15⟩ .empty) ⟨2,false,16,24⟩ .empty)))
def t92_104 : Tree := (.node (.node (.node (.node .empty ⟨2,false,20,14⟩ .empty) ⟨2,false,20,15⟩ (.node .empty ⟨2,false,20,21⟩ .empty)) ⟨2,false,20,23⟩ (.node (.node .empty ⟨2,false,20,24⟩ .empty) ⟨2,false,20,29⟩ .empty)) ⟨3,false,1,5⟩ (.node (.node (.node .empty ⟨3,false,1,23⟩ .empty) ⟨3,false,1,29⟩ .empty) ⟨3,false,2,1⟩ (.node (.node .empty ⟨3,false,3,0⟩ .empty) ⟨3,false,4,4⟩ .empty)))
def t79_104 : Tree := .node t79_91 ⟨2,false,20,5⟩ t92_104
def t53_104 : Tree := .node t53_78 ⟨2,false,2,14⟩ t79_104
def t0_104 : Tree := .node t0_52 ⟨1,false,1,0⟩ t53_104
def t105_118 : Tree := (.node (.node (.node (.node .empty ⟨3,false,4,26⟩ .empty) ⟨3,false,4,30⟩ (.node .empty ⟨3,false,8,2⟩ .empty)) ⟨3,false,9,1⟩ (.node (.node .empty ⟨3,false,10,0⟩ .empty) ⟨3,false,16,1⟩ .empty)) ⟨3,false,16,14⟩ (.node (.node (.node .empty ⟨3,false,16,23⟩ .empty) ⟨3,false,17,0⟩ (.node .empty ⟨3,false,17,8⟩ .empty)) ⟨3,false,17,22⟩ (.node (.node .empty ⟨3,false,20,14⟩ .empty) ⟨3,false,20,23⟩ .empty)))
def t119_131 : Tree := (.node (.node (.node (.node .empty ⟨3,false,21,22⟩ .empty) ⟨3,true,0,8⟩ (.node .empty ⟨3,true,0,26⟩ .empty)) ⟨3,true,0,30⟩ (.node (.node .empty ⟨3,true,1,2⟩ .empty) ⟨3,true,3,4⟩ .empty)) ⟨3,true,3,8⟩ (.node (.node (.node .empty ⟨3,true,3,22⟩ .empty) ⟨3,true,3,26⟩ .empty) ⟨3,true,3,30⟩ (.node (.node .empty ⟨3,true,7,0⟩ .empty) ⟨3,true,7,8⟩ .empty)))
def t105_131 : Tree := .node t105_118 ⟨3,false,21,8⟩ t119_131
def t132_144 : Tree := (.node (.node (.node (.node .empty ⟨3,true,7,22⟩ .empty) ⟨3,true,13,1⟩ (.node .empty ⟨3,true,13,4⟩ .empty)) ⟨3,true,13,20⟩ (.node (.node .empty ⟨3,true,15,2⟩ .empty) ⟨3,true,15,18⟩ .empty)) ⟨3,true,15,26⟩ (.node (.node (.node .empty ⟨3,true,19,18⟩ .empty) ⟨3,true,19,26⟩ .empty) ⟨3,true,21,4⟩ (.node (.node .empty ⟨3,true,21,8⟩ .empty) ⟨3,true,21,20⟩ .empty)))
def t145_157 : Tree := (.node (.node (.node (.node .empty ⟨3,true,21,26⟩ .empty) ⟨3,true,21,30⟩ (.node .empty ⟨4,false,5,3⟩ .empty)) ⟨4,false,8,0⟩ (.node (.node .empty ⟨4,false,14,3⟩ .empty) ⟨4,false,14,19⟩ .empty)) ⟨4,false,22,3⟩ (.node (.node (.node .empty ⟨4,false,22,19⟩ .empty) ⟨4,true,0,6⟩ .empty) ⟨4,true,0,24⟩ (.node (.node .empty ⟨4,true,1,5⟩ .empty) ⟨4,true,1,23⟩ .empty)))
def t132_157 : Tree := .node t132_144 ⟨3,true,21,22⟩ t145_157
def t105_157 : Tree := .node t105_131 ⟨3,true,7,11⟩ t132_157
def t158_170 : Tree := (.node (.node (.node (.node .empty ⟨4,true,2,1⟩ .empty) ⟨4,true,5,5⟩ (.node .empty ⟨4,true,5,15⟩ .empty)) ⟨4,true,5,21⟩ (.node (.node .empty ⟨4,true,5,23⟩ .empty) ⟨4,true,5,24⟩ .empty)) ⟨4,true,5,29⟩ (.node (.node (.node .empty ⟨4,true,8,2⟩ .empty) ⟨4,true,8,5⟩ .empty) ⟨4,true,8,21⟩ (.node (.node .empty ⟨4,true,14,0⟩ .empty) ⟨4,true,14,15⟩ .empty)))
def t171_183 : Tree := (.node (.node (.node (.node .empty ⟨4,true,16,1⟩ .empty) ⟨4,true,16,14⟩ (.node .empty ⟨4,true,16,23⟩ .empty)) ⟨4,true,20,14⟩ (.node (.node .empty ⟨4,true,20,23⟩ .empty) ⟨4,true,22,5⟩ .empty)) ⟨4,true,22,15⟩ (.node (.node (.node .empty ⟨4,true,22,21⟩ .empty) ⟨4,true,22,23⟩ .empty) ⟨4,true,22,24⟩ (.node (.node .empty ⟨4,true,22,29⟩ .empty) ⟨5,false,0,7⟩ .empty)))
def t158_183 : Tree := .node t158_170 ⟨4,true,14,24⟩ t171_183
def t184_196 : Tree := (.node (.node (.node (.node .empty ⟨5,true,0,9⟩ .empty) ⟨5,true,0,19⟩ (.node .empty ⟨5,true,0,31⟩ .empty)) ⟨5,true,1,3⟩ (.node (.node .empty ⟨5,true,3,9⟩ .empty) ⟨5,true,3,16⟩ .empty)) ⟨5,true,3,19⟩ (.node (.node (.node .empty ⟨5,true,3,25⟩ .empty) ⟨5,true,3,27⟩ .empty) ⟨5,true,3,31⟩ (.node (.node .empty ⟨5,true,7,9⟩ .empty) ⟨5,true,7,12⟩ .empty)))
def t197_209 : Tree := (.node (.node (.node (.node .empty ⟨5,true,13,0⟩ .empty) ⟨5,true,13,16⟩ (.node .empty ⟨5,true,13,25⟩ .empty)) ⟨5,true,15,3⟩ (.node (.node .empty ⟨5,true,15,19⟩ .empty) ⟨5,true,19,19⟩ .empty)) ⟨5,true,21,9⟩ (.node (.node (.node .empty ⟨5,true,21,16⟩ .empty) ⟨5,true,21,19⟩ .empty) ⟨5,true,21,25⟩ (.node (.node .empty ⟨5,true,21,27⟩ .empty) ⟨5,true,21,31⟩ .empty)))
def t184_209 : Tree := .node t184_196 ⟨5,true,7,27⟩ t197_209
def t158_209 : Tree := .node t158_183 ⟨5,false,0,25⟩ t184_209
def t105_209 : Tree := .node t105_157 ⟨4,true,1,29⟩ t158_209
def t0_209 : Tree := .node t0_104 ⟨3,false,4,22⟩ t105_209
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 19, 0, 5, 0, 0, 6, 18, 7, 11, 0, 8, 9, 0, 10, 0, 0, 0, 0, 12, 13, 15, 0, 14, 6, 18, 0, 16, 17, 0, 0, 0, 0, 0, 0, 20, 21, 19, 0, 22, 6, 18],#[0, 1, 3, 2, 12, 11, 4, 0, 6, 5, 9, 8, 7, 0, 0, 0, 15, 14, 10, 0, 0, 0, 0, 0, 13, 0, 0, 0, 19, 18, 16, 0, 17, 0, 0, 0, 0, 0, 20, 0, 0, 21, 27, 22, 24, 23, 19, 26, 25, 0, 17, 0, 6, 29, 28, 0, 0, 0, 31, 30, 6, 29, 32, 0, 0, 0],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,3)],[(false,5),(false,14),(false,22)],[(false,6)],[(true,7)],[(false,8)],[(false,9)],[(true,6)],[(true,11)],[(false,12)],[(true,13)],[(true,12)],[(true,15)],[(false,16)],[(true,5),(true,14),(true,22)],[(true,2),(true,20)],[(true,19)],[(false,20)],[(true,21)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(true,4)],[(false,4),(false,26),(false,30)],[(false,6)],[(true,5)],[(false,5)],[(false,9)],[(true,2)],[(false,2)],[(false,12)],[(true,8)],[(false,8)],[(false,15)],[(false,16),(false,25)],[(true,14)],[(false,14),(false,23)],[(false,19)],[(true,20)],[(true,21)],[(true,22)],[(false,22)],[(false,24)],[(true,23)],[(false,21)],[(false,27)],[(true,26),(true,30)],[(true,29)],[(false,29)],[(false,31)]],
  t0_209⟩
theorem check0_13 : t0_13.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check14_26 : t14_26.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node13 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,5,23⟩ = true := by decide
theorem check0_26 : t0_26.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node13 check0_13 check14_26
theorem check27_39 : t27_39.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check40_52 : t40_52.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node39 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,6,8⟩ = true := by decide
theorem check27_52 : t27_52.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node39 check27_39 check40_52
theorem node26 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,22,14⟩ = true := by decide
theorem check0_52 : t0_52.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node26 check0_26 check27_52
theorem check53_65 : t53_65.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check66_78 : t66_78.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node65 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,19,25⟩ = true := by decide
theorem check53_78 : t53_78.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node65 check53_65 check66_78
theorem check79_91 : t79_91.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check92_104 : t92_104.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node91 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,20,5⟩ = true := by decide
theorem check79_104 : t79_104.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node91 check79_91 check92_104
theorem node78 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,2,14⟩ = true := by decide
theorem check53_104 : t53_104.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node78 check53_78 check79_104
theorem node52 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,1,0⟩ = true := by decide
theorem check0_104 : t0_104.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node52 check0_52 check53_104
theorem check105_118 : t105_118.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check119_131 : t119_131.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node118 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,21,8⟩ = true := by decide
theorem check105_131 : t105_131.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node118 check105_118 check119_131
theorem check132_144 : t132_144.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check145_157 : t145_157.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node144 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,21,22⟩ = true := by decide
theorem check132_157 : t132_157.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node144 check132_144 check145_157
theorem node131 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,7,11⟩ = true := by decide
theorem check105_157 : t105_157.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node131 check105_131 check132_157
theorem check158_170 : t158_170.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check171_183 : t171_183.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node170 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,14,24⟩ = true := by decide
theorem check158_183 : t158_183.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node170 check158_170 check171_183
theorem check184_196 : t184_196.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check197_209 : t197_209.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node196 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,7,27⟩ = true := by decide
theorem check184_209 : t184_209.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node196 check184_196 check197_209
theorem node183 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,0,25⟩ = true := by decide
theorem check158_209 : t158_209.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node183 check158_183 check184_209
theorem node157 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,1,29⟩ = true := by decide
theorem check105_209 : t105_209.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node157 check105_157 check158_209
theorem node104 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,4,22⟩ = true := by decide
theorem check0_209 : t0_209.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node104 check0_104 check105_209
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_209
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M026
