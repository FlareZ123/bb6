import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M075
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
def t0_11 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,4⟩ .empty) ⟨0,false,0,7⟩ (.node (.node .empty ⟨0,false,2,4⟩ .empty) ⟨0,false,4,4⟩ .empty)) ⟨1,false,1,0⟩ (.node (.node (.node .empty ⟨1,false,2,1⟩ .empty) ⟨1,false,2,2⟩ .empty) ⟨1,false,2,4⟩ (.node (.node .empty ⟨1,false,2,7⟩ .empty) ⟨1,false,4,1⟩ .empty)))
def t12_22 : Tree := (.node (.node (.node (.node .empty ⟨1,true,1,3⟩ .empty) ⟨1,true,1,6⟩ .empty) ⟨1,true,1,8⟩ (.node (.node .empty ⟨1,true,2,3⟩ .empty) ⟨1,true,4,3⟩ .empty)) ⟨2,false,2,0⟩ (.node (.node (.node .empty ⟨2,false,3,0⟩ .empty) ⟨2,false,3,1⟩ .empty) ⟨2,false,3,4⟩ (.node .empty ⟨2,false,5,0⟩ .empty)))
def t0_22 : Tree := .node t0_11 ⟨1,false,4,4⟩ t12_22
def t23_34 : Tree := (.node (.node (.node (.node .empty ⟨2,false,5,2⟩ .empty) ⟨2,false,5,4⟩ .empty) ⟨2,false,5,7⟩ (.node (.node .empty ⟨2,false,6,0⟩ .empty) ⟨2,true,2,0⟩ .empty)) ⟨2,true,2,3⟩ (.node (.node (.node .empty ⟨2,true,4,0⟩ .empty) ⟨2,true,4,1⟩ .empty) ⟨2,true,4,3⟩ (.node (.node .empty ⟨2,true,4,6⟩ .empty) ⟨2,true,4,8⟩ .empty)))
def t35_45 : Tree := (.node (.node (.node (.node .empty ⟨3,false,2,0⟩ .empty) ⟨3,false,2,1⟩ .empty) ⟨3,false,2,2⟩ (.node (.node .empty ⟨3,false,3,0⟩ .empty) ⟨3,false,3,1⟩ .empty)) ⟨3,false,4,0⟩ (.node (.node (.node .empty ⟨3,false,4,2⟩ .empty) ⟨3,false,4,5⟩ .empty) ⟨3,false,5,1⟩ (.node .empty ⟨3,false,5,2⟩ .empty)))
def t23_45 : Tree := .node t23_34 ⟨2,true,5,0⟩ t35_45
def t0_45 : Tree := .node t0_22 ⟨2,false,5,1⟩ t23_45
def t46_57 : Tree := (.node (.node (.node (.node .empty ⟨3,false,6,1⟩ .empty) ⟨3,false,8,0⟩ .empty) ⟨3,false,9,0⟩ (.node (.node .empty ⟨3,false,10,0⟩ .empty) ⟨3,false,13,0⟩ .empty)) ⟨3,true,1,1⟩ (.node (.node (.node .empty ⟨3,true,1,2⟩ .empty) ⟨3,true,1,3⟩ .empty) ⟨3,true,1,5⟩ (.node (.node .empty ⟨3,true,1,6⟩ .empty) ⟨3,true,1,8⟩ .empty)))
def t58_68 : Tree := (.node (.node (.node (.node .empty ⟨3,true,1,12⟩ .empty) ⟨3,true,2,0⟩ .empty) ⟨3,true,2,1⟩ (.node (.node .empty ⟨3,true,2,3⟩ .empty) ⟨3,true,2,5⟩ .empty)) ⟨3,true,2,9⟩ (.node (.node (.node .empty ⟨3,true,4,0⟩ .empty) ⟨3,true,4,1⟩ .empty) ⟨3,true,4,2⟩ (.node .empty ⟨3,true,4,3⟩ .empty)))
def t46_68 : Tree := .node t46_57 ⟨3,true,1,10⟩ t58_68
def t69_80 : Tree := (.node (.node (.node (.node .empty ⟨3,true,4,6⟩ .empty) ⟨3,true,4,8⟩ .empty) ⟨3,true,4,10⟩ (.node (.node .empty ⟨3,true,4,12⟩ .empty) ⟨3,true,6,0⟩ .empty)) ⟨3,true,6,1⟩ (.node (.node (.node .empty ⟨3,true,6,3⟩ .empty) ⟨3,true,6,6⟩ .empty) ⟨3,true,6,8⟩ (.node (.node .empty ⟨3,true,7,1⟩ .empty) ⟨3,true,8,0⟩ .empty)))
def t81_91 : Tree := (.node (.node (.node (.node .empty ⟨3,true,8,3⟩ .empty) ⟨3,true,8,6⟩ .empty) ⟨3,true,8,8⟩ (.node (.node .empty ⟨3,true,9,0⟩ .empty) ⟨3,true,9,3⟩ .empty)) ⟨3,true,11,0⟩ (.node (.node (.node .empty ⟨3,true,11,3⟩ .empty) ⟨3,true,12,1⟩ .empty) ⟨3,true,13,0⟩ (.node .empty ⟨3,true,13,3⟩ .empty)))
def t69_91 : Tree := .node t69_80 ⟨3,true,8,1⟩ t81_91
def t46_91 : Tree := .node t46_68 ⟨3,true,4,5⟩ t69_91
def t0_91 : Tree := .node t0_45 ⟨3,false,6,0⟩ t46_91
def t92_103 : Tree := (.node (.node (.node (.node .empty ⟨4,false,0,7⟩ .empty) ⟨4,false,0,11⟩ .empty) ⟨4,false,2,0⟩ (.node (.node .empty ⟨4,false,2,1⟩ .empty) ⟨4,false,2,2⟩ .empty)) ⟨4,false,2,4⟩ (.node (.node (.node .empty ⟨4,false,2,5⟩ .empty) ⟨4,false,2,7⟩ .empty) ⟨4,false,2,11⟩ (.node (.node .empty ⟨4,false,3,1⟩ .empty) ⟨4,false,3,4⟩ .empty)))
def t104_114 : Tree := (.node (.node (.node (.node .empty ⟨4,false,4,1⟩ .empty) ⟨4,false,4,4⟩ .empty) ⟨4,false,5,1⟩ (.node (.node .empty ⟨4,false,5,4⟩ .empty) ⟨4,false,7,0⟩ .empty)) ⟨4,false,7,1⟩ (.node (.node (.node .empty ⟨4,false,7,2⟩ .empty) ⟨4,false,7,4⟩ .empty) ⟨4,false,7,7⟩ (.node .empty ⟨4,false,12,0⟩ .empty)))
def t92_114 : Tree := .node t92_103 ⟨4,false,4,0⟩ t104_114
def t115_126 : Tree := (.node (.node (.node (.node .empty ⟨4,false,12,4⟩ .empty) ⟨4,true,0,1⟩ .empty) ⟨4,true,0,4⟩ (.node (.node .empty ⟨4,true,0,7⟩ .empty) ⟨4,true,1,1⟩ .empty)) ⟨4,true,1,4⟩ (.node (.node (.node .empty ⟨4,true,1,7⟩ .empty) ⟨4,true,1,11⟩ .empty) ⟨4,true,2,0⟩ (.node (.node .empty ⟨4,true,2,1⟩ .empty) ⟨4,true,2,2⟩ .empty)))
def t127_137 : Tree := (.node (.node (.node (.node .empty ⟨4,true,2,7⟩ .empty) ⟨4,true,4,0⟩ .empty) ⟨4,true,4,1⟩ (.node (.node .empty ⟨4,true,4,2⟩ .empty) ⟨4,true,4,4⟩ .empty)) ⟨4,true,4,5⟩ (.node (.node (.node .empty ⟨4,true,4,7⟩ .empty) ⟨4,true,4,11⟩ .empty) ⟨4,true,6,1⟩ (.node .empty ⟨4,true,6,4⟩ .empty)))
def t115_137 : Tree := .node t115_126 ⟨4,true,2,4⟩ t127_137
def t92_137 : Tree := .node t92_114 ⟨4,false,12,1⟩ t115_137
def t138_149 : Tree := (.node (.node (.node (.node .empty ⟨4,true,7,1⟩ .empty) ⟨4,true,7,4⟩ .empty) ⟨4,true,8,0⟩ (.node (.node .empty ⟨4,true,8,1⟩ .empty) ⟨4,true,8,4⟩ .empty)) ⟨4,true,9,1⟩ (.node (.node (.node .empty ⟨4,true,9,4⟩ .empty) ⟨4,true,11,1⟩ .empty) ⟨4,true,11,4⟩ (.node (.node .empty ⟨4,true,13,0⟩ .empty) ⟨4,true,13,1⟩ .empty)))
def t150_160 : Tree := (.node (.node (.node (.node .empty ⟨5,false,0,3⟩ .empty) ⟨5,false,0,8⟩ .empty) ⟨5,false,3,3⟩ (.node (.node .empty ⟨5,false,5,3⟩ .empty) ⟨5,true,0,3⟩ .empty)) ⟨5,true,0,8⟩ (.node (.node (.node .empty ⟨5,true,0,12⟩ .empty) ⟨5,true,1,0⟩ .empty) ⟨5,true,1,3⟩ (.node .empty ⟨5,true,1,6⟩ .empty)))
def t138_160 : Tree := .node t138_149 ⟨4,true,13,4⟩ t150_160
def t161_172 : Tree := (.node (.node (.node (.node .empty ⟨5,true,2,0⟩ .empty) ⟨5,true,2,3⟩ .empty) ⟨5,true,2,6⟩ (.node (.node .empty ⟨5,true,2,8⟩ .empty) ⟨5,true,2,10⟩ .empty)) ⟨5,true,2,12⟩ (.node (.node (.node .empty ⟨5,true,3,3⟩ .empty) ⟨5,true,4,0⟩ .empty) ⟨5,true,4,3⟩ (.node (.node .empty ⟨5,true,4,6⟩ .empty) ⟨5,true,4,8⟩ .empty)))
def t173_183 : Tree := (.node (.node (.node (.node .empty ⟨5,true,6,0⟩ .empty) ⟨5,true,6,3⟩ .empty) ⟨5,true,7,0⟩ (.node (.node .empty ⟨5,true,7,3⟩ .empty) ⟨5,true,8,0⟩ .empty)) ⟨5,true,8,3⟩ (.node (.node (.node .empty ⟨5,true,9,0⟩ .empty) ⟨5,true,9,3⟩ .empty) ⟨5,true,12,0⟩ (.node .empty ⟨5,true,12,3⟩ .empty)))
def t161_183 : Tree := .node t161_172 ⟨5,true,5,3⟩ t173_183
def t138_183 : Tree := .node t138_160 ⟨5,true,1,8⟩ t161_183
def t92_183 : Tree := .node t92_137 ⟨4,true,7,0⟩ t138_183
def t0_183 : Tree := .node t0_91 ⟨4,false,0,4⟩ t92_183
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 4, 9, 11, 5, 2, 6, 11, 10, 7, 0, 8, 0, 7, 0, 7, 0, 0, 0, 12, 0, 13, 0, 12],#[0, 1, 3, 2, 6, 5, 0, 4, 3, 0, 10, 9, 0, 7, 8, 0, 0, 7, 0, 0, 0, 11, 12, 0, 0, 11],
  #[[(false,0)],[(true,0)],[(true,1),(true,4)],[(false,2)],[(true,2)],[(false,4)],[(false,5)],[(true,6),(true,8),(true,9)],[(true,7)],[(false,3)],[(false,6)],[(true,3),(true,5)],[(true,11),(true,13)],[(true,12)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1),(false,4)],[(true,3)],[(true,2)],[(false,2)],[(true,6),(true,8)],[(false,7)],[(true,5)],[(false,5)],[(true,10),(true,12)],[(false,11)]],
  t0_183⟩
theorem check0_11 : t0_11.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check12_22 : t12_22.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node11 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,4,4⟩ = true := by decide
theorem check0_22 : t0_22.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node11 check0_11 check12_22
theorem check23_34 : t23_34.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check35_45 : t35_45.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node34 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,5,0⟩ = true := by decide
theorem check23_45 : t23_45.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node34 check23_34 check35_45
theorem node22 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,5,1⟩ = true := by decide
theorem check0_45 : t0_45.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node22 check0_22 check23_45
theorem check46_57 : t46_57.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check58_68 : t58_68.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node57 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,1,10⟩ = true := by decide
theorem check46_68 : t46_68.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node57 check46_57 check58_68
theorem check69_80 : t69_80.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check81_91 : t81_91.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node80 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,8,1⟩ = true := by decide
theorem check69_91 : t69_91.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node80 check69_80 check81_91
theorem node68 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,4,5⟩ = true := by decide
theorem check46_91 : t46_91.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node68 check46_68 check69_91
theorem node45 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,6,0⟩ = true := by decide
theorem check0_91 : t0_91.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node45 check0_45 check46_91
theorem check92_103 : t92_103.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check104_114 : t104_114.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node103 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,4,0⟩ = true := by decide
theorem check92_114 : t92_114.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node103 check92_103 check104_114
theorem check115_126 : t115_126.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check127_137 : t127_137.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node126 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,2,4⟩ = true := by decide
theorem check115_137 : t115_137.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node126 check115_126 check127_137
theorem node114 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,12,1⟩ = true := by decide
theorem check92_137 : t92_137.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node114 check92_114 check115_137
theorem check138_149 : t138_149.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check150_160 : t150_160.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node149 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,13,4⟩ = true := by decide
theorem check138_160 : t138_160.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node149 check138_149 check150_160
theorem check161_172 : t161_172.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check173_183 : t173_183.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node172 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,5,3⟩ = true := by decide
theorem check161_183 : t161_183.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node172 check161_172 check173_183
theorem node160 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,1,8⟩ = true := by decide
theorem check138_183 : t138_183.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node160 check138_160 check161_183
theorem node137 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,7,0⟩ = true := by decide
theorem check92_183 : t92_183.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node137 check92_137 check138_183
theorem node91 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,0,4⟩ = true := by decide
theorem check0_183 : t0_183.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node91 check0_91 check92_183
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_183
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M075
