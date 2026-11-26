import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M030
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_13 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,7⟩ (.node .empty ⟨0,false,0,10⟩ .empty)) ⟨0,false,2,3⟩ (.node (.node .empty ⟨0,false,2,6⟩ .empty) ⟨0,false,2,10⟩ .empty)) ⟨0,false,4,0⟩ (.node (.node (.node .empty ⟨0,false,4,3⟩ .empty) ⟨0,false,4,6⟩ (.node .empty ⟨0,false,5,0⟩ .empty)) ⟨0,false,5,3⟩ (.node (.node .empty ⟨0,false,5,6⟩ .empty) ⟨0,false,6,0⟩ .empty)))
def t14_26 : Tree := (.node (.node (.node (.node .empty ⟨0,false,6,6⟩ .empty) ⟨0,false,9,10⟩ (.node .empty ⟨0,false,11,0⟩ .empty)) ⟨0,false,11,3⟩ (.node (.node .empty ⟨0,false,11,6⟩ .empty) ⟨0,false,12,0⟩ .empty)) ⟨0,false,12,3⟩ (.node (.node (.node .empty ⟨0,false,12,6⟩ .empty) ⟨0,false,18,0⟩ .empty) ⟨0,false,18,3⟩ (.node (.node .empty ⟨0,false,18,6⟩ .empty) ⟨0,true,0,4⟩ .empty)))
def t0_26 : Tree := .node t0_13 ⟨0,false,6,3⟩ t14_26
def t27_40 : Tree := (.node (.node (.node (.node .empty ⟨0,true,1,4⟩ .empty) ⟨0,true,1,7⟩ (.node .empty ⟨0,true,2,4⟩ .empty)) ⟨0,true,2,6⟩ (.node (.node .empty ⟨0,true,2,7⟩ .empty) ⟨0,true,3,4⟩ .empty)) ⟨0,true,3,7⟩ (.node (.node (.node .empty ⟨0,true,4,4⟩ .empty) ⟨0,true,4,7⟩ (.node .empty ⟨0,true,5,4⟩ .empty)) ⟨0,true,5,7⟩ (.node (.node .empty ⟨0,true,6,4⟩ .empty) ⟨0,true,6,7⟩ .empty)))
def t41_53 : Tree := (.node (.node (.node (.node .empty ⟨0,true,8,4⟩ .empty) ⟨0,true,8,7⟩ (.node .empty ⟨0,true,9,6⟩ .empty)) ⟨0,true,10,4⟩ (.node (.node .empty ⟨0,true,10,7⟩ .empty) ⟨0,true,11,4⟩ .empty)) ⟨0,true,11,7⟩ (.node (.node (.node .empty ⟨0,true,12,4⟩ .empty) ⟨0,true,12,7⟩ .empty) ⟨0,true,15,7⟩ (.node (.node .empty ⟨0,true,18,4⟩ .empty) ⟨0,true,18,7⟩ .empty)))
def t27_53 : Tree := .node t27_40 ⟨0,true,7,7⟩ t41_53
def t0_53 : Tree := .node t0_26 ⟨0,true,0,7⟩ t27_53
def t54_67 : Tree := (.node (.node (.node (.node .empty ⟨1,false,1,6⟩ .empty) ⟨1,false,1,9⟩ (.node .empty ⟨1,false,4,0⟩ .empty)) ⟨1,false,4,1⟩ (.node (.node .empty ⟨1,false,4,5⟩ .empty) ⟨1,false,4,9⟩ .empty)) ⟨1,false,5,0⟩ (.node (.node (.node .empty ⟨1,false,5,1⟩ .empty) ⟨1,false,5,5⟩ (.node .empty ⟨1,false,6,0⟩ .empty)) ⟨1,false,6,1⟩ (.node (.node .empty ⟨1,false,6,5⟩ .empty) ⟨1,false,11,9⟩ .empty)))
def t68_80 : Tree := (.node (.node (.node (.node .empty ⟨1,false,12,1⟩ .empty) ⟨1,false,12,5⟩ (.node .empty ⟨1,false,13,0⟩ .empty)) ⟨1,false,13,1⟩ (.node (.node .empty ⟨1,false,13,5⟩ .empty) ⟨1,false,19,0⟩ .empty)) ⟨1,false,19,1⟩ (.node (.node (.node .empty ⟨1,false,19,5⟩ .empty) ⟨2,false,0,8⟩ .empty) ⟨2,false,2,0⟩ (.node (.node .empty ⟨2,false,2,5⟩ .empty) ⟨2,false,2,8⟩ .empty)))
def t54_80 : Tree := .node t54_67 ⟨1,false,12,0⟩ t68_80
def t81_93 : Tree := (.node (.node (.node (.node .empty ⟨2,false,5,0⟩ .empty) ⟨2,false,5,8⟩ (.node .empty ⟨2,false,6,0⟩ .empty)) ⟨2,false,9,0⟩ (.node (.node .empty ⟨2,false,9,1⟩ .empty) ⟨2,false,9,5⟩ .empty)) ⟨2,false,11,0⟩ (.node (.node (.node .empty ⟨2,false,12,8⟩ .empty) ⟨2,false,13,0⟩ .empty) ⟨2,false,20,0⟩ (.node (.node .empty ⟨2,true,1,4⟩ .empty) ⟨2,true,1,7⟩ .empty)))
def t94_106 : Tree := (.node (.node (.node (.node .empty ⟨2,true,2,4⟩ .empty) ⟨2,true,2,7⟩ (.node .empty ⟨2,true,4,0⟩ .empty)) ⟨2,true,4,4⟩ (.node (.node .empty ⟨2,true,4,7⟩ .empty) ⟨2,true,5,0⟩ .empty)) ⟨2,true,5,4⟩ (.node (.node (.node .empty ⟨2,true,5,7⟩ .empty) ⟨2,true,6,0⟩ .empty) ⟨2,true,6,4⟩ (.node (.node .empty ⟨2,true,6,7⟩ .empty) ⟨2,true,8,8⟩ .empty)))
def t81_106 : Tree := .node t81_93 ⟨2,true,1,8⟩ t94_106
def t54_106 : Tree := .node t54_80 ⟨2,false,4,0⟩ t81_106
def t0_106 : Tree := .node t0_53 ⟨1,false,1,0⟩ t54_106
def t107_120 : Tree := (.node (.node (.node (.node .empty ⟨2,true,9,7⟩ .empty) ⟨2,true,11,0⟩ (.node .empty ⟨2,true,11,4⟩ .empty)) ⟨2,true,11,7⟩ (.node (.node .empty ⟨2,true,13,0⟩ .empty) ⟨2,true,13,4⟩ .empty)) ⟨2,true,13,7⟩ (.node (.node (.node .empty ⟨2,true,17,4⟩ .empty) ⟨2,true,17,7⟩ (.node .empty ⟨2,true,20,0⟩ .empty)) ⟨2,true,20,4⟩ (.node (.node .empty ⟨2,true,20,7⟩ .empty) ⟨3,false,2,1⟩ .empty)))
def t121_133 : Tree := (.node (.node (.node (.node .empty ⟨3,false,4,1⟩ .empty) ⟨3,false,5,1⟩ (.node .empty ⟨3,false,6,1⟩ .empty)) ⟨3,false,7,0⟩ (.node (.node .empty ⟨3,false,9,1⟩ .empty) ⟨3,false,10,0⟩ .empty)) ⟨3,false,11,1⟩ (.node (.node (.node .empty ⟨3,false,13,1⟩ .empty) ⟨3,false,14,0⟩ .empty) ⟨3,false,20,1⟩ (.node (.node .empty ⟨3,true,0,6⟩ .empty) ⟨3,true,1,2⟩ .empty)))
def t107_133 : Tree := .node t107_120 ⟨3,false,3,0⟩ t121_133
def t134_146 : Tree := (.node (.node (.node (.node .empty ⟨3,true,3,4⟩ .empty) ⟨3,true,3,6⟩ (.node .empty ⟨3,true,3,7⟩ .empty)) ⟨3,true,4,2⟩ (.node (.node .empty ⟨3,true,5,2⟩ .empty) ⟨3,true,6,2⟩ .empty)) ⟨3,true,7,6⟩ (.node (.node (.node .empty ⟨3,true,8,2⟩ .empty) ⟨3,true,9,2⟩ .empty) ⟨3,true,10,0⟩ (.node (.node .empty ⟨3,true,10,4⟩ .empty) ⟨3,true,10,7⟩ .empty)))
def t147_159 : Tree := (.node (.node (.node (.node .empty ⟨3,true,13,2⟩ .empty) ⟨3,true,15,6⟩ (.node .empty ⟨3,true,19,2⟩ .empty)) ⟨4,false,0,5⟩ (.node (.node .empty ⟨4,false,1,5⟩ .empty) ⟨4,false,2,5⟩ .empty)) ⟨4,false,5,5⟩ (.node (.node (.node .empty ⟨4,false,8,0⟩ .empty) ⟨4,false,8,3⟩ .empty) ⟨4,false,8,5⟩ (.node (.node .empty ⟨4,false,8,6⟩ .empty) ⟨4,false,9,5⟩ .empty)))
def t134_159 : Tree := .node t134_146 ⟨3,true,12,2⟩ t147_159
def t107_159 : Tree := .node t107_133 ⟨3,true,2,2⟩ t134_159
def t160_173 : Tree := (.node (.node (.node (.node .empty ⟨4,false,16,5⟩ .empty) ⟨4,true,0,5⟩ (.node .empty ⟨4,true,1,5⟩ .empty)) ⟨4,true,1,8⟩ (.node (.node .empty ⟨4,true,2,1⟩ .empty) ⟨4,true,2,5⟩ .empty)) ⟨4,true,3,5⟩ (.node (.node (.node .empty ⟨4,true,4,1⟩ .empty) ⟨4,true,4,5⟩ (.node .empty ⟨4,true,5,1⟩ .empty)) ⟨4,true,5,5⟩ (.node (.node .empty ⟨4,true,6,1⟩ .empty) ⟨4,true,6,5⟩ .empty)))
def t174_186 : Tree := (.node (.node (.node (.node .empty ⟨4,true,9,1⟩ .empty) ⟨4,true,9,5⟩ (.node .empty ⟨4,true,10,5⟩ .empty)) ⟨4,true,11,1⟩ (.node (.node .empty ⟨4,true,11,5⟩ .empty) ⟨4,true,13,1⟩ .empty)) ⟨4,true,13,5⟩ (.node (.node (.node .empty ⟨4,true,17,5⟩ .empty) ⟨4,true,20,1⟩ .empty) ⟨4,true,20,5⟩ (.node (.node .empty ⟨5,false,0,6⟩ .empty) ⟨5,false,2,6⟩ .empty)))
def t160_186 : Tree := .node t160_173 ⟨4,true,8,8⟩ t174_186
def t187_199 : Tree := (.node (.node (.node (.node .empty ⟨5,true,0,6⟩ .empty) ⟨5,true,0,9⟩ (.node .empty ⟨5,true,1,3⟩ .empty)) ⟨5,true,1,6⟩ (.node (.node .empty ⟨5,true,2,3⟩ .empty) ⟨5,true,2,6⟩ .empty)) ⟨5,true,3,9⟩ (.node (.node (.node .empty ⟨5,true,4,3⟩ .empty) ⟨5,true,4,6⟩ .empty) ⟨5,true,5,3⟩ (.node (.node .empty ⟨5,true,5,6⟩ .empty) ⟨5,true,6,3⟩ .empty)))
def t200_212 : Tree := (.node (.node (.node (.node .empty ⟨5,true,8,3⟩ .empty) ⟨5,true,8,6⟩ (.node .empty ⟨5,true,9,3⟩ .empty)) ⟨5,true,9,6⟩ (.node (.node .empty ⟨5,true,10,9⟩ .empty) ⟨5,true,12,3⟩ .empty)) ⟨5,true,12,6⟩ (.node (.node (.node .empty ⟨5,true,13,3⟩ .empty) ⟨5,true,13,6⟩ .empty) ⟨5,true,16,6⟩ (.node (.node .empty ⟨5,true,19,3⟩ .empty) ⟨5,true,19,6⟩ .empty)))
def t187_212 : Tree := .node t187_199 ⟨5,true,6,6⟩ t200_212
def t160_212 : Tree := .node t160_186 ⟨5,false,9,6⟩ t187_212
def t107_212 : Tree := .node t107_159 ⟨4,false,12,5⟩ t160_212
def t0_212 : Tree := .node t0_106 ⟨2,true,9,4⟩ t107_212
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 4, 0, 8, 14, 5, 7, 6, 14, 4, 0, 16, 0, 9, 10, 11, 0, 8, 14, 12, 15, 13, 14, 11, 0, 0, 0, 16, 0, 17, 0, 18, 0, 19, 0, 20, 14, 18],#[0, 1, 3, 2, 0, 0, 4, 0, 0, 5, 6, 0, 7, 8, 0, 5, 9, 0, 10, 0, 0, 0],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(true,2),(true,6)],[(true,4)],[(true,5)],[(false,5)],[(true,3),(true,10)],[(true,8)],[(false,9)],[(true,9),(true,13)],[(true,11)],[(true,12)],[(false,4),(false,6),(false,11),(false,13),(false,20)],[(false,12)],[(true,7),(true,15)],[(true,16)],[(true,17),(true,20)],[(true,18)],[(true,19)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(true,4),(true,7)],[(false,5)],[(false,6)],[(true,6)],[(false,8)],[(false,9)]],
  t0_212⟩
theorem check0_13 : t0_13.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check14_26 : t14_26.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node13 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,6,3⟩ = true := by decide
theorem check0_26 : t0_26.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node13 check0_13 check14_26
theorem check27_40 : t27_40.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check41_53 : t41_53.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node40 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,7,7⟩ = true := by decide
theorem check27_53 : t27_53.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node40 check27_40 check41_53
theorem node26 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,0,7⟩ = true := by decide
theorem check0_53 : t0_53.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node26 check0_26 check27_53
theorem check54_67 : t54_67.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check68_80 : t68_80.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node67 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,12,0⟩ = true := by decide
theorem check54_80 : t54_80.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node67 check54_67 check68_80
theorem check81_93 : t81_93.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check94_106 : t94_106.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node93 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,1,8⟩ = true := by decide
theorem check81_106 : t81_106.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node93 check81_93 check94_106
theorem node80 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,4,0⟩ = true := by decide
theorem check54_106 : t54_106.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node80 check54_80 check81_106
theorem node53 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,1,0⟩ = true := by decide
theorem check0_106 : t0_106.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node53 check0_53 check54_106
theorem check107_120 : t107_120.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check121_133 : t121_133.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node120 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,3,0⟩ = true := by decide
theorem check107_133 : t107_133.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node120 check107_120 check121_133
theorem check134_146 : t134_146.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check147_159 : t147_159.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node146 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,12,2⟩ = true := by decide
theorem check134_159 : t134_159.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node146 check134_146 check147_159
theorem node133 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,2,2⟩ = true := by decide
theorem check107_159 : t107_159.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node133 check107_133 check134_159
theorem check160_173 : t160_173.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check174_186 : t174_186.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node173 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,8,8⟩ = true := by decide
theorem check160_186 : t160_186.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node173 check160_173 check174_186
theorem check187_199 : t187_199.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check200_212 : t200_212.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node199 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,6,6⟩ = true := by decide
theorem check187_212 : t187_212.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node199 check187_199 check200_212
theorem node186 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,9,6⟩ = true := by decide
theorem check160_212 : t160_212.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node186 check160_186 check187_212
theorem node159 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,12,5⟩ = true := by decide
theorem check107_212 : t107_212.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node159 check107_159 check160_212
theorem node106 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,9,4⟩ = true := by decide
theorem check0_212 : t0_212.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node106 check0_106 check107_212
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_212
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M030
