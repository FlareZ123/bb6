import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M074
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
def t0_12 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,9,0⟩ (.node .empty ⟨0,false,9,1⟩ .empty)) ⟨0,false,9,4⟩ (.node (.node .empty ⟨0,false,9,8⟩ .empty) ⟨0,false,9,9⟩ .empty)) ⟨0,false,12,0⟩ (.node (.node (.node .empty ⟨0,false,12,4⟩ .empty) ⟨0,false,12,8⟩ .empty) ⟨1,false,0,5⟩ (.node (.node .empty ⟨1,false,1,0⟩ .empty) ⟨1,false,6,7⟩ .empty)))
def t13_25 : Tree := (.node (.node (.node (.node .empty ⟨1,false,7,1⟩ .empty) ⟨1,false,7,4⟩ (.node .empty ⟨1,false,7,7⟩ .empty)) ⟨1,false,7,9⟩ (.node (.node .empty ⟨1,false,7,14⟩ .empty) ⟨1,false,10,1⟩ .empty)) ⟨1,false,10,9⟩ (.node (.node (.node .empty ⟨1,false,10,14⟩ .empty) ⟨1,false,13,0⟩ .empty) ⟨1,false,13,7⟩ (.node (.node .empty ⟨1,false,16,0⟩ .empty) ⟨1,false,16,7⟩ .empty)))
def t0_25 : Tree := .node t0_12 ⟨1,false,7,0⟩ t13_25
def t26_38 : Tree := (.node (.node (.node (.node .empty ⟨1,false,17,1⟩ .empty) ⟨1,false,17,4⟩ (.node .empty ⟨1,false,17,7⟩ .empty)) ⟨1,false,17,9⟩ (.node (.node .empty ⟨1,false,17,14⟩ .empty) ⟨1,false,18,1⟩ .empty)) ⟨1,false,18,7⟩ (.node (.node (.node .empty ⟨1,false,18,9⟩ .empty) ⟨1,false,18,14⟩ .empty) ⟨1,true,6,0⟩ (.node (.node .empty ⟨1,true,6,3⟩ .empty) ⟨1,true,6,5⟩ .empty)))
def t39_51 : Tree := (.node (.node (.node (.node .empty ⟨1,true,6,15⟩ .empty) ⟨1,true,7,3⟩ (.node .empty ⟨1,true,7,11⟩ .empty)) ⟨1,true,7,15⟩ (.node (.node .empty ⟨1,true,13,3⟩ .empty) ⟨1,true,13,11⟩ .empty)) ⟨1,true,13,15⟩ (.node (.node (.node .empty ⟨1,true,16,0⟩ .empty) ⟨1,true,16,3⟩ .empty) ⟨1,true,16,5⟩ (.node (.node .empty ⟨1,true,16,11⟩ .empty) ⟨1,true,16,15⟩ .empty)))
def t26_51 : Tree := .node t26_38 ⟨1,true,6,11⟩ t39_51
def t0_51 : Tree := .node t0_25 ⟨1,false,17,0⟩ t26_51
def t52_64 : Tree := (.node (.node (.node (.node .empty ⟨1,true,17,11⟩ .empty) ⟨1,true,17,15⟩ (.node .empty ⟨1,true,18,3⟩ .empty)) ⟨1,true,18,11⟩ (.node (.node .empty ⟨1,true,18,15⟩ .empty) ⟨2,false,1,4⟩ .empty)) ⟨2,false,2,0⟩ (.node (.node (.node .empty ⟨2,false,8,0⟩ .empty) ⟨2,false,8,6⟩ .empty) ⟨2,false,8,13⟩ (.node (.node .empty ⟨2,false,14,0⟩ .empty) ⟨2,false,14,6⟩ .empty)))
def t65_77 : Tree := (.node (.node (.node (.node .empty ⟨2,false,19,6⟩ .empty) ⟨2,false,19,13⟩ (.node .empty ⟨2,true,8,0⟩ .empty)) ⟨2,true,8,3⟩ (.node (.node .empty ⟨2,true,8,5⟩ .empty) ⟨2,true,8,11⟩ .empty)) ⟨2,true,8,12⟩ (.node (.node (.node .empty ⟨2,true,11,0⟩ .empty) ⟨2,true,11,5⟩ .empty) ⟨2,true,11,12⟩ (.node (.node .empty ⟨3,false,2,1⟩ .empty) ⟨3,false,3,0⟩ .empty)))
def t52_77 : Tree := .node t52_64 ⟨2,false,14,13⟩ t65_77
def t78_90 : Tree := (.node (.node (.node (.node .empty ⟨3,false,8,9⟩ .empty) ⟨3,false,8,14⟩ (.node .empty ⟨3,false,9,0⟩ .empty)) ⟨3,false,9,5⟩ (.node (.node .empty ⟨3,false,9,12⟩ .empty) ⟨3,false,14,1⟩ .empty)) ⟨3,false,14,9⟩ (.node (.node (.node .empty ⟨3,false,14,14⟩ .empty) ⟨3,false,15,0⟩ .empty) ⟨3,false,15,5⟩ (.node (.node .empty ⟨3,false,15,12⟩ .empty) ⟨3,false,19,9⟩ .empty)))
def t91_103 : Tree := (.node (.node (.node (.node .empty ⟨3,false,20,5⟩ .empty) ⟨3,false,20,12⟩ (.node .empty ⟨3,true,1,2⟩ .empty)) ⟨3,true,4,3⟩ (.node (.node .empty ⟨3,true,4,11⟩ .empty) ⟨3,true,6,10⟩ .empty)) ⟨3,true,7,2⟩ (.node (.node (.node .empty ⟨3,true,7,10⟩ .empty) ⟨3,true,13,2⟩ .empty) ⟨3,true,13,10⟩ (.node (.node .empty ⟨3,true,16,2⟩ .empty) ⟨3,true,16,10⟩ .empty)))
def t78_103 : Tree := .node t78_90 ⟨3,false,19,14⟩ t91_103
def t52_103 : Tree := .node t52_77 ⟨3,false,8,1⟩ t78_103
def t0_103 : Tree := .node t0_51 ⟨1,true,17,3⟩ t52_103
def t104_116 : Tree := (.node (.node (.node (.node .empty ⟨3,true,17,10⟩ .empty) ⟨3,true,18,2⟩ (.node .empty ⟨3,true,18,10⟩ .empty)) ⟨4,false,0,6⟩ (.node (.node .empty ⟨4,false,5,1⟩ .empty) ⟨4,false,5,4⟩ .empty)) ⟨4,false,5,8⟩ (.node (.node (.node .empty ⟨4,false,5,9⟩ .empty) ⟨4,false,6,0⟩ .empty) ⟨4,false,6,3⟩ (.node (.node .empty ⟨4,false,6,4⟩ .empty) ⟨4,false,6,5⟩ .empty)))
def t117_129 : Tree := (.node (.node (.node (.node .empty ⟨4,false,6,11⟩ .empty) ⟨4,false,6,15⟩ (.node .empty ⟨4,false,7,3⟩ .empty)) ⟨4,false,7,11⟩ (.node (.node .empty ⟨4,false,7,15⟩ .empty) ⟨4,false,13,3⟩ .empty)) ⟨4,false,13,11⟩ (.node (.node (.node .empty ⟨4,false,13,15⟩ .empty) ⟨4,false,16,0⟩ .empty) ⟨4,false,16,3⟩ (.node (.node .empty ⟨4,false,16,4⟩ .empty) ⟨4,false,16,5⟩ .empty)))
def t104_129 : Tree := .node t104_116 ⟨4,false,6,8⟩ t117_129
def t130_142 : Tree := (.node (.node (.node (.node .empty ⟨4,false,16,11⟩ .empty) ⟨4,false,16,15⟩ (.node .empty ⟨4,false,17,3⟩ .empty)) ⟨4,false,17,4⟩ (.node (.node .empty ⟨4,false,17,8⟩ .empty) ⟨4,false,17,11⟩ .empty)) ⟨4,false,17,15⟩ (.node (.node (.node .empty ⟨4,false,18,3⟩ .empty) ⟨4,false,18,11⟩ .empty) ⟨4,false,18,15⟩ (.node (.node .empty ⟨4,true,0,4⟩ .empty) ⟨4,true,2,1⟩ .empty)))
def t143_155 : Tree := (.node (.node (.node (.node .empty ⟨4,true,7,13⟩ .empty) ⟨4,true,8,1⟩ (.node .empty ⟨4,true,8,9⟩ .empty)) ⟨4,true,8,14⟩ (.node (.node .empty ⟨4,true,9,4⟩ .empty) ⟨4,true,9,8⟩ .empty)) ⟨4,true,10,6⟩ (.node (.node (.node .empty ⟨4,true,10,13⟩ .empty) ⟨4,true,12,4⟩ .empty) ⟨4,true,12,8⟩ (.node (.node .empty ⟨4,true,14,1⟩ .empty) ⟨4,true,14,9⟩ .empty)))
def t130_155 : Tree := .node t130_142 ⟨4,true,7,6⟩ t143_155
def t104_155 : Tree := .node t104_129 ⟨4,false,16,8⟩ t130_155
def t156_168 : Tree := (.node (.node (.node (.node .empty ⟨4,true,17,6⟩ .empty) ⟨4,true,17,13⟩ (.node .empty ⟨4,true,18,6⟩ .empty)) ⟨4,true,18,13⟩ (.node (.node .empty ⟨4,true,19,9⟩ .empty) ⟨4,true,19,14⟩ .empty)) ⟨5,false,0,5⟩ (.node (.node (.node .empty ⟨5,false,6,7⟩ .empty) ⟨5,false,7,0⟩ .empty) ⟨5,false,7,1⟩ (.node (.node .empty ⟨5,false,7,4⟩ .empty) ⟨5,false,7,7⟩ .empty)))
def t169_181 : Tree := (.node (.node (.node (.node .empty ⟨5,false,7,14⟩ .empty) ⟨5,false,8,5⟩ (.node .empty ⟨5,false,8,12⟩ .empty)) ⟨5,false,10,1⟩ (.node (.node .empty ⟨5,false,10,9⟩ .empty) ⟨5,false,10,14⟩ .empty)) ⟨5,false,11,5⟩ (.node (.node (.node .empty ⟨5,false,11,12⟩ .empty) ⟨5,false,13,7⟩ .empty) ⟨5,false,16,7⟩ (.node (.node .empty ⟨5,false,17,0⟩ .empty) ⟨5,false,17,1⟩ .empty)))
def t156_181 : Tree := .node t156_168 ⟨5,false,7,9⟩ t169_181
def t182_194 : Tree := (.node (.node (.node (.node .empty ⟨5,false,17,7⟩ .empty) ⟨5,false,17,9⟩ (.node .empty ⟨5,false,17,14⟩ .empty)) ⟨5,false,18,1⟩ (.node (.node .empty ⟨5,false,18,7⟩ .empty) ⟨5,false,18,9⟩ .empty)) ⟨5,false,18,14⟩ (.node (.node (.node .empty ⟨5,true,1,3⟩ .empty) ⟨5,true,6,11⟩ .empty) ⟨5,true,6,15⟩ (.node (.node .empty ⟨5,true,7,3⟩ .empty) ⟨5,true,7,11⟩ .empty)))
def t195_207 : Tree := (.node (.node (.node (.node .empty ⟨5,true,13,3⟩ .empty) ⟨5,true,13,11⟩ (.node .empty ⟨5,true,13,15⟩ .empty)) ⟨5,true,16,3⟩ (.node (.node .empty ⟨5,true,16,11⟩ .empty) ⟨5,true,16,15⟩ .empty)) ⟨5,true,17,3⟩ (.node (.node (.node .empty ⟨5,true,17,11⟩ .empty) ⟨5,true,17,15⟩ .empty) ⟨5,true,18,3⟩ (.node (.node .empty ⟨5,true,18,11⟩ .empty) ⟨5,true,18,15⟩ .empty)))
def t182_207 : Tree := .node t182_194 ⟨5,true,7,15⟩ t195_207
def t156_207 : Tree := .node t156_181 ⟨5,false,17,4⟩ t182_207
def t104_207 : Tree := .node t104_155 ⟨4,true,14,14⟩ t156_207
def t0_207 : Tree := .node t0_103 ⟨3,true,17,2⟩ t104_207
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 0, 0, 0, 0, 5, 6, 0, 7, 19, 10, 8, 9, 0, 0, 16, 0, 11, 12, 0, 0, 13, 10, 14, 15, 0, 0, 0, 17, 14, 18, 8, 10, 8, 20, 0, 0, 0],#[0, 1, 3, 2, 0, 0, 0, 4, 5, 0, 6, 9, 7, 0, 8, 0, 12, 0, 11, 10, 0, 0, 0, 4, 13, 14, 7, 0, 15, 10, 0, 8],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,4)],[(false,5)],[(false,6)],[(true,7),(true,17),(true,18)],[(false,8)],[(false,7),(false,13),(false,18)],[(true,10)],[(false,11)],[(true,12)],[(true,13),(true,16)],[(false,14)],[(true,9)],[(false,16)],[(false,17)],[(true,6)],[(false,19)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3),(true,11)],[(false,4)],[(false,5)],[(false,6),(false,13)],[(false,7),(true,15)],[(true,5)],[(true,9),(true,14)],[(false,9)],[(false,8)],[(false,12)],[(true,12)],[(false,14)]],
  t0_207⟩
theorem check0_12 : t0_12.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check13_25 : t13_25.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node12 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,7,0⟩ = true := by decide
theorem check0_25 : t0_25.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node12 check0_12 check13_25
theorem check26_38 : t26_38.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check39_51 : t39_51.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node38 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,6,11⟩ = true := by decide
theorem check26_51 : t26_51.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node38 check26_38 check39_51
theorem node25 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,17,0⟩ = true := by decide
theorem check0_51 : t0_51.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node25 check0_25 check26_51
theorem check52_64 : t52_64.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check65_77 : t65_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node64 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,14,13⟩ = true := by decide
theorem check52_77 : t52_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node64 check52_64 check65_77
theorem check78_90 : t78_90.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check91_103 : t91_103.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node90 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,19,14⟩ = true := by decide
theorem check78_103 : t78_103.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node90 check78_90 check91_103
theorem node77 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,8,1⟩ = true := by decide
theorem check52_103 : t52_103.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node77 check52_77 check78_103
theorem node51 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,17,3⟩ = true := by decide
theorem check0_103 : t0_103.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node51 check0_51 check52_103
theorem check104_116 : t104_116.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check117_129 : t117_129.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node116 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,6,8⟩ = true := by decide
theorem check104_129 : t104_129.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node116 check104_116 check117_129
theorem check130_142 : t130_142.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check143_155 : t143_155.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node142 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,7,6⟩ = true := by decide
theorem check130_155 : t130_155.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node142 check130_142 check143_155
theorem node129 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,16,8⟩ = true := by decide
theorem check104_155 : t104_155.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node129 check104_129 check130_155
theorem check156_168 : t156_168.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check169_181 : t169_181.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node168 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,7,9⟩ = true := by decide
theorem check156_181 : t156_181.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node168 check156_168 check169_181
theorem check182_194 : t182_194.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check195_207 : t195_207.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node194 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,7,15⟩ = true := by decide
theorem check182_207 : t182_207.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node194 check182_194 check195_207
theorem node181 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,17,4⟩ = true := by decide
theorem check156_207 : t156_207.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node181 check156_181 check182_207
theorem node155 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,14,14⟩ = true := by decide
theorem check104_207 : t104_207.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node155 check104_155 check156_207
theorem node103 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,17,2⟩ = true := by decide
theorem check0_207 : t0_207.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node103 check0_103 check104_207
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_207
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M074
