import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M099
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def t0_15 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,true,6,1⟩ (.node .empty ⟨0,true,6,7⟩ .empty)) ⟨0,true,6,12⟩ (.node (.node .empty ⟨0,true,6,14⟩ .empty) ⟨0,true,6,15⟩ (.node .empty ⟨0,true,6,17⟩ .empty))) ⟨0,true,6,19⟩ (.node (.node (.node .empty ⟨0,true,7,0⟩ .empty) ⟨0,true,7,2⟩ (.node .empty ⟨0,true,7,13⟩ .empty)) ⟨0,true,8,1⟩ (.node (.node .empty ⟨0,true,8,12⟩ .empty) ⟨0,true,8,14⟩ (.node .empty ⟨0,true,13,0⟩ .empty))))
def t16_31 : Tree := (.node (.node (.node (.node .empty ⟨0,true,13,13⟩ .empty) ⟨0,true,14,12⟩ (.node .empty ⟨0,true,14,14⟩ .empty)) ⟨0,true,14,15⟩ (.node (.node .empty ⟨0,true,14,17⟩ .empty) ⟨0,true,14,19⟩ (.node .empty ⟨0,true,15,2⟩ .empty))) ⟨0,true,15,13⟩ (.node (.node (.node .empty ⟨0,true,16,1⟩ .empty) ⟨0,true,16,12⟩ (.node .empty ⟨0,true,16,14⟩ .empty)) ⟨0,true,17,1⟩ (.node (.node .empty ⟨0,true,17,12⟩ .empty) ⟨0,true,17,14⟩ (.node .empty ⟨1,false,1,0⟩ .empty))))
def t0_31 : Tree := .node t0_15 ⟨0,true,13,2⟩ t16_31
def t32_47 : Tree := (.node (.node (.node (.node .empty ⟨2,false,1,10⟩ .empty) ⟨2,false,1,18⟩ (.node .empty ⟨2,false,2,0⟩ .empty)) ⟨2,false,5,10⟩ (.node (.node .empty ⟨2,false,5,16⟩ .empty) ⟨2,false,5,18⟩ (.node .empty ⟨2,false,5,21⟩ .empty))) ⟨2,false,7,3⟩ (.node (.node (.node .empty ⟨2,false,7,13⟩ .empty) ⟨2,false,7,16⟩ (.node .empty ⟨2,false,7,18⟩ .empty)) ⟨2,false,8,0⟩ (.node (.node .empty ⟨2,false,11,10⟩ .empty) ⟨2,false,11,16⟩ (.node .empty ⟨2,false,11,18⟩ .empty))))
def t48_63 : Tree := (.node (.node (.node (.node .empty ⟨2,false,15,13⟩ .empty) ⟨2,false,15,16⟩ (.node .empty ⟨2,false,15,18⟩ .empty)) ⟨2,false,17,0⟩ (.node (.node .empty ⟨2,true,1,4⟩ .empty) ⟨2,true,1,9⟩ (.node .empty ⟨2,true,1,17⟩ .empty))) ⟨2,true,1,19⟩ (.node (.node (.node .empty ⟨2,true,2,7⟩ .empty) ⟨2,true,2,15⟩ (.node .empty ⟨2,true,2,17⟩ .empty)) ⟨2,true,2,19⟩ (.node (.node .empty ⟨2,true,7,0⟩ .empty) ⟨2,true,7,2⟩ (.node .empty ⟨2,true,7,13⟩ .empty))))
def t32_63 : Tree := .node t32_47 ⟨2,false,11,21⟩ t48_63
def t0_63 : Tree := .node t0_31 ⟨2,false,1,5⟩ t32_63
def t64_79 : Tree := (.node (.node (.node (.node .empty ⟨2,true,8,12⟩ .empty) ⟨2,true,8,14⟩ (.node .empty ⟨2,true,10,9⟩ .empty)) ⟨2,true,10,15⟩ (.node (.node .empty ⟨2,true,10,17⟩ .empty) ⟨2,true,10,19⟩ (.node .empty ⟨2,true,10,20⟩ .empty))) ⟨2,true,12,15⟩ (.node (.node (.node .empty ⟨2,true,12,17⟩ .empty) ⟨2,true,12,19⟩ (.node .empty ⟨2,true,13,0⟩ .empty)) ⟨2,true,13,2⟩ (.node (.node .empty ⟨2,true,13,13⟩ .empty) ⟨2,true,15,2⟩ (.node .empty ⟨2,true,15,13⟩ .empty))))
def t80_95 : Tree := (.node (.node (.node (.node .empty ⟨2,true,16,12⟩ .empty) ⟨2,true,16,14⟩ (.node .empty ⟨2,true,17,1⟩ .empty)) ⟨2,true,17,12⟩ (.node (.node .empty ⟨2,true,17,14⟩ .empty) ⟨2,true,18,7⟩ (.node .empty ⟨2,true,18,15⟩ .empty))) ⟨2,true,18,17⟩ (.node (.node (.node .empty ⟨2,true,18,19⟩ .empty) ⟨3,false,2,1⟩ (.node .empty ⟨3,false,3,0⟩ .empty)) ⟨3,false,5,13⟩ (.node (.node .empty ⟨3,false,6,12⟩ .empty) ⟨3,false,6,14⟩ (.node .empty ⟨3,false,7,2⟩ .empty))))
def t64_95 : Tree := .node t64_79 ⟨2,true,16,1⟩ t80_95
def t96_111 : Tree := (.node (.node (.node (.node .empty ⟨3,false,8,1⟩ .empty) ⟨3,false,8,12⟩ (.node .empty ⟨3,false,8,14⟩ .empty)) ⟨3,false,9,13⟩ (.node (.node .empty ⟨3,false,11,13⟩ .empty) ⟨3,false,13,0⟩ (.node .empty ⟨3,false,13,2⟩ .empty))) ⟨3,false,13,13⟩ (.node (.node (.node .empty ⟨3,false,14,12⟩ .empty) ⟨3,false,14,14⟩ (.node .empty ⟨3,false,15,2⟩ .empty)) ⟨3,false,15,13⟩ (.node (.node .empty ⟨3,false,16,1⟩ .empty) ⟨3,false,16,12⟩ (.node .empty ⟨3,false,16,14⟩ .empty))))
def t112_126 : Tree := (.node (.node (.node (.node .empty ⟨3,false,17,12⟩ .empty) ⟨3,false,17,14⟩ (.node .empty ⟨3,true,1,2⟩ .empty)) ⟨3,true,4,4⟩ (.node (.node .empty ⟨3,true,4,9⟩ .empty) ⟨3,true,4,14⟩ (.node .empty ⟨3,true,4,17⟩ .empty))) ⟨3,true,4,19⟩ (.node (.node (.node .empty ⟨3,true,6,9⟩ .empty) ⟨3,true,6,14⟩ (.node .empty ⟨3,true,6,15⟩ .empty)) ⟨3,true,6,17⟩ (.node (.node .empty ⟨3,true,6,19⟩ .empty) ⟨3,true,6,20⟩ .empty)))
def t96_126 : Tree := .node t96_111 ⟨3,false,17,1⟩ t112_126
def t64_126 : Tree := .node t64_95 ⟨3,false,7,13⟩ t96_126
def t0_126 : Tree := .node t0_63 ⟨2,true,8,1⟩ t64_126
def t127_142 : Tree := (.node (.node (.node (.node .empty ⟨3,true,8,14⟩ .empty) ⟨3,true,8,15⟩ (.node .empty ⟨3,true,8,17⟩ .empty)) ⟨3,true,8,19⟩ (.node (.node .empty ⟨3,true,14,14⟩ .empty) ⟨3,true,16,12⟩ (.node .empty ⟨3,true,16,14⟩ .empty))) ⟨3,true,16,15⟩ (.node (.node (.node .empty ⟨3,true,16,17⟩ .empty) ⟨3,true,16,19⟩ (.node .empty ⟨4,false,5,8⟩ .empty)) ⟨4,false,5,16⟩ (.node (.node .empty ⟨4,false,5,18⟩ .empty) ⟨4,false,6,1⟩ (.node .empty ⟨4,false,6,12⟩ .empty))))
def t143_158 : Tree := (.node (.node (.node (.node .empty ⟨4,false,7,2⟩ .empty) ⟨4,false,7,13⟩ (.node .empty ⟨4,false,8,1⟩ .empty)) ⟨4,false,8,12⟩ (.node (.node .empty ⟨4,false,8,14⟩ .empty) ⟨4,false,9,13⟩ (.node .empty ⟨4,false,9,16⟩ .empty))) ⟨4,false,9,18⟩ (.node (.node (.node .empty ⟨4,false,11,2⟩ .empty) ⟨4,false,11,8⟩ (.node .empty ⟨4,false,11,13⟩ .empty)) ⟨4,false,11,16⟩ (.node (.node .empty ⟨4,false,11,18⟩ .empty) ⟨4,false,13,2⟩ (.node .empty ⟨4,false,13,13⟩ .empty))))
def t127_158 : Tree := .node t127_142 ⟨4,false,6,14⟩ t143_158
def t159_174 : Tree := (.node (.node (.node (.node .empty ⟨4,false,14,14⟩ .empty) ⟨4,false,15,2⟩ (.node .empty ⟨4,false,15,13⟩ .empty)) ⟨4,false,16,1⟩ (.node (.node .empty ⟨4,false,16,12⟩ .empty) ⟨4,false,16,14⟩ (.node .empty ⟨4,false,17,1⟩ .empty))) ⟨4,false,17,12⟩ (.node (.node (.node .empty ⟨4,false,17,14⟩ .empty) ⟨4,true,0,5⟩ (.node .empty ⟨4,true,0,10⟩ .empty)) ⟨4,true,0,18⟩ (.node (.node .empty ⟨4,true,1,8⟩ .empty) ⟨4,true,1,16⟩ (.node .empty ⟨4,true,1,18⟩ .empty))))
def t175_190 : Tree := (.node (.node (.node (.node .empty ⟨4,true,5,3⟩ .empty) ⟨4,true,5,13⟩ (.node .empty ⟨4,true,5,16⟩ .empty)) ⟨4,true,5,18⟩ (.node (.node .empty ⟨4,true,7,10⟩ .empty) ⟨4,true,7,16⟩ (.node .empty ⟨4,true,7,18⟩ .empty))) ⟨4,true,7,21⟩ (.node (.node (.node .empty ⟨4,true,9,2⟩ .empty) ⟨4,true,9,8⟩ (.node .empty ⟨4,true,9,13⟩ .empty)) ⟨4,true,9,16⟩ (.node (.node .empty ⟨4,true,9,18⟩ .empty) ⟨4,true,11,13⟩ (.node .empty ⟨4,true,11,16⟩ .empty))))
def t159_190 : Tree := .node t159_174 ⟨4,true,2,1⟩ t175_190
def t127_190 : Tree := .node t127_158 ⟨4,false,14,12⟩ t159_190
def t191_206 : Tree := (.node (.node (.node (.node .empty ⟨4,true,15,10⟩ .empty) ⟨4,true,15,16⟩ (.node .empty ⟨4,true,15,18⟩ .empty)) ⟨4,true,15,21⟩ (.node (.node .empty ⟨5,false,0,5⟩ .empty) ⟨5,false,0,6⟩ (.node .empty ⟨5,false,0,10⟩ .empty))) ⟨5,false,0,11⟩ (.node (.node (.node .empty ⟨5,false,0,18⟩ .empty) ⟨5,false,0,19⟩ (.node .empty ⟨5,false,1,8⟩ .empty)) ⟨5,false,1,16⟩ (.node (.node .empty ⟨5,false,1,18⟩ .empty) ⟨5,false,5,16⟩ (.node .empty ⟨5,false,5,18⟩ .empty))))
def t207_222 : Tree := (.node (.node (.node (.node .empty ⟨5,false,6,17⟩ .empty) ⟨5,false,6,19⟩ (.node .empty ⟨5,false,6,22⟩ .empty)) ⟨5,false,7,10⟩ (.node (.node .empty ⟨5,false,7,16⟩ .empty) ⟨5,false,7,18⟩ (.node .empty ⟨5,false,7,21⟩ .empty))) ⟨5,false,9,8⟩ (.node (.node (.node .empty ⟨5,false,9,16⟩ .empty) ⟨5,false,9,18⟩ (.node .empty ⟨5,false,11,16⟩ .empty)) ⟨5,false,11,18⟩ (.node (.node .empty ⟨5,false,14,11⟩ .empty) ⟨5,false,14,17⟩ (.node .empty ⟨5,false,14,19⟩ .empty))))
def t191_222 : Tree := .node t191_206 ⟨5,false,6,11⟩ t207_222
def t223_238 : Tree := (.node (.node (.node (.node .empty ⟨5,false,15,10⟩ .empty) ⟨5,false,15,16⟩ (.node .empty ⟨5,false,15,18⟩ .empty)) ⟨5,false,15,21⟩ (.node (.node .empty ⟨5,true,0,4⟩ .empty) ⟨5,true,0,9⟩ (.node .empty ⟨5,true,0,17⟩ .empty))) ⟨5,true,0,19⟩ (.node (.node (.node .empty ⟨5,true,1,3⟩ .empty) ⟨5,true,4,7⟩ (.node .empty ⟨5,true,4,15⟩ .empty)) ⟨5,true,4,17⟩ (.node (.node .empty ⟨5,true,4,19⟩ .empty) ⟨5,true,6,15⟩ (.node .empty ⟨5,true,6,17⟩ .empty))))
def t239_253 : Tree := (.node (.node (.node (.node .empty ⟨5,true,8,9⟩ .empty) ⟨5,true,8,15⟩ (.node .empty ⟨5,true,8,17⟩ .empty)) ⟨5,true,8,19⟩ (.node (.node .empty ⟨5,true,8,20⟩ .empty) ⟨5,true,14,7⟩ (.node .empty ⟨5,true,14,15⟩ .empty))) ⟨5,true,14,17⟩ (.node (.node (.node .empty ⟨5,true,14,19⟩ .empty) ⟨5,true,16,9⟩ (.node .empty ⟨5,true,16,15⟩ .empty)) ⟨5,true,16,17⟩ (.node (.node .empty ⟨5,true,16,19⟩ .empty) ⟨5,true,16,20⟩ .empty)))
def t223_253 : Tree := .node t223_238 ⟨5,true,6,19⟩ t239_253
def t191_253 : Tree := .node t191_222 ⟨5,false,14,22⟩ t223_253
def t127_253 : Tree := .node t127_190 ⟨4,true,11,18⟩ t191_253
def t0_253 : Tree := .node t0_126 ⟨3,true,8,12⟩ t127_253
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 0, 0, 0, 0, 5, 6, 12, 7, 11, 8, 10, 13, 9, 14, 18, 0, 0, 6, 12, 0, 0, 17, 0, 15, 5, 16, 10, 13, 9, 13, 0, 0, 0],#[0, 1, 3, 2, 20, 12, 7, 4, 0, 5, 6, 0, 0, 0, 0, 8, 9, 0, 0, 10, 11, 0, 0, 0, 0, 13, 15, 14, 0, 13, 0, 16, 17, 0, 0, 18, 19, 0, 0, 18, 0, 21, 22, 0, 0, 0],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,4),(true,14)],[(false,5),(false,11)],[(false,6)],[(false,7)],[(true,8),(true,16)],[(true,7),(true,15)],[(true,6)],[(true,5),(true,11)],[(false,8),(false,16),(false,17)],[(false,9)],[(false,14)],[(false,15)],[(false,13)],[(true,9)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3)],[(true,4)],[(false,5)],[(false,3)],[(true,7)],[(false,8)],[(true,9)],[(false,10)],[(true,2)],[(true,12),(true,14)],[(true,13)],[(false,13)],[(true,15)],[(false,16)],[(true,17),(true,19)],[(false,18)],[(false,2)],[(true,20)],[(false,21)]],
  t0_253⟩
theorem check0_15 : t0_15.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check16_31 : t16_31.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node15 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,13,2⟩ = true := by decide
theorem check0_31 : t0_31.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node15 check0_15 check16_31
theorem check32_47 : t32_47.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check48_63 : t48_63.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node47 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,11,21⟩ = true := by decide
theorem check32_63 : t32_63.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node47 check32_47 check48_63
theorem node31 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,1,5⟩ = true := by decide
theorem check0_63 : t0_63.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node31 check0_31 check32_63
theorem check64_79 : t64_79.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check80_95 : t80_95.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node79 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,16,1⟩ = true := by decide
theorem check64_95 : t64_95.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node79 check64_79 check80_95
theorem check96_111 : t96_111.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check112_126 : t112_126.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node111 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,17,1⟩ = true := by decide
theorem check96_126 : t96_126.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node111 check96_111 check112_126
theorem node95 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,7,13⟩ = true := by decide
theorem check64_126 : t64_126.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node95 check64_95 check96_126
theorem node63 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,8,1⟩ = true := by decide
theorem check0_126 : t0_126.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node63 check0_63 check64_126
theorem check127_142 : t127_142.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check143_158 : t143_158.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node142 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,6,14⟩ = true := by decide
theorem check127_158 : t127_158.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node142 check127_142 check143_158
theorem check159_174 : t159_174.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check175_190 : t175_190.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node174 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,2,1⟩ = true := by decide
theorem check159_190 : t159_190.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node174 check159_174 check175_190
theorem node158 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,14,12⟩ = true := by decide
theorem check127_190 : t127_190.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node158 check127_158 check159_190
theorem check191_206 : t191_206.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check207_222 : t207_222.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node206 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,6,11⟩ = true := by decide
theorem check191_222 : t191_222.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node206 check191_206 check207_222
theorem check223_238 : t223_238.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check239_253 : t239_253.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node238 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,6,19⟩ = true := by decide
theorem check223_253 : t223_253.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node238 check223_238 check239_253
theorem node222 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,14,22⟩ = true := by decide
theorem check191_253 : t191_253.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node222 check191_222 check223_253
theorem node190 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,11,18⟩ = true := by decide
theorem check127_253 : t127_253.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node190 check127_190 check191_253
theorem node126 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,8,12⟩ = true := by decide
theorem check0_253 : t0_253.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node126 check0_126 check127_253
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_253
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M099
