import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M060
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
def t0_14 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,5,3⟩ (.node .empty ⟨0,false,5,13⟩ .empty)) ⟨0,false,10,4⟩ (.node (.node .empty ⟨0,false,10,19⟩ .empty) ⟨0,false,15,0⟩ (.node .empty ⟨0,false,15,3⟩ .empty))) ⟨0,false,15,4⟩ (.node (.node (.node .empty ⟨0,false,15,13⟩ .empty) ⟨0,false,15,19⟩ (.node .empty ⟨0,false,15,23⟩ .empty)) ⟨0,false,20,3⟩ (.node (.node .empty ⟨0,false,20,4⟩ .empty) ⟨0,false,20,13⟩ .empty)))
def t15_29 : Tree := (.node (.node (.node (.node .empty ⟨0,false,20,23⟩ .empty) ⟨0,true,1,5⟩ (.node .empty ⟨0,true,1,9⟩ .empty)) ⟨0,true,1,15⟩ (.node (.node .empty ⟨0,true,1,18⟩ .empty) ⟨0,true,5,7⟩ (.node .empty ⟨0,true,5,9⟩ .empty))) ⟨0,true,5,16⟩ (.node (.node (.node .empty ⟨0,true,5,18⟩ .empty) ⟨0,true,10,5⟩ (.node .empty ⟨0,true,10,7⟩ .empty)) ⟨0,true,10,9⟩ (.node (.node .empty ⟨0,true,10,15⟩ .empty) ⟨0,true,10,16⟩ .empty)))
def t0_29 : Tree := .node t0_14 ⟨0,false,20,19⟩ t15_29
def t30_44 : Tree := (.node (.node (.node (.node .empty ⟨0,true,10,25⟩ .empty) ⟨0,true,20,5⟩ (.node .empty ⟨0,true,20,7⟩ .empty)) ⟨0,true,20,9⟩ (.node (.node .empty ⟨0,true,20,15⟩ .empty) ⟨0,true,20,16⟩ (.node .empty ⟨0,true,20,18⟩ .empty))) ⟨0,true,20,25⟩ (.node (.node (.node .empty ⟨1,false,1,0⟩ .empty) ⟨1,false,6,1⟩ (.node .empty ⟨1,false,6,12⟩ .empty)) ⟨1,false,11,3⟩ (.node (.node .empty ⟨1,false,11,9⟩ .empty) ⟨1,false,11,16⟩ .empty)))
def t45_59 : Tree := (.node (.node (.node (.node .empty ⟨1,false,16,1⟩ .empty) ⟨1,false,16,3⟩ (.node .empty ⟨1,false,16,9⟩ .empty)) ⟨1,false,16,12⟩ (.node (.node .empty ⟨1,false,16,16⟩ .empty) ⟨1,false,16,22⟩ (.node .empty ⟨1,false,21,1⟩ .empty))) ⟨1,false,21,3⟩ (.node (.node (.node .empty ⟨1,false,21,9⟩ .empty) ⟨1,false,21,12⟩ (.node .empty ⟨1,false,21,16⟩ .empty)) ⟨1,false,21,22⟩ (.node (.node .empty ⟨2,false,2,0⟩ .empty) ⟨2,false,12,1⟩ .empty)))
def t30_59 : Tree := .node t30_44 ⟨1,false,16,0⟩ t45_59
def t0_59 : Tree := .node t0_29 ⟨0,true,10,18⟩ t30_59
def t60_74 : Tree := (.node (.node (.node (.node .empty ⟨2,false,12,8⟩ .empty) ⟨2,false,12,26⟩ (.node .empty ⟨2,false,17,0⟩ .empty)) ⟨2,false,17,1⟩ (.node (.node .empty ⟨2,false,17,6⟩ .empty) ⟨2,false,17,8⟩ (.node .empty ⟨2,false,17,26⟩ .empty))) ⟨2,true,7,0⟩ (.node (.node (.node .empty ⟨2,true,7,11⟩ .empty) ⟨2,true,12,0⟩ (.node .empty ⟨2,true,12,11⟩ .empty)) ⟨2,true,12,21⟩ (.node (.node .empty ⟨2,true,17,0⟩ .empty) ⟨2,true,17,11⟩ .empty)))
def t75_89 : Tree := (.node (.node (.node (.node .empty ⟨3,false,2,1⟩ .empty) ⟨3,false,3,0⟩ (.node .empty ⟨3,false,17,1⟩ .empty)) ⟨3,false,18,0⟩ (.node (.node .empty ⟨3,true,1,2⟩ .empty) ⟨3,true,13,0⟩ (.node .empty ⟨3,true,13,5⟩ .empty))) ⟨3,true,13,7⟩ (.node (.node (.node .empty ⟨3,true,13,15⟩ .empty) ⟨3,true,13,25⟩ (.node .empty ⟨3,true,16,2⟩ .empty)) ⟨3,true,18,0⟩ (.node (.node .empty ⟨3,true,18,5⟩ .empty) ⟨3,true,18,7⟩ .empty)))
def t60_89 : Tree := .node t60_74 ⟨2,true,17,21⟩ t75_89
def t90_104 : Tree := (.node (.node (.node (.node .empty ⟨3,true,18,25⟩ .empty) ⟨4,false,0,6⟩ (.node .empty ⟨4,false,0,10⟩ .empty)) ⟨4,false,4,4⟩ (.node (.node .empty ⟨4,false,4,8⟩ .empty) ⟨4,false,4,10⟩ (.node .empty ⟨4,false,4,14⟩ .empty))) ⟨4,false,4,17⟩ (.node (.node (.node .empty ⟨4,false,9,5⟩ .empty) ⟨4,false,9,6⟩ (.node .empty ⟨4,false,9,8⟩ .empty)) ⟨4,false,9,10⟩ (.node (.node .empty ⟨4,false,9,17⟩ .empty) ⟨4,false,9,20⟩ .empty)))
def t105_119 : Tree := (.node (.node (.node (.node .empty ⟨4,false,14,0⟩ .empty) ⟨4,false,14,4⟩ (.node .empty ⟨4,false,14,5⟩ .empty)) ⟨4,false,14,14⟩ (.node (.node .empty ⟨4,false,14,20⟩ .empty) ⟨4,false,14,24⟩ (.node .empty ⟨4,false,19,4⟩ .empty))) ⟨4,false,19,5⟩ (.node (.node (.node .empty ⟨4,false,19,6⟩ .empty) ⟨4,false,19,8⟩ (.node .empty ⟨4,false,19,10⟩ .empty)) ⟨4,false,19,14⟩ (.node (.node .empty ⟨4,false,19,17⟩ .empty) ⟨4,false,19,20⟩ .empty)))
def t90_119 : Tree := .node t90_104 ⟨4,false,9,26⟩ t105_119
def t60_119 : Tree := .node t60_89 ⟨3,true,18,15⟩ t90_119
def t0_119 : Tree := .node t0_59 ⟨2,false,12,6⟩ t60_119
def t120_134 : Tree := (.node (.node (.node (.node .empty ⟨4,false,19,26⟩ .empty) ⟨4,true,0,8⟩ (.node .empty ⟨4,true,0,10⟩ .empty)) ⟨4,true,0,17⟩ (.node (.node .empty ⟨4,true,2,1⟩ .empty) ⟨4,true,4,6⟩ (.node .empty ⟨4,true,4,8⟩ .empty))) ⟨4,true,4,10⟩ (.node (.node (.node .empty ⟨4,true,4,17⟩ .empty) ⟨4,true,4,26⟩ (.node .empty ⟨4,true,7,1⟩ .empty)) ⟨4,true,7,6⟩ (.node (.node .empty ⟨4,true,7,8⟩ .empty) ⟨4,true,7,26⟩ .empty)))
def t135_149 : Tree := (.node (.node (.node (.node .empty ⟨4,true,9,8⟩ .empty) ⟨4,true,9,10⟩ (.node .empty ⟨4,true,9,17⟩ .empty)) ⟨4,true,9,26⟩ (.node (.node .empty ⟨4,true,11,12⟩ .empty) ⟨4,true,11,22⟩ (.node .empty ⟨4,true,12,1⟩ .empty))) ⟨4,true,12,6⟩ (.node (.node (.node .empty ⟨4,true,12,8⟩ .empty) ⟨4,true,12,26⟩ (.node .empty ⟨4,true,16,12⟩ .empty)) ⟨4,true,16,22⟩ (.node (.node .empty ⟨4,true,17,1⟩ .empty) ⟨4,true,17,6⟩ .empty)))
def t120_149 : Tree := .node t120_134 ⟨4,true,9,6⟩ t135_149
def t150_164 : Tree := (.node (.node (.node (.node .empty ⟨4,true,17,26⟩ .empty) ⟨4,true,19,6⟩ (.node .empty ⟨4,true,19,8⟩ .empty)) ⟨4,true,19,10⟩ (.node (.node .empty ⟨4,true,19,17⟩ .empty) ⟨4,true,19,26⟩ (.node .empty ⟨4,true,21,12⟩ .empty))) ⟨4,true,21,22⟩ (.node (.node (.node .empty ⟨5,false,0,5⟩ .empty) ⟨5,false,0,9⟩ (.node .empty ⟨5,false,0,18⟩ .empty)) ⟨5,false,1,7⟩ (.node (.node .empty ⟨5,false,1,9⟩ .empty) ⟨5,false,1,16⟩ .empty)))
def t165_179 : Tree := (.node (.node (.node (.node .empty ⟨5,false,5,7⟩ .empty) ⟨5,false,5,9⟩ (.node .empty ⟨5,false,5,15⟩ .empty)) ⟨5,false,5,16⟩ (.node (.node .empty ⟨5,false,5,18⟩ .empty) ⟨5,false,5,25⟩ (.node .empty ⟨5,false,8,0⟩ .empty))) ⟨5,false,8,7⟩ (.node (.node (.node .empty ⟨5,false,8,15⟩ .empty) ⟨5,false,8,25⟩ (.node .empty ⟨5,false,10,7⟩ .empty)) ⟨5,false,10,9⟩ (.node (.node .empty ⟨5,false,10,15⟩ .empty) ⟨5,false,10,16⟩ .empty)))
def t150_179 : Tree := .node t150_164 ⟨5,false,1,18⟩ t165_179
def t120_179 : Tree := .node t120_149 ⟨4,true,17,8⟩ t150_179
def t180_194 : Tree := (.node (.node (.node (.node .empty ⟨5,false,10,25⟩ .empty) ⟨5,false,12,11⟩ (.node .empty ⟨5,false,12,21⟩ .empty)) ⟨5,false,17,11⟩ (.node (.node .empty ⟨5,false,17,21⟩ .empty) ⟨5,false,20,7⟩ (.node .empty ⟨5,false,20,9⟩ .empty))) ⟨5,false,20,15⟩ (.node (.node (.node .empty ⟨5,false,20,16⟩ .empty) ⟨5,false,20,18⟩ (.node .empty ⟨5,false,20,25⟩ .empty)) ⟨5,true,0,4⟩ (.node (.node .empty ⟨5,true,1,3⟩ .empty) ⟨5,true,4,5⟩ .empty)))
def t195_209 : Tree := (.node (.node (.node (.node .empty ⟨5,true,5,4⟩ .empty) ⟨5,true,5,19⟩ (.node .empty ⟨5,true,6,3⟩ .empty)) ⟨5,true,6,9⟩ (.node (.node .empty ⟨5,true,6,16⟩ .empty) ⟨5,true,9,5⟩ (.node .empty ⟨5,true,9,14⟩ .empty))) ⟨5,true,9,20⟩ (.node (.node (.node .empty ⟨5,true,9,24⟩ .empty) ⟨5,true,10,4⟩ (.node .empty ⟨5,true,10,13⟩ .empty)) ⟨5,true,10,19⟩ (.node (.node .empty ⟨5,true,10,23⟩ .empty) ⟨5,true,11,3⟩ .empty)))
def t180_209 : Tree := .node t180_194 ⟨5,true,4,20⟩ t195_209
def t210_224 : Tree := (.node (.node (.node (.node .empty ⟨5,true,11,16⟩ .empty) ⟨5,true,13,7⟩ (.node .empty ⟨5,true,13,15⟩ .empty)) ⟨5,true,13,25⟩ (.node (.node .empty ⟨5,true,14,5⟩ .empty) ⟨5,true,14,14⟩ (.node .empty ⟨5,true,14,20⟩ .empty))) ⟨5,true,14,24⟩ (.node (.node (.node .empty ⟨5,true,15,4⟩ .empty) ⟨5,true,15,13⟩ (.node .empty ⟨5,true,15,19⟩ .empty)) ⟨5,true,15,23⟩ (.node (.node .empty ⟨5,true,16,3⟩ .empty) ⟨5,true,16,9⟩ .empty)))
def t225_239 : Tree := (.node (.node (.node (.node .empty ⟨5,true,18,7⟩ .empty) ⟨5,true,18,15⟩ (.node .empty ⟨5,true,18,25⟩ .empty)) ⟨5,true,19,5⟩ (.node (.node .empty ⟨5,true,19,14⟩ .empty) ⟨5,true,19,20⟩ (.node .empty ⟨5,true,19,24⟩ .empty))) ⟨5,true,20,4⟩ (.node (.node (.node .empty ⟨5,true,20,13⟩ .empty) ⟨5,true,20,19⟩ (.node .empty ⟨5,true,20,23⟩ .empty)) ⟨5,true,21,3⟩ (.node (.node .empty ⟨5,true,21,9⟩ .empty) ⟨5,true,21,16⟩ .empty)))
def t210_239 : Tree := .node t210_224 ⟨5,true,16,16⟩ t225_239
def t180_239 : Tree := .node t180_209 ⟨5,true,11,9⟩ t210_239
def t120_239 : Tree := .node t120_179 ⟨5,false,10,18⟩ t180_239
def t0_239 : Tree := .node t0_119 ⟨4,false,19,24⟩ t120_239
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 0, 0, 0, 0, 5, 9, 6, 0, 7, 0, 8, 0, 0, 0, 10, 19, 11, 0, 12, 13, 8, 0, 14, 0, 15, 0, 16, 0, 17, 18, 8, 0, 14, 0, 20, 19, 21, 0, 12],#[0, 1, 3, 2, 0, 0, 4, 0, 5, 0, 7, 6, 16, 0, 11, 8, 9, 0, 19, 10, 18, 0, 0, 12, 13, 0, 14, 0, 15, 0, 21, 6, 19, 17, 18, 0, 0, 10, 20, 0, 7, 0, 0, 22, 23, 0, 24, 0, 25, 0, 21, 26, 16, 0],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,4)],[(true,5)],[(true,6)],[(true,7),(true,12),(true,17)],[(false,5)],[(true,9)],[(true,10)],[(true,11),(true,21)],[(false,12)],[(true,13),(true,18)],[(true,14)],[(true,15)],[(true,16)],[(false,17)],[(false,10),(false,20)],[(true,19)],[(true,20)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(false,4)],[(true,5),(true,15)],[(false,5),(false,20)],[(true,7)],[(false,8)],[(true,9),(true,18)],[(false,7)],[(true,11)],[(false,12)],[(false,13)],[(false,14)],[(false,6),(false,26)],[(true,16)],[(false,10),(false,17)],[(false,9),(false,16)],[(false,19)],[(false,15),(false,25)],[(true,21)],[(false,22)],[(false,23)],[(false,24)],[(true,25)]],
  t0_239⟩
theorem check0_14 : t0_14.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check15_29 : t15_29.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node14 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,20,19⟩ = true := by decide
theorem check0_29 : t0_29.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node14 check0_14 check15_29
theorem check30_44 : t30_44.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check45_59 : t45_59.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node44 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,16,0⟩ = true := by decide
theorem check30_59 : t30_59.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node44 check30_44 check45_59
theorem node29 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,10,18⟩ = true := by decide
theorem check0_59 : t0_59.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node29 check0_29 check30_59
theorem check60_74 : t60_74.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check75_89 : t75_89.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node74 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,17,21⟩ = true := by decide
theorem check60_89 : t60_89.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node74 check60_74 check75_89
theorem check90_104 : t90_104.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check105_119 : t105_119.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node104 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,9,26⟩ = true := by decide
theorem check90_119 : t90_119.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node104 check90_104 check105_119
theorem node89 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,18,15⟩ = true := by decide
theorem check60_119 : t60_119.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node89 check60_89 check90_119
theorem node59 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,12,6⟩ = true := by decide
theorem check0_119 : t0_119.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node59 check0_59 check60_119
theorem check120_134 : t120_134.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check135_149 : t135_149.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node134 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,9,6⟩ = true := by decide
theorem check120_149 : t120_149.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node134 check120_134 check135_149
theorem check150_164 : t150_164.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check165_179 : t165_179.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node164 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,1,18⟩ = true := by decide
theorem check150_179 : t150_179.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node164 check150_164 check165_179
theorem node149 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,17,8⟩ = true := by decide
theorem check120_179 : t120_179.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node149 check120_149 check150_179
theorem check180_194 : t180_194.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check195_209 : t195_209.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node194 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,4,20⟩ = true := by decide
theorem check180_209 : t180_209.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node194 check180_194 check195_209
theorem check210_224 : t210_224.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check225_239 : t225_239.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node224 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,16,16⟩ = true := by decide
theorem check210_239 : t210_239.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node224 check210_224 check225_239
theorem node209 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,11,9⟩ = true := by decide
theorem check180_239 : t180_239.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node209 check180_209 check210_239
theorem node179 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,10,18⟩ = true := by decide
theorem check120_239 : t120_239.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node179 check120_179 check180_239
theorem node119 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,19,24⟩ = true := by decide
theorem check0_239 : t0_239.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node119 check0_119 check120_239
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_239
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M060
