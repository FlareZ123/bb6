import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M059
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
def t0_9 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,5,3⟩ .empty) ⟨0,false,5,13⟩ (.node .empty ⟨0,false,10,4⟩ .empty)) ⟨0,false,10,20⟩ (.node (.node (.node .empty ⟨0,false,15,0⟩ .empty) ⟨0,false,15,3⟩ .empty) ⟨0,false,15,4⟩ (.node .empty ⟨0,false,15,13⟩ .empty)))
def t10_18 : Tree := (.node (.node (.node (.node .empty ⟨0,false,15,24⟩ .empty) ⟨0,false,15,29⟩ .empty) ⟨0,false,19,3⟩ (.node .empty ⟨0,false,19,4⟩ .empty)) ⟨0,false,19,13⟩ (.node (.node .empty ⟨0,false,19,20⟩ .empty) ⟨0,false,19,24⟩ (.node .empty ⟨0,false,19,29⟩ .empty)))
def t0_18 : Tree := .node t0_9 ⟨0,false,15,20⟩ t10_18
def t19_27 : Tree := (.node (.node (.node (.node .empty ⟨0,true,1,9⟩ .empty) ⟨0,true,1,15⟩ .empty) ⟨0,true,1,18⟩ (.node .empty ⟨0,true,5,7⟩ .empty)) ⟨0,true,5,9⟩ (.node (.node .empty ⟨0,true,5,16⟩ .empty) ⟨0,true,5,18⟩ (.node .empty ⟨0,true,5,33⟩ .empty)))
def t28_36 : Tree := (.node (.node (.node (.node .empty ⟨0,true,10,7⟩ .empty) ⟨0,true,10,9⟩ .empty) ⟨0,true,10,15⟩ (.node .empty ⟨0,true,10,16⟩ .empty)) ⟨0,true,10,18⟩ (.node (.node .empty ⟨0,true,10,26⟩ .empty) ⟨0,true,10,31⟩ (.node .empty ⟨0,true,10,33⟩ .empty)))
def t19_36 : Tree := .node t19_27 ⟨0,true,10,5⟩ t28_36
def t0_36 : Tree := .node t0_18 ⟨0,true,1,5⟩ t19_36
def t37_46 : Tree := (.node (.node (.node (.node .empty ⟨0,true,19,7⟩ .empty) ⟨0,true,19,9⟩ .empty) ⟨0,true,19,15⟩ (.node .empty ⟨0,true,19,16⟩ .empty)) ⟨0,true,19,18⟩ (.node (.node (.node .empty ⟨0,true,19,26⟩ .empty) ⟨0,true,19,31⟩ .empty) ⟨0,true,19,33⟩ (.node .empty ⟨1,false,1,0⟩ .empty)))
def t47_55 : Tree := (.node (.node (.node (.node .empty ⟨1,false,6,12⟩ .empty) ⟨1,false,11,3⟩ .empty) ⟨1,false,11,9⟩ (.node .empty ⟨1,false,11,33⟩ .empty)) ⟨1,false,16,0⟩ (.node (.node .empty ⟨1,false,16,1⟩ .empty) ⟨1,false,16,3⟩ (.node .empty ⟨1,false,16,9⟩ .empty)))
def t37_55 : Tree := .node t37_46 ⟨1,false,6,1⟩ t47_55
def t56_64 : Tree := (.node (.node (.node (.node .empty ⟨1,false,16,16⟩ .empty) ⟨1,false,16,23⟩ .empty) ⟨1,false,16,33⟩ (.node .empty ⟨1,false,20,1⟩ .empty)) ⟨1,false,20,3⟩ (.node (.node .empty ⟨1,false,20,9⟩ .empty) ⟨1,false,20,12⟩ (.node .empty ⟨1,false,20,16⟩ .empty)))
def t65_73 : Tree := (.node (.node (.node (.node .empty ⟨1,false,20,33⟩ .empty) ⟨2,false,2,0⟩ .empty) ⟨2,false,12,1⟩ (.node .empty ⟨2,false,12,6⟩ .empty)) ⟨2,false,12,8⟩ (.node (.node .empty ⟨2,false,12,27⟩ .empty) ⟨2,false,12,32⟩ (.node .empty ⟨2,false,17,0⟩ .empty)))
def t56_73 : Tree := .node t56_64 ⟨1,false,20,23⟩ t65_73
def t37_73 : Tree := .node t37_55 ⟨1,false,16,12⟩ t56_73
def t0_73 : Tree := .node t0_36 ⟨0,true,19,5⟩ t37_73
def t74_83 : Tree := (.node (.node (.node (.node .empty ⟨2,false,17,6⟩ .empty) ⟨2,false,17,8⟩ .empty) ⟨2,false,17,27⟩ (.node .empty ⟨2,false,17,32⟩ .empty)) ⟨2,true,7,0⟩ (.node (.node (.node .empty ⟨2,true,7,11⟩ .empty) ⟨2,true,12,0⟩ .empty) ⟨2,true,12,11⟩ (.node .empty ⟨2,true,12,22⟩ .empty)))
def t84_92 : Tree := (.node (.node (.node (.node .empty ⟨2,true,17,11⟩ .empty) ⟨2,true,17,22⟩ .empty) ⟨3,false,2,1⟩ (.node .empty ⟨3,false,3,0⟩ .empty)) ⟨3,false,7,1⟩ (.node (.node .empty ⟨3,false,7,8⟩ .empty) ⟨3,false,7,32⟩ (.node .empty ⟨3,false,8,0⟩ .empty)))
def t74_92 : Tree := .node t74_83 ⟨2,true,17,0⟩ t84_92
def t93_101 : Tree := (.node (.node (.node (.node .empty ⟨3,false,8,31⟩ .empty) ⟨3,false,12,1⟩ .empty) ⟨3,false,12,6⟩ (.node .empty ⟨3,false,12,8⟩ .empty)) ⟨3,false,12,27⟩ (.node (.node .empty ⟨3,false,12,32⟩ .empty) ⟨3,false,13,0⟩ (.node .empty ⟨3,false,13,7⟩ .empty)))
def t102_110 : Tree := (.node (.node (.node (.node .empty ⟨3,false,13,26⟩ .empty) ⟨3,false,13,31⟩ .empty) ⟨3,false,17,1⟩ (.node .empty ⟨3,false,17,6⟩ .empty)) ⟨3,false,17,8⟩ (.node (.node .empty ⟨3,false,17,27⟩ .empty) ⟨3,false,17,32⟩ (.node .empty ⟨3,true,1,2⟩ .empty)))
def t93_110 : Tree := .node t93_101 ⟨3,false,13,15⟩ t102_110
def t74_110 : Tree := .node t74_92 ⟨3,false,8,7⟩ t93_110
def t111_119 : Tree := (.node (.node (.node (.node .empty ⟨3,true,6,19⟩ .empty) ⟨3,true,11,2⟩ .empty) ⟨3,true,11,19⟩ (.node .empty ⟨3,true,11,28⟩ .empty)) ⟨3,true,13,0⟩ (.node (.node .empty ⟨3,true,13,5⟩ .empty) ⟨3,true,13,7⟩ (.node .empty ⟨3,true,13,15⟩ .empty)))
def t120_128 : Tree := (.node (.node (.node (.node .empty ⟨3,true,13,31⟩ .empty) ⟨3,true,16,2⟩ .empty) ⟨3,true,16,19⟩ (.node .empty ⟨3,true,16,28⟩ .empty)) ⟨3,true,20,2⟩ (.node (.node .empty ⟨3,true,20,19⟩ .empty) ⟨3,true,20,28⟩ (.node .empty ⟨4,false,0,6⟩ .empty)))
def t111_128 : Tree := .node t111_119 ⟨3,true,13,26⟩ t120_128
def t129_137 : Tree := (.node (.node (.node (.node .empty ⟨4,false,4,4⟩ .empty) ⟨4,false,4,8⟩ .empty) ⟨4,false,4,10⟩ (.node .empty ⟨4,false,4,14⟩ .empty)) ⟨4,false,4,17⟩ (.node (.node .empty ⟨4,false,9,5⟩ .empty) ⟨4,false,9,6⟩ (.node .empty ⟨4,false,9,8⟩ .empty)))
def t138_146 : Tree := (.node (.node (.node (.node .empty ⟨4,false,9,17⟩ .empty) ⟨4,false,9,21⟩ .empty) ⟨4,false,9,27⟩ (.node .empty ⟨4,false,9,32⟩ .empty)) ⟨4,false,14,0⟩ (.node (.node .empty ⟨4,false,14,4⟩ .empty) ⟨4,false,14,5⟩ (.node .empty ⟨4,false,14,14⟩ .empty)))
def t129_146 : Tree := .node t129_137 ⟨4,false,9,10⟩ t138_146
def t111_146 : Tree := .node t111_128 ⟨4,false,0,10⟩ t129_146
def t74_146 : Tree := .node t74_110 ⟨3,true,6,2⟩ t111_146
def t0_146 : Tree := .node t0_73 ⟨2,false,17,1⟩ t74_146
def t147_156 : Tree := (.node (.node (.node (.node .empty ⟨4,false,14,25⟩ .empty) ⟨4,false,14,30⟩ .empty) ⟨4,false,18,4⟩ (.node .empty ⟨4,false,18,5⟩ .empty)) ⟨4,false,18,6⟩ (.node (.node (.node .empty ⟨4,false,18,8⟩ .empty) ⟨4,false,18,10⟩ .empty) ⟨4,false,18,14⟩ (.node .empty ⟨4,false,18,17⟩ .empty)))
def t157_165 : Tree := (.node (.node (.node (.node .empty ⟨4,false,18,25⟩ .empty) ⟨4,false,18,27⟩ .empty) ⟨4,false,18,30⟩ (.node .empty ⟨4,false,18,32⟩ .empty)) ⟨4,true,0,8⟩ (.node (.node .empty ⟨4,true,0,10⟩ .empty) ⟨4,true,0,17⟩ (.node .empty ⟨4,true,2,1⟩ .empty)))
def t147_165 : Tree := .node t147_156 ⟨4,false,18,21⟩ t157_165
def t166_174 : Tree := (.node (.node (.node (.node .empty ⟨4,true,4,8⟩ .empty) ⟨4,true,4,10⟩ .empty) ⟨4,true,4,17⟩ (.node .empty ⟨4,true,4,27⟩ .empty)) ⟨4,true,4,32⟩ (.node (.node .empty ⟨4,true,7,1⟩ .empty) ⟨4,true,7,8⟩ (.node .empty ⟨4,true,7,32⟩ .empty)))
def t175_183 : Tree := (.node (.node (.node (.node .empty ⟨4,true,9,8⟩ .empty) ⟨4,true,9,10⟩ .empty) ⟨4,true,9,17⟩ (.node .empty ⟨4,true,9,27⟩ .empty)) ⟨4,true,9,32⟩ (.node (.node .empty ⟨4,true,11,12⟩ .empty) ⟨4,true,11,23⟩ (.node .empty ⟨4,true,12,1⟩ .empty)))
def t166_183 : Tree := .node t166_174 ⟨4,true,9,6⟩ t175_183
def t147_183 : Tree := .node t147_165 ⟨4,true,4,6⟩ t166_183
def t184_193 : Tree := (.node (.node (.node (.node .empty ⟨4,true,12,8⟩ .empty) ⟨4,true,12,27⟩ .empty) ⟨4,true,12,32⟩ (.node .empty ⟨4,true,16,12⟩ .empty)) ⟨4,true,16,23⟩ (.node (.node (.node .empty ⟨4,true,17,1⟩ .empty) ⟨4,true,17,6⟩ .empty) ⟨4,true,17,8⟩ (.node .empty ⟨4,true,17,27⟩ .empty)))
def t194_202 : Tree := (.node (.node (.node (.node .empty ⟨4,true,18,6⟩ .empty) ⟨4,true,18,8⟩ .empty) ⟨4,true,18,10⟩ (.node .empty ⟨4,true,18,17⟩ .empty)) ⟨4,true,18,27⟩ (.node (.node .empty ⟨4,true,18,32⟩ .empty) ⟨4,true,20,12⟩ (.node .empty ⟨4,true,20,23⟩ .empty)))
def t184_202 : Tree := .node t184_193 ⟨4,true,17,32⟩ t194_202
def t203_211 : Tree := (.node (.node (.node (.node .empty ⟨5,false,0,9⟩ .empty) ⟨5,false,0,18⟩ .empty) ⟨5,false,1,7⟩ (.node .empty ⟨5,false,1,9⟩ .empty)) ⟨5,false,1,16⟩ (.node (.node .empty ⟨5,false,1,18⟩ .empty) ⟨5,false,1,33⟩ (.node .empty ⟨5,false,5,7⟩ .empty)))
def t212_220 : Tree := (.node (.node (.node (.node .empty ⟨5,false,5,15⟩ .empty) ⟨5,false,5,16⟩ .empty) ⟨5,false,5,18⟩ (.node .empty ⟨5,false,5,26⟩ .empty)) ⟨5,false,5,31⟩ (.node (.node .empty ⟨5,false,5,33⟩ .empty) ⟨5,false,10,7⟩ (.node .empty ⟨5,false,10,9⟩ .empty)))
def t203_220 : Tree := .node t203_211 ⟨5,false,5,9⟩ t212_220
def t184_220 : Tree := .node t184_202 ⟨5,false,0,5⟩ t203_220
def t147_220 : Tree := .node t147_183 ⟨4,true,12,6⟩ t184_220
def t221_230 : Tree := (.node (.node (.node (.node .empty ⟨5,false,10,16⟩ .empty) ⟨5,false,10,18⟩ .empty) ⟨5,false,10,26⟩ (.node .empty ⟨5,false,10,31⟩ .empty)) ⟨5,false,10,33⟩ (.node (.node (.node .empty ⟨5,false,12,11⟩ .empty) ⟨5,false,12,22⟩ .empty) ⟨5,false,17,11⟩ (.node .empty ⟨5,false,17,22⟩ .empty)))
def t231_239 : Tree := (.node (.node (.node (.node .empty ⟨5,false,19,9⟩ .empty) ⟨5,false,19,15⟩ .empty) ⟨5,false,19,16⟩ (.node .empty ⟨5,false,19,18⟩ .empty)) ⟨5,false,19,26⟩ (.node (.node .empty ⟨5,false,19,31⟩ .empty) ⟨5,false,19,33⟩ (.node .empty ⟨5,true,0,4⟩ .empty)))
def t221_239 : Tree := .node t221_230 ⟨5,false,19,7⟩ t231_239
def t240_248 : Tree := (.node (.node (.node (.node .empty ⟨5,true,4,5⟩ .empty) ⟨5,true,4,21⟩ .empty) ⟨5,true,5,4⟩ (.node .empty ⟨5,true,5,20⟩ .empty)) ⟨5,true,6,3⟩ (.node (.node .empty ⟨5,true,6,9⟩ .empty) ⟨5,true,6,33⟩ (.node .empty ⟨5,true,9,5⟩ .empty)))
def t249_257 : Tree := (.node (.node (.node (.node .empty ⟨5,true,9,21⟩ .empty) ⟨5,true,9,25⟩ .empty) ⟨5,true,9,30⟩ (.node .empty ⟨5,true,10,4⟩ .empty)) ⟨5,true,10,13⟩ (.node (.node .empty ⟨5,true,10,20⟩ .empty) ⟨5,true,10,24⟩ (.node .empty ⟨5,true,10,29⟩ .empty)))
def t240_257 : Tree := .node t240_248 ⟨5,true,9,14⟩ t249_257
def t221_257 : Tree := .node t221_239 ⟨5,true,1,3⟩ t240_257
def t258_266 : Tree := (.node (.node (.node (.node .empty ⟨5,true,11,9⟩ .empty) ⟨5,true,11,16⟩ .empty) ⟨5,true,11,33⟩ (.node .empty ⟨5,true,13,7⟩ .empty)) ⟨5,true,13,15⟩ (.node (.node .empty ⟨5,true,13,26⟩ .empty) ⟨5,true,13,31⟩ (.node .empty ⟨5,true,14,5⟩ .empty)))
def t267_275 : Tree := (.node (.node (.node (.node .empty ⟨5,true,14,21⟩ .empty) ⟨5,true,14,25⟩ .empty) ⟨5,true,14,30⟩ (.node .empty ⟨5,true,15,4⟩ .empty)) ⟨5,true,15,13⟩ (.node (.node .empty ⟨5,true,15,20⟩ .empty) ⟨5,true,15,24⟩ (.node .empty ⟨5,true,15,29⟩ .empty)))
def t258_275 : Tree := .node t258_266 ⟨5,true,14,14⟩ t267_275
def t276_284 : Tree := (.node (.node (.node (.node .empty ⟨5,true,16,9⟩ .empty) ⟨5,true,16,16⟩ .empty) ⟨5,true,16,33⟩ (.node .empty ⟨5,true,18,5⟩ .empty)) ⟨5,true,18,14⟩ (.node (.node .empty ⟨5,true,18,21⟩ .empty) ⟨5,true,18,25⟩ (.node .empty ⟨5,true,18,30⟩ .empty)))
def t285_293 : Tree := (.node (.node (.node (.node .empty ⟨5,true,19,13⟩ .empty) ⟨5,true,19,20⟩ .empty) ⟨5,true,19,24⟩ (.node .empty ⟨5,true,19,29⟩ .empty)) ⟨5,true,20,3⟩ (.node (.node .empty ⟨5,true,20,9⟩ .empty) ⟨5,true,20,16⟩ (.node .empty ⟨5,true,20,33⟩ .empty)))
def t276_293 : Tree := .node t276_284 ⟨5,true,19,4⟩ t285_293
def t258_293 : Tree := .node t258_275 ⟨5,true,16,3⟩ t276_293
def t221_293 : Tree := .node t221_257 ⟨5,true,11,3⟩ t258_293
def t147_293 : Tree := .node t147_220 ⟨5,false,10,15⟩ t221_293
def t0_293 : Tree := .node t0_146 ⟨4,false,14,21⟩ t147_293
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 0, 0, 0, 0, 5, 9, 6, 0, 7, 8, 0, 0, 0, 0, 10, 18, 11, 0, 12, 13, 0, 0, 14, 0, 15, 0, 16, 0, 17, 13, 0, 0, 19, 18, 20, 0, 12],#[0, 1, 3, 2, 0, 0, 4, 0, 5, 0, 7, 6, 16, 28, 11, 8, 9, 19, 20, 10, 18, 0, 0, 12, 13, 0, 14, 0, 15, 0, 22, 6, 29, 17, 18, 0, 0, 10, 0, 0, 21, 0, 7, 0, 0, 23, 24, 0, 25, 0, 26, 0, 22, 27, 16, 28, 0, 0, 30, 0, 31, 0, 11, 32, 33, 19, 20, 17],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,4)],[(true,5)],[(true,6)],[(false,7)],[(false,5)],[(true,9)],[(true,10)],[(true,11),(true,20)],[(false,12),(false,17)],[(true,13)],[(true,14)],[(true,15)],[(true,16)],[(false,10),(false,19)],[(true,18)],[(true,19)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(false,4)],[(true,5),(true,15)],[(false,5),(false,21)],[(true,7)],[(false,8)],[(true,9),(true,18)],[(false,7),(false,31)],[(true,11)],[(false,12)],[(false,13)],[(false,14)],[(false,6),(false,27)],[(true,16),(true,33)],[(false,10),(false,17)],[(true,8),(true,32)],[(false,9),(false,33)],[(false,20)],[(false,15),(false,26)],[(true,22)],[(false,23)],[(false,24)],[(false,25)],[(true,26)],[(true,6),(true,27)],[(false,16)],[(false,29)],[(false,30)],[(true,31)],[(false,32)]],
  t0_293⟩
theorem check0_9 : t0_9.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check10_18 : t10_18.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node9 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,15,20⟩ = true := by decide
theorem check0_18 : t0_18.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node9 check0_9 check10_18
theorem check19_27 : t19_27.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check28_36 : t28_36.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node27 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,10,5⟩ = true := by decide
theorem check19_36 : t19_36.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node27 check19_27 check28_36
theorem node18 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,1,5⟩ = true := by decide
theorem check0_36 : t0_36.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node18 check0_18 check19_36
theorem check37_46 : t37_46.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check47_55 : t47_55.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node46 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,6,1⟩ = true := by decide
theorem check37_55 : t37_55.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node46 check37_46 check47_55
theorem check56_64 : t56_64.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check65_73 : t65_73.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node64 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,20,23⟩ = true := by decide
theorem check56_73 : t56_73.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node64 check56_64 check65_73
theorem node55 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,16,12⟩ = true := by decide
theorem check37_73 : t37_73.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node55 check37_55 check56_73
theorem node36 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,19,5⟩ = true := by decide
theorem check0_73 : t0_73.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node36 check0_36 check37_73
theorem check74_83 : t74_83.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check84_92 : t84_92.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node83 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,17,0⟩ = true := by decide
theorem check74_92 : t74_92.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node83 check74_83 check84_92
theorem check93_101 : t93_101.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check102_110 : t102_110.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node101 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,13,15⟩ = true := by decide
theorem check93_110 : t93_110.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node101 check93_101 check102_110
theorem node92 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,8,7⟩ = true := by decide
theorem check74_110 : t74_110.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node92 check74_92 check93_110
theorem check111_119 : t111_119.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check120_128 : t120_128.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node119 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,13,26⟩ = true := by decide
theorem check111_128 : t111_128.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node119 check111_119 check120_128
theorem check129_137 : t129_137.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check138_146 : t138_146.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node137 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,9,10⟩ = true := by decide
theorem check129_146 : t129_146.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node137 check129_137 check138_146
theorem node128 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,0,10⟩ = true := by decide
theorem check111_146 : t111_146.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node128 check111_128 check129_146
theorem node110 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,6,2⟩ = true := by decide
theorem check74_146 : t74_146.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node110 check74_110 check111_146
theorem node73 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,17,1⟩ = true := by decide
theorem check0_146 : t0_146.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node73 check0_73 check74_146
theorem check147_156 : t147_156.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check157_165 : t157_165.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node156 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,18,21⟩ = true := by decide
theorem check147_165 : t147_165.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node156 check147_156 check157_165
theorem check166_174 : t166_174.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check175_183 : t175_183.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node174 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,9,6⟩ = true := by decide
theorem check166_183 : t166_183.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node174 check166_174 check175_183
theorem node165 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,4,6⟩ = true := by decide
theorem check147_183 : t147_183.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node165 check147_165 check166_183
theorem check184_193 : t184_193.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check194_202 : t194_202.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node193 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,17,32⟩ = true := by decide
theorem check184_202 : t184_202.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node193 check184_193 check194_202
theorem check203_211 : t203_211.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check212_220 : t212_220.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node211 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,5,9⟩ = true := by decide
theorem check203_220 : t203_220.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node211 check203_211 check212_220
theorem node202 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,0,5⟩ = true := by decide
theorem check184_220 : t184_220.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node202 check184_202 check203_220
theorem node183 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,12,6⟩ = true := by decide
theorem check147_220 : t147_220.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node183 check147_183 check184_220
theorem check221_230 : t221_230.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check231_239 : t231_239.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node230 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,19,7⟩ = true := by decide
theorem check221_239 : t221_239.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node230 check221_230 check231_239
theorem check240_248 : t240_248.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check249_257 : t249_257.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node248 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,9,14⟩ = true := by decide
theorem check240_257 : t240_257.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node248 check240_248 check249_257
theorem node239 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,1,3⟩ = true := by decide
theorem check221_257 : t221_257.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node239 check221_239 check240_257
theorem check258_266 : t258_266.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check267_275 : t267_275.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node266 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,14,14⟩ = true := by decide
theorem check258_275 : t258_275.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node266 check258_266 check267_275
theorem check276_284 : t276_284.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check285_293 : t285_293.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node284 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,19,4⟩ = true := by decide
theorem check276_293 : t276_293.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node284 check276_284 check285_293
theorem node275 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,16,3⟩ = true := by decide
theorem check258_293 : t258_293.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node275 check258_275 check276_293
theorem node257 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,11,3⟩ = true := by decide
theorem check221_293 : t221_293.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node257 check221_257 check258_293
theorem node220 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,10,15⟩ = true := by decide
theorem check147_293 : t147_293.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node220 check147_220 check221_293
theorem node146 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,14,21⟩ = true := by decide
theorem check0_293 : t0_293.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node146 check0_146 check147_293
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_293
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M059
