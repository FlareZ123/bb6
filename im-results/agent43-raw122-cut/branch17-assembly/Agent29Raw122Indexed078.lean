import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M078
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def t0_8 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,6⟩ .empty) ⟨0,false,0,14⟩ (.node .empty ⟨0,false,2,17⟩ .empty)) ⟨0,false,2,32⟩ (.node (.node .empty ⟨0,false,4,1⟩ .empty) ⟨0,false,4,9⟩ (.node .empty ⟨0,false,4,23⟩ .empty)))
def t9_17 : Tree := (.node (.node (.node (.node .empty ⟨0,false,4,35⟩ .empty) ⟨0,false,6,0⟩ .empty) ⟨0,false,6,20⟩ (.node .empty ⟨0,false,6,38⟩ .empty)) ⟨0,false,13,17⟩ (.node (.node .empty ⟨0,false,17,1⟩ .empty) ⟨0,false,19,0⟩ (.node .empty ⟨0,false,21,20⟩ .empty)))
def t0_17 : Tree := .node t0_8 ⟨0,false,4,25⟩ t9_17
def t18_34 : Tree := (.node (.node (.node (.node (.node .empty ⟨0,false,23,12⟩ .empty) ⟨0,false,23,23⟩ .empty) ⟨0,false,25,9⟩ (.node .empty ⟨0,false,25,20⟩ .empty)) ⟨0,false,25,38⟩ (.node (.node .empty ⟨0,false,27,12⟩ .empty) ⟨0,false,27,23⟩ (.node .empty ⟨0,true,3,22⟩ .empty))) ⟨0,true,4,6⟩ (.node (.node (.node .empty ⟨0,true,4,17⟩ .empty) ⟨0,true,4,23⟩ (.node .empty ⟨0,true,6,6⟩ .empty)) ⟨0,true,6,17⟩ (.node (.node .empty ⟨0,true,6,23⟩ .empty) ⟨0,true,10,28⟩ (.node .empty ⟨0,true,12,18⟩ .empty))))
def t0_34 : Tree := .node t0_17 ⟨0,false,21,38⟩ t18_34
def t35_51 : Tree := (.node (.node (.node (.node (.node .empty ⟨0,true,16,18⟩ .empty) ⟨0,true,16,27⟩ .empty) ⟨0,true,17,6⟩ (.node .empty ⟨0,true,23,17⟩ .empty)) ⟨0,true,27,6⟩ (.node (.node .empty ⟨0,true,27,17⟩ .empty) ⟨0,true,30,18⟩ (.node .empty ⟨0,true,30,27⟩ .empty))) ⟨1,false,1,0⟩ (.node (.node (.node .empty ⟨1,false,1,5⟩ .empty) ⟨1,false,1,13⟩ (.node .empty ⟨1,false,1,26⟩ .empty)) ⟨1,false,1,39⟩ (.node (.node .empty ⟨1,false,3,28⟩ .empty) ⟨1,false,7,0⟩ (.node .empty ⟨1,false,10,16⟩ .empty))))
def t52_68 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,false,10,37⟩ .empty) ⟨1,false,12,8⟩ .empty) ⟨1,false,12,24⟩ (.node .empty ⟨1,false,12,34⟩ .empty)) ⟨1,false,14,5⟩ (.node (.node .empty ⟨1,false,14,16⟩ .empty) ⟨1,false,14,37⟩ (.node .empty ⟨1,false,16,8⟩ .empty))) ⟨1,false,16,34⟩ (.node (.node (.node .empty ⟨1,false,20,0⟩ .empty) ⟨1,false,28,16⟩ (.node .empty ⟨1,false,28,37⟩ .empty)) ⟨1,false,30,8⟩ (.node (.node .empty ⟨1,false,30,34⟩ .empty) ⟨1,false,32,5⟩ (.node .empty ⟨1,false,32,16⟩ .empty))))
def t35_68 : Tree := .node t35_51 ⟨1,false,10,31⟩ t52_68
def t0_68 : Tree := .node t0_34 ⟨0,true,12,27⟩ t35_68
def t69_77 : Tree := (.node (.node (.node (.node .empty ⟨1,true,3,3⟩ .empty) ⟨1,true,3,11⟩ .empty) ⟨1,true,3,24⟩ (.node .empty ⟨1,true,3,27⟩ .empty)) ⟨1,true,3,28⟩ (.node (.node .empty ⟨1,true,3,43⟩ .empty) ⟨1,true,5,0⟩ (.node .empty ⟨1,true,5,8⟩ .empty)))
def t78_86 : Tree := (.node (.node (.node (.node .empty ⟨1,true,5,24⟩ .empty) ⟨1,true,5,34⟩ .empty) ⟨1,true,7,18⟩ (.node .empty ⟨1,true,7,27⟩ .empty)) ⟨1,true,14,22⟩ (.node (.node .empty ⟨1,true,16,3⟩ .empty) ⟨1,true,18,0⟩ (.node .empty ⟨1,true,22,18⟩ .empty)))
def t69_86 : Tree := .node t69_77 ⟨1,true,5,22⟩ t78_86
def t87_103 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,true,24,11⟩ .empty) ⟨1,true,24,22⟩ .empty) ⟨1,true,26,8⟩ (.node .empty ⟨1,true,26,18⟩ .empty)) ⟨1,true,26,27⟩ (.node (.node .empty ⟨2,false,2,0⟩ .empty) ⟨2,false,2,41⟩ (.node .empty ⟨2,false,3,7⟩ .empty))) ⟨2,false,3,27⟩ (.node (.node (.node .empty ⟨2,false,3,33⟩ .empty) ⟨2,false,5,7⟩ (.node .empty ⟨2,false,5,27⟩ .empty)) ⟨2,false,5,33⟩ (.node (.node .empty ⟨2,false,7,7⟩ .empty) ⟨2,false,7,33⟩ (.node .empty ⟨2,false,8,0⟩ .empty))))
def t69_103 : Tree := .node t69_86 ⟨1,true,22,27⟩ t87_103
def t104_120 : Tree := (.node (.node (.node (.node (.node .empty ⟨2,false,15,19⟩ .empty) ⟨2,false,16,7⟩ .empty) ⟨2,false,22,33⟩ (.node .empty ⟨2,false,26,7⟩ .empty)) ⟨2,false,26,33⟩ (.node (.node .empty ⟨2,false,29,19⟩ .empty) ⟨2,false,33,25⟩ (.node .empty ⟨2,true,2,4⟩ .empty))) ⟨2,true,2,12⟩ (.node (.node (.node .empty ⟨2,true,2,25⟩ .empty) ⟨2,true,2,29⟩ (.node .empty ⟨2,true,2,38⟩ .empty)) ⟨2,true,2,40⟩ (.node (.node .empty ⟨2,true,11,15⟩ .empty) ⟨2,true,11,30⟩ (.node .empty ⟨2,true,11,36⟩ .empty))))
def t121_137 : Tree := (.node (.node (.node (.node (.node .empty ⟨2,true,13,17⟩ .empty) ⟨2,true,13,23⟩ .empty) ⟨2,true,15,4⟩ (.node .empty ⟨2,true,15,15⟩ .empty)) ⟨2,true,15,36⟩ (.node (.node .empty ⟨2,true,29,15⟩ .empty) ⟨2,true,29,36⟩ (.node .empty ⟨2,true,31,6⟩ .empty))) ⟨2,true,31,17⟩ (.node (.node (.node .empty ⟨3,false,2,1⟩ .empty) ⟨3,false,2,9⟩ (.node .empty ⟨3,false,2,23⟩ .empty)) ⟨3,false,2,25⟩ (.node (.node .empty ⟨3,false,2,35⟩ .empty) ⟨3,false,3,0⟩ (.node .empty ⟨3,false,3,8⟩ .empty))))
def t104_137 : Tree := .node t104_120 ⟨2,true,13,6⟩ t121_137
def t69_137 : Tree := .node t69_103 ⟨2,false,11,19⟩ t104_137
def t0_137 : Tree := .node t0_68 ⟨1,false,32,37⟩ t69_137
def t138_146 : Tree := (.node (.node (.node (.node .empty ⟨3,false,3,24⟩ .empty) ⟨3,false,3,34⟩ .empty) ⟨3,false,4,6⟩ (.node .empty ⟨3,false,4,17⟩ .empty)) ⟨3,false,4,23⟩ (.node (.node .empty ⟨3,false,5,8⟩ .empty) ⟨3,false,5,24⟩ (.node .empty ⟨3,false,5,34⟩ .empty)))
def t147_155 : Tree := (.node (.node (.node (.node .empty ⟨3,false,6,17⟩ .empty) ⟨3,false,6,23⟩ .empty) ⟨3,false,7,8⟩ (.node .empty ⟨3,false,7,34⟩ .empty)) ⟨3,false,8,1⟩ (.node (.node .empty ⟨3,false,9,0⟩ .empty) ⟨3,false,11,20⟩ (.node .empty ⟨3,false,11,38⟩ .empty)))
def t138_155 : Tree := .node t138_146 ⟨3,false,6,6⟩ t147_155
def t156_172 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,false,12,27⟩ .empty) ⟨3,false,15,9⟩ .empty) ⟨3,false,15,20⟩ (.node .empty ⟨3,false,15,38⟩ .empty)) ⟨3,false,16,8⟩ (.node (.node .empty ⟨3,false,16,18⟩ .empty) ⟨3,false,16,27⟩ (.node .empty ⟨3,false,17,6⟩ .empty))) ⟨3,false,22,34⟩ (.node (.node (.node .empty ⟨3,false,23,17⟩ .empty) ⟨3,false,26,8⟩ (.node .empty ⟨3,false,26,34⟩ .empty)) ⟨3,false,27,6⟩ (.node (.node .empty ⟨3,false,27,17⟩ .empty) ⟨3,false,29,20⟩ (.node .empty ⟨3,false,29,38⟩ .empty))))
def t138_172 : Tree := .node t138_155 ⟨3,false,12,18⟩ t156_172
def t173_189 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,false,30,27⟩ .empty) ⟨3,true,1,2⟩ .empty) ⟨3,true,1,10⟩ (.node .empty ⟨3,true,1,24⟩ .empty)) ⟨3,true,1,26⟩ (.node (.node .empty ⟨3,true,1,42⟩ .empty) ⟨3,true,4,9⟩ (.node .empty ⟨3,true,4,25⟩ .empty))) ⟨3,true,4,35⟩ (.node (.node (.node .empty ⟨3,true,6,9⟩ .empty) ⟨3,true,6,35⟩ (.node .empty ⟨3,true,7,2⟩ .empty)) ⟨3,true,10,21⟩ (.node (.node .empty ⟨3,true,10,39⟩ .empty) ⟨3,true,14,10⟩ (.node .empty ⟨3,true,14,21⟩ .empty))))
def t190_206 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,true,20,2⟩ .empty) ⟨3,true,21,35⟩ .empty) ⟨3,true,25,9⟩ (.node .empty ⟨3,true,25,35⟩ .empty)) ⟨3,true,28,21⟩ (.node (.node .empty ⟨3,true,28,39⟩ .empty) ⟨3,true,32,10⟩ (.node .empty ⟨3,true,32,21⟩ .empty))) ⟨3,true,32,39⟩ (.node (.node (.node .empty ⟨3,true,34,24⟩ .empty) ⟨4,true,2,1⟩ (.node .empty ⟨4,true,2,9⟩ .empty)) ⟨4,true,2,23⟩ (.node (.node .empty ⟨4,true,2,25⟩ .empty) ⟨4,true,2,35⟩ (.node .empty ⟨4,true,5,8⟩ .empty))))
def t173_206 : Tree := .node t173_189 ⟨3,true,14,39⟩ t190_206
def t138_206 : Tree := .node t138_172 ⟨3,false,30,18⟩ t173_206
def t207_215 : Tree := (.node (.node (.node (.node .empty ⟨4,true,5,34⟩ .empty) ⟨4,true,7,8⟩ .empty) ⟨4,true,7,34⟩ (.node .empty ⟨4,true,8,1⟩ .empty)) ⟨4,true,11,20⟩ (.node (.node .empty ⟨4,true,11,38⟩ .empty) ⟨4,true,15,9⟩ (.node .empty ⟨4,true,15,20⟩ .empty)))
def t216_224 : Tree := (.node (.node (.node (.node .empty ⟨4,true,22,34⟩ .empty) ⟨4,true,26,8⟩ .empty) ⟨4,true,26,34⟩ (.node .empty ⟨4,true,29,20⟩ .empty)) ⟨4,true,29,38⟩ (.node (.node .empty ⟨4,true,35,23⟩ .empty) ⟨5,false,0,5⟩ (.node .empty ⟨5,false,0,13⟩ .empty)))
def t207_224 : Tree := .node t207_215 ⟨4,true,15,38⟩ t216_224
def t225_241 : Tree := (.node (.node (.node (.node (.node .empty ⟨5,false,0,39⟩ .empty) ⟨5,false,3,16⟩ .empty) ⟨5,false,3,31⟩ (.node .empty ⟨5,false,3,37⟩ .empty)) ⟨5,false,5,5⟩ (.node (.node .empty ⟨5,false,5,16⟩ .empty) ⟨5,false,5,37⟩ (.node .empty ⟨5,false,11,25⟩ .empty))) ⟨5,false,13,12⟩ (.node (.node (.node .empty ⟨5,false,13,23⟩ .empty) ⟨5,false,14,37⟩ (.node .empty ⟨5,false,18,5⟩ .empty)) ⟨5,false,24,16⟩ (.node (.node .empty ⟨5,false,24,37⟩ .empty) ⟨5,false,31,12⟩ (.node .empty ⟨5,false,31,23⟩ .empty))))
def t207_241 : Tree := .node t207_224 ⟨5,false,0,26⟩ t225_241
def t242_258 : Tree := (.node (.node (.node (.node (.node .empty ⟨5,true,0,4⟩ .empty) ⟨5,true,0,12⟩ .empty) ⟨5,true,0,25⟩ (.node .empty ⟨5,true,0,29⟩ .empty)) ⟨5,true,0,38⟩ (.node (.node .empty ⟨5,true,1,3⟩ .empty) ⟨5,true,1,11⟩ (.node .empty ⟨5,true,1,24⟩ .empty))) ⟨5,true,1,27⟩ (.node (.node (.node .empty ⟨5,true,1,28⟩ .empty) ⟨5,true,1,43⟩ (.node .empty ⟨5,true,2,23⟩ .empty)) ⟨5,true,4,15⟩ (.node (.node .empty ⟨5,true,4,30⟩ .empty) ⟨5,true,4,36⟩ (.node .empty ⟨5,true,6,4⟩ .empty))))
def t259_275 : Tree := (.node (.node (.node (.node (.node .empty ⟨5,true,6,36⟩ .empty) ⟨5,true,7,3⟩ .empty) ⟨5,true,10,22⟩ (.node .empty ⟨5,true,12,24⟩ .empty)) ⟨5,true,13,23⟩ (.node (.node .empty ⟨5,true,14,11⟩ .empty) ⟨5,true,14,22⟩ (.node .empty ⟨5,true,19,4⟩ .empty))) ⟨5,true,20,3⟩ (.node (.node (.node .empty ⟨5,true,21,36⟩ .empty) ⟨5,true,25,15⟩ (.node .empty ⟨5,true,25,36⟩ .empty)) ⟨5,true,28,22⟩ (.node (.node .empty ⟨5,true,32,11⟩ .empty) ⟨5,true,32,22⟩ (.node .empty ⟨5,true,34,27⟩ .empty))))
def t242_275 : Tree := .node t242_258 ⟨5,true,6,15⟩ t259_275
def t207_275 : Tree := .node t207_241 ⟨5,false,33,38⟩ t242_275
def t138_275 : Tree := .node t138_206 ⟨4,true,5,24⟩ t207_275
def t0_275 : Tree := .node t0_137 ⟨3,false,3,22⟩ t138_275
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 10, 4, 33, 0, 5, 6, 0, 0, 7, 27, 8, 9, 0, 0, 0, 0, 11, 12, 0, 0, 13, 14, 28, 21, 15, 16, 0, 17, 31, 0, 18, 19, 0, 0, 20, 0, 8, 0, 22, 23, 0, 0, 24, 25, 0, 0, 26, 27, 0, 0, 24, 0, 29, 30, 0, 0, 31, 32, 0, 0, 15, 34, 0, 0, 35, 0, 0],#[0, 1, 3, 2, 0, 0, 0, 4, 0, 5, 6, 0, 7, 8, 0, 0, 15, 9, 11, 10, 0, 0, 0, 12, 18, 13, 14, 0, 0, 0, 0, 16, 17, 0, 33, 34, 19, 20, 0, 0, 22, 21, 0, 0, 41, 23, 27, 24, 30, 25, 28, 26, 14, 0, 19, 38, 40, 29, 0, 13, 0, 31, 32, 0, 0, 0, 0, 0, 36, 35, 43, 42, 0, 37, 17, 0, 22, 39, 14, 0, 0, 0, 0, 0, 0, 0, 0, 29],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,3)],[(true,4)],[(false,5)],[(true,6)],[(true,7),(true,20)],[(false,8)],[(true,2)],[(true,10)],[(false,11)],[(true,12)],[(false,13)],[(true,14),(true,32)],[(false,15)],[(false,16)],[(true,17)],[(false,18)],[(true,19)],[(false,14)],[(true,21)],[(false,22)],[(true,23),(true,27)],[(false,24)],[(true,25)],[(false,7),(false,26)],[(true,13)],[(true,28)],[(false,29)],[(true,16),(true,30)],[(false,31)],[(true,3)],[(false,33)],[(true,34)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3)],[(true,4)],[(false,5)],[(false,6)],[(true,6)],[(true,8)],[(true,9)],[(false,9)],[(true,11)],[(true,12),(true,29)],[(false,13),(false,26),(false,39)],[(false,8)],[(true,15)],[(false,16),(false,37)],[(false,12)],[(false,18),(false,27)],[(true,18)],[(true,20)],[(false,20),(false,38)],[(true,22)],[(true,23)],[(true,24)],[(true,25)],[(false,23)],[(false,25)],[(true,28),(true,43)],[(false,24)],[(true,30)],[(false,31)],[(false,17)],[(true,17)],[(true,34)],[(false,34)],[(true,36)],[(true,27)],[(true,38)],[(false,28)],[(false,22)],[(true,35)],[(false,35)]],
  t0_275⟩
theorem check0_8 : t0_8.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check9_17 : t9_17.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node8 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,4,25⟩ = true := by decide
theorem check0_17 : t0_17.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node8 check0_8 check9_17
theorem check18_34 : t18_34.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node17 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,21,38⟩ = true := by decide
theorem check0_34 : t0_34.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node17 check0_17 check18_34
theorem check35_51 : t35_51.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check52_68 : t52_68.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node51 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,10,31⟩ = true := by decide
theorem check35_68 : t35_68.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node51 check35_51 check52_68
theorem node34 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,12,27⟩ = true := by decide
theorem check0_68 : t0_68.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node34 check0_34 check35_68
theorem check69_77 : t69_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check78_86 : t78_86.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node77 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,5,22⟩ = true := by decide
theorem check69_86 : t69_86.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node77 check69_77 check78_86
theorem check87_103 : t87_103.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node86 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,22,27⟩ = true := by decide
theorem check69_103 : t69_103.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node86 check69_86 check87_103
theorem check104_120 : t104_120.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check121_137 : t121_137.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node120 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,13,6⟩ = true := by decide
theorem check104_137 : t104_137.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node120 check104_120 check121_137
theorem node103 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,11,19⟩ = true := by decide
theorem check69_137 : t69_137.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node103 check69_103 check104_137
theorem node68 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,32,37⟩ = true := by decide
theorem check0_137 : t0_137.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node68 check0_68 check69_137
theorem check138_146 : t138_146.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check147_155 : t147_155.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node146 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,6,6⟩ = true := by decide
theorem check138_155 : t138_155.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node146 check138_146 check147_155
theorem check156_172 : t156_172.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node155 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,12,18⟩ = true := by decide
theorem check138_172 : t138_172.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node155 check138_155 check156_172
theorem check173_189 : t173_189.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check190_206 : t190_206.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node189 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,14,39⟩ = true := by decide
theorem check173_206 : t173_206.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node189 check173_189 check190_206
theorem node172 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,30,18⟩ = true := by decide
theorem check138_206 : t138_206.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node172 check138_172 check173_206
theorem check207_215 : t207_215.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check216_224 : t216_224.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node215 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,15,38⟩ = true := by decide
theorem check207_224 : t207_224.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node215 check207_215 check216_224
theorem check225_241 : t225_241.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node224 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,0,26⟩ = true := by decide
theorem check207_241 : t207_241.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node224 check207_224 check225_241
theorem check242_258 : t242_258.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check259_275 : t259_275.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node258 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,6,15⟩ = true := by decide
theorem check242_275 : t242_275.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node258 check242_258 check259_275
theorem node241 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,33,38⟩ = true := by decide
theorem check207_275 : t207_275.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node241 check207_241 check242_275
theorem node206 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,5,24⟩ = true := by decide
theorem check138_275 : t138_275.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node206 check138_206 check207_275
theorem node137 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,3,22⟩ = true := by decide
theorem check0_275 : t0_275.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node137 check0_137 check138_275
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_275
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M078
