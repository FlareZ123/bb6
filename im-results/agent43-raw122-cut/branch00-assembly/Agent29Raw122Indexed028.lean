import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M028
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_8 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,5⟩ .empty) ⟨0,false,0,6⟩ (.node .empty ⟨0,false,0,9⟩ .empty)) ⟨0,false,0,12⟩ (.node (.node .empty ⟨0,false,0,13⟩ .empty) ⟨0,false,0,15⟩ (.node .empty ⟨0,false,0,16⟩ .empty)))
def t9_17 : Tree := (.node (.node (.node (.node .empty ⟨0,false,2,16⟩ .empty) ⟨0,false,2,18⟩ .empty) ⟨0,false,2,33⟩ (.node .empty ⟨0,false,2,37⟩ .empty)) ⟨0,false,4,0⟩ (.node (.node .empty ⟨0,false,8,25⟩ .empty) ⟨0,false,8,35⟩ (.node .empty ⟨0,false,8,39⟩ .empty)))
def t0_17 : Tree := .node t0_8 ⟨0,false,2,7⟩ t9_17
def t18_26 : Tree := (.node (.node (.node (.node .empty ⟨0,false,11,16⟩ .empty) ⟨0,false,11,18⟩ .empty) ⟨0,false,11,33⟩ (.node .empty ⟨0,false,11,37⟩ .empty)) ⟨0,false,13,17⟩ (.node (.node .empty ⟨0,false,13,35⟩ .empty) ⟨0,false,17,25⟩ (.node .empty ⟨0,false,17,35⟩ .empty)))
def t27_35 : Tree := (.node (.node (.node (.node .empty ⟨0,false,20,35⟩ .empty) ⟨0,false,20,39⟩ .empty) ⟨0,false,20,41⟩ (.node .empty ⟨0,false,24,35⟩ .empty)) ⟨0,false,24,39⟩ (.node (.node .empty ⟨0,false,24,41⟩ .empty) ⟨0,true,0,4⟩ (.node .empty ⟨0,true,0,11⟩ .empty)))
def t18_35 : Tree := .node t18_26 ⟨0,false,17,39⟩ t27_35
def t0_35 : Tree := .node t0_17 ⟨0,false,11,7⟩ t18_35
def t36_44 : Tree := (.node (.node (.node (.node .empty ⟨0,true,1,10⟩ .empty) ⟨0,true,1,12⟩ .empty) ⟨0,true,1,15⟩ (.node .empty ⟨0,true,1,22⟩ .empty)) ⟨0,true,1,34⟩ (.node (.node .empty ⟨0,true,2,11⟩ .empty) ⟨0,true,2,14⟩ (.node .empty ⟨0,true,2,21⟩ .empty)))
def t45_53 : Tree := (.node (.node (.node (.node .empty ⟨0,true,3,32⟩ .empty) ⟨0,true,3,36⟩ .empty) ⟨0,true,4,4⟩ (.node .empty ⟨0,true,4,31⟩ .empty)) ⟨0,true,4,33⟩ (.node (.node .empty ⟨0,true,4,37⟩ .empty) ⟨0,true,7,30⟩ (.node .empty ⟨0,true,7,32⟩ .empty)))
def t36_53 : Tree := .node t36_44 ⟨0,true,3,5⟩ t45_53
def t54_70 : Tree := (.node (.node (.node (.node (.node .empty ⟨0,true,8,29⟩ .empty) ⟨0,true,8,31⟩ .empty) ⟨0,true,8,33⟩ (.node .empty ⟨0,true,8,37⟩ .empty)) ⟨0,true,10,10⟩ (.node (.node .empty ⟨0,true,10,12⟩ .empty) ⟨0,true,10,15⟩ (.node .empty ⟨0,true,10,22⟩ .empty))) ⟨0,true,10,34⟩ (.node (.node (.node .empty ⟨0,true,11,11⟩ .empty) ⟨0,true,11,14⟩ (.node .empty ⟨0,true,11,21⟩ .empty)) ⟨0,true,12,5⟩ (.node (.node .empty ⟨0,true,12,32⟩ .empty) ⟨0,true,12,36⟩ (.node .empty ⟨0,true,13,4⟩ .empty))))
def t36_70 : Tree := .node t36_53 ⟨0,true,7,36⟩ t54_70
def t0_70 : Tree := .node t0_35 ⟨0,true,0,14⟩ t36_70
def t71_79 : Tree := (.node (.node (.node (.node .empty ⟨0,true,13,33⟩ .empty) ⟨0,true,13,37⟩ .empty) ⟨0,true,16,30⟩ (.node .empty ⟨0,true,16,32⟩ .empty)) ⟨0,true,16,36⟩ (.node (.node .empty ⟨0,true,17,29⟩ .empty) ⟨0,true,17,31⟩ (.node .empty ⟨0,true,17,33⟩ .empty)))
def t80_88 : Tree := (.node (.node (.node (.node .empty ⟨0,true,19,30⟩ .empty) ⟨0,true,19,32⟩ .empty) ⟨0,true,19,36⟩ (.node .empty ⟨0,true,20,29⟩ .empty)) ⟨0,true,20,31⟩ (.node (.node .empty ⟨0,true,20,33⟩ .empty) ⟨0,true,20,37⟩ (.node .empty ⟨0,true,23,30⟩ .empty)))
def t71_88 : Tree := .node t71_79 ⟨0,true,17,37⟩ t80_88
def t89_105 : Tree := (.node (.node (.node (.node (.node .empty ⟨0,true,23,36⟩ .empty) ⟨0,true,24,29⟩ .empty) ⟨0,true,24,31⟩ (.node .empty ⟨0,true,24,33⟩ .empty)) ⟨0,true,24,37⟩ (.node (.node .empty ⟨1,false,1,0⟩ .empty) ⟨1,false,1,5⟩ (.node .empty ⟨1,false,1,6⟩ .empty))) ⟨1,false,1,12⟩ (.node (.node (.node .empty ⟨1,false,1,13⟩ .empty) ⟨1,false,1,15⟩ (.node .empty ⟨1,false,5,1⟩ .empty)) ⟨1,false,7,0⟩ (.node (.node .empty ⟨1,false,10,13⟩ .empty) ⟨1,false,10,17⟩ (.node .empty ⟨1,false,10,23⟩ .empty))))
def t71_105 : Tree := .node t71_88 ⟨0,true,23,32⟩ t89_105
def t106_114 : Tree := (.node (.node (.node (.node .empty ⟨1,false,14,8⟩ .empty) ⟨1,false,14,36⟩ .empty) ⟨1,false,16,10⟩ (.node .empty ⟨1,false,16,34⟩ .empty)) ⟨1,false,19,24⟩ (.node (.node .empty ⟨1,false,19,34⟩ .empty) ⟨1,false,19,38⟩ (.node .empty ⟨1,false,19,40⟩ .empty)))
def t115_123 : Tree := (.node (.node (.node (.node .empty ⟨1,false,23,38⟩ .empty) ⟨1,false,23,40⟩ .empty) ⟨1,true,1,4⟩ (.node .empty ⟨1,true,1,11⟩ .empty)) ⟨1,true,1,14⟩ (.node (.node .empty ⟨1,true,10,5⟩ .empty) ⟨1,true,10,32⟩ (.node .empty ⟨1,true,10,36⟩ .empty)))
def t106_123 : Tree := .node t106_114 ⟨1,false,23,34⟩ t115_123
def t124_140 : Tree := (.node (.node (.node (.node (.node .empty ⟨2,false,0,15⟩ .empty) ⟨2,false,2,0⟩ .empty) ⟨2,false,2,5⟩ (.node .empty ⟨2,false,2,12⟩ .empty)) ⟨2,false,2,15⟩ (.node (.node .empty ⟨2,false,4,2⟩ .empty) ⟨2,false,8,0⟩ (.node .empty ⟨2,false,11,10⟩ .empty))) ⟨2,false,11,12⟩ (.node (.node (.node .empty ⟨2,false,11,15⟩ .empty) ⟨2,false,11,22⟩ (.node .empty ⟨2,false,11,34⟩ .empty)) ⟨2,false,13,19⟩ (.node (.node .empty ⟨2,false,13,37⟩ .empty) ⟨2,false,17,7⟩ (.node .empty ⟨2,false,17,33⟩ .empty))))
def t106_140 : Tree := .node t106_123 ⟨2,false,0,8⟩ t124_140
def t71_140 : Tree := .node t71_105 ⟨1,false,10,35⟩ t106_140
def t0_140 : Tree := .node t0_70 ⟨0,true,13,31⟩ t71_140
def t141_149 : Tree := (.node (.node (.node (.node .empty ⟨2,false,20,4⟩ .empty) ⟨2,false,20,29⟩ .empty) ⟨2,false,20,31⟩ (.node .empty ⟨2,false,20,33⟩ .empty)) ⟨2,false,20,37⟩ (.node (.node .empty ⟨2,false,24,29⟩ .empty) ⟨2,false,24,31⟩ (.node .empty ⟨2,false,24,33⟩ .empty)))
def t150_158 : Tree := (.node (.node (.node (.node .empty ⟨2,true,0,7⟩ .empty) ⟨2,true,0,14⟩ .empty) ⟨2,true,1,5⟩ (.node .empty ⟨2,true,1,12⟩ .empty)) ⟨2,true,1,15⟩ (.node (.node .empty ⟨2,true,2,4⟩ .empty) ⟨2,true,2,11⟩ (.node .empty ⟨2,true,2,14⟩ .empty)))
def t141_158 : Tree := .node t141_149 ⟨2,false,24,37⟩ t150_158
def t159_167 : Tree := (.node (.node (.node (.node .empty ⟨2,true,6,0⟩ .empty) ⟨2,true,14,8⟩ .empty) ⟨2,true,14,36⟩ (.node .empty ⟨2,true,15,7⟩ .empty)) ⟨2,true,15,33⟩ (.node (.node .empty ⟨2,true,15,37⟩ .empty) ⟨3,false,2,1⟩ (.node .empty ⟨3,false,3,0⟩ .empty)))
def t168_176 : Tree := (.node (.node (.node (.node .empty ⟨3,false,9,0⟩ .empty) ⟨3,false,11,8⟩ .empty) ⟨3,false,11,36⟩ (.node .empty ⟨3,false,12,7⟩ .empty)) ⟨3,false,12,33⟩ (.node (.node .empty ⟨3,false,12,37⟩ .empty) ⟨3,false,17,1⟩ (.node .empty ⟨3,false,20,26⟩ .empty)))
def t159_176 : Tree := .node t159_167 ⟨3,false,8,1⟩ t168_176
def t141_176 : Tree := .node t141_158 ⟨2,true,5,1⟩ t159_176
def t177_185 : Tree := (.node (.node (.node (.node .empty ⟨3,false,21,3⟩ .empty) ⟨3,false,21,28⟩ .empty) ⟨3,false,24,42⟩ (.node .empty ⟨3,false,25,28⟩ .empty)) ⟨3,true,0,7⟩ (.node (.node .empty ⟨3,true,0,14⟩ .empty) ⟨3,true,1,2⟩ (.node .empty ⟨3,true,3,4⟩ .empty)))
def t186_194 : Tree := (.node (.node (.node (.node .empty ⟨3,true,3,14⟩ .empty) ⟨3,true,5,1⟩ .empty) ⟨3,true,7,2⟩ (.node .empty ⟨3,true,9,5⟩ .empty)) ⟨3,true,9,32⟩ (.node (.node .empty ⟨3,true,9,36⟩ .empty) ⟨3,true,10,19⟩ (.node .empty ⟨3,true,10,37⟩ .empty)))
def t177_194 : Tree := .node t177_185 ⟨3,true,3,11⟩ t186_194
def t195_211 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,true,12,14⟩ .empty) ⟨3,true,12,21⟩ .empty) ⟨3,true,14,8⟩ (.node .empty ⟨3,true,14,36⟩ .empty)) ⟨3,true,16,2⟩ (.node (.node .empty ⟨3,true,19,27⟩ .empty) ⟨3,true,19,43⟩ (.node .empty ⟨3,true,21,30⟩ .empty))) ⟨3,true,21,32⟩ (.node (.node (.node .empty ⟨3,true,21,36⟩ .empty) ⟨3,true,23,43⟩ (.node .empty ⟨3,true,25,30⟩ .empty)) ⟨3,true,25,32⟩ (.node (.node .empty ⟨3,true,25,36⟩ .empty) ⟨4,false,4,3⟩ (.node .empty ⟨4,false,13,20⟩ .empty))))
def t177_211 : Tree := .node t177_194 ⟨3,true,12,11⟩ t195_211
def t141_211 : Tree := .node t141_176 ⟨3,false,20,42⟩ t177_211
def t212_220 : Tree := (.node (.node (.node (.node .empty ⟨4,true,1,12⟩ .empty) ⟨4,true,1,15⟩ .empty) ⟨4,true,2,1⟩ (.node .empty ⟨4,true,4,10⟩ .empty)) ⟨4,true,4,12⟩ (.node (.node .empty ⟨4,true,4,15⟩ .empty) ⟨4,true,4,22⟩ (.node .empty ⟨4,true,4,34⟩ .empty)))
def t221_229 : Tree := (.node (.node (.node (.node .empty ⟨4,true,8,1⟩ .empty) ⟨4,true,11,8⟩ .empty) ⟨4,true,11,36⟩ (.node .empty ⟨4,true,13,10⟩ .empty)) ⟨4,true,13,12⟩ (.node (.node .empty ⟨4,true,13,15⟩ .empty) ⟨4,true,13,22⟩ (.node .empty ⟨4,true,13,34⟩ .empty)))
def t212_229 : Tree := .node t212_220 ⟨4,true,6,0⟩ t221_229
def t230_246 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,true,15,33⟩ .empty) ⟨4,true,15,37⟩ .empty) ⟨4,true,17,1⟩ (.node .empty ⟨4,true,18,4⟩ .empty)) ⟨4,true,18,31⟩ (.node (.node .empty ⟨4,true,18,33⟩ .empty) ⟨4,true,18,37⟩ (.node .empty ⟨4,true,20,26⟩ .empty))) ⟨4,true,20,42⟩ (.node (.node (.node .empty ⟨4,true,22,29⟩ .empty) ⟨4,true,22,31⟩ (.node .empty ⟨4,true,22,33⟩ .empty)) ⟨4,true,22,37⟩ (.node (.node .empty ⟨4,true,24,42⟩ .empty) ⟨5,true,0,5⟩ (.node .empty ⟨5,true,0,6⟩ .empty))))
def t212_246 : Tree := .node t212_229 ⟨4,true,15,7⟩ t230_246
def t247_255 : Tree := (.node (.node (.node (.node .empty ⟨5,true,0,13⟩ .empty) ⟨5,true,0,15⟩ .empty) ⟨5,true,1,3⟩ (.node .empty ⟨5,true,2,7⟩ .empty)) ⟨5,true,2,33⟩ (.node (.node .empty ⟨5,true,2,37⟩ .empty) ⟨5,true,3,13⟩ (.node .empty ⟨5,true,3,17⟩ .empty)))
def t256_264 : Tree := (.node (.node (.node (.node .empty ⟨5,true,3,35⟩ .empty) ⟨5,true,5,0⟩ .empty) ⟨5,true,7,3⟩ (.node .empty ⟨5,true,9,24⟩ .empty)) ⟨5,true,9,34⟩ (.node (.node .empty ⟨5,true,9,38⟩ .empty) ⟨5,true,10,20⟩ (.node .empty ⟨5,true,11,7⟩ .empty)))
def t247_264 : Tree := .node t247_255 ⟨5,true,3,23⟩ t256_264
def t265_281 : Tree := (.node (.node (.node (.node (.node .empty ⟨5,true,11,37⟩ .empty) ⟨5,true,12,13⟩ .empty) ⟨5,true,12,17⟩ (.node .empty ⟨5,true,12,23⟩ .empty)) ⟨5,true,12,35⟩ (.node (.node .empty ⟨5,true,14,10⟩ .empty) ⟨5,true,14,34⟩ (.node .empty ⟨5,true,16,3⟩ .empty))) ⟨5,true,19,28⟩ (.node (.node (.node .empty ⟨5,true,21,34⟩ .empty) ⟨5,true,21,38⟩ (.node .empty ⟨5,true,21,40⟩ .empty)) ⟨5,true,23,28⟩ (.node (.node .empty ⟨5,true,25,34⟩ .empty) ⟨5,true,25,38⟩ (.node .empty ⟨5,true,25,40⟩ .empty))))
def t247_281 : Tree := .node t247_264 ⟨5,true,11,33⟩ t265_281
def t212_281 : Tree := .node t212_246 ⟨5,true,0,12⟩ t247_281
def t141_281 : Tree := .node t141_211 ⟨4,true,1,5⟩ t212_281
def t0_281 : Tree := .node t0_140 ⟨2,false,17,37⟩ t141_281
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 10, 0, 4, 5, 7, 0, 6, 0, 0, 0, 8, 9, 19, 0, 18, 0, 11, 12, 10, 0, 13, 14, 16, 0, 15, 0, 0, 0, 17, 9, 19, 0, 0, 0, 20, 21, 23, 0, 22, 0, 0, 0, 24, 25, 19, 0, 22],#[0, 1, 3, 2, 0, 0, 4, 26, 24, 5, 6, 7, 9, 0, 10, 8, 20, 19, 0, 0, 17, 11, 0, 12, 13, 14, 16, 0, 0, 15, 13, 14, 0, 0, 18, 0, 0, 0, 0, 0, 21, 0, 0, 22, 23, 11, 18, 0, 25, 0, 0, 0, 28, 27, 0, 0, 29, 42, 40, 30, 0, 31, 38, 32, 0, 33, 34, 36, 35, 11, 18, 0, 20, 37, 34, 36, 39, 0, 0, 0, 41, 0, 0, 0, 28, 43, 0, 0],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(true,3)],[(false,4)],[(true,5)],[(true,4)],[(true,7)],[(false,8),(false,17)],[(true,2),(true,11)],[(true,10)],[(false,11)],[(true,12)],[(false,13)],[(true,14)],[(true,13)],[(true,16)],[(true,9)],[(true,8),(true,17),(true,24)],[(true,19)],[(false,20)],[(true,21),(true,25)],[(true,20)],[(true,23)],[(false,24)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(true,4)],[(false,5)],[(true,5)],[(true,7)],[(false,6)],[(false,7)],[(true,10),(true,22),(true,34)],[(true,11)],[(false,12),(false,15)],[(true,12),(true,15)],[(true,14)],[(false,13)],[(false,10)],[(false,17),(false,23),(false,35)],[(true,8)],[(false,8),(false,36)],[(false,20)],[(true,21)],[(false,22)],[(false,4)],[(false,24)],[(true,3)],[(true,26)],[(false,26),(false,42)],[(false,28)],[(true,29)],[(true,30)],[(true,31)],[(true,32)],[(false,33),(false,37)],[(false,34)],[(true,33),(true,37)],[(true,36)],[(false,31)],[(false,38)],[(false,29)],[(false,40)],[(true,28)],[(true,42)]],
  t0_281⟩
theorem check0_8 : t0_8.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check9_17 : t9_17.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node8 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,2,7⟩ = true := by decide
theorem check0_17 : t0_17.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node8 check0_8 check9_17
theorem check18_26 : t18_26.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check27_35 : t27_35.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node26 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,17,39⟩ = true := by decide
theorem check18_35 : t18_35.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node26 check18_26 check27_35
theorem node17 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,11,7⟩ = true := by decide
theorem check0_35 : t0_35.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node17 check0_17 check18_35
theorem check36_44 : t36_44.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check45_53 : t45_53.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node44 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,3,5⟩ = true := by decide
theorem check36_53 : t36_53.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node44 check36_44 check45_53
theorem check54_70 : t54_70.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node53 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,7,36⟩ = true := by decide
theorem check36_70 : t36_70.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node53 check36_53 check54_70
theorem node35 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,0,14⟩ = true := by decide
theorem check0_70 : t0_70.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node35 check0_35 check36_70
theorem check71_79 : t71_79.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check80_88 : t80_88.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node79 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,17,37⟩ = true := by decide
theorem check71_88 : t71_88.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node79 check71_79 check80_88
theorem check89_105 : t89_105.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node88 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,23,32⟩ = true := by decide
theorem check71_105 : t71_105.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node88 check71_88 check89_105
theorem check106_114 : t106_114.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check115_123 : t115_123.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node114 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,23,34⟩ = true := by decide
theorem check106_123 : t106_123.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node114 check106_114 check115_123
theorem check124_140 : t124_140.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node123 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,0,8⟩ = true := by decide
theorem check106_140 : t106_140.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node123 check106_123 check124_140
theorem node105 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,10,35⟩ = true := by decide
theorem check71_140 : t71_140.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node105 check71_105 check106_140
theorem node70 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,13,31⟩ = true := by decide
theorem check0_140 : t0_140.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node70 check0_70 check71_140
theorem check141_149 : t141_149.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check150_158 : t150_158.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node149 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,24,37⟩ = true := by decide
theorem check141_158 : t141_158.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node149 check141_149 check150_158
theorem check159_167 : t159_167.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check168_176 : t168_176.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node167 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,8,1⟩ = true := by decide
theorem check159_176 : t159_176.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node167 check159_167 check168_176
theorem node158 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,5,1⟩ = true := by decide
theorem check141_176 : t141_176.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node158 check141_158 check159_176
theorem check177_185 : t177_185.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check186_194 : t186_194.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node185 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,3,11⟩ = true := by decide
theorem check177_194 : t177_194.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node185 check177_185 check186_194
theorem check195_211 : t195_211.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node194 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,12,11⟩ = true := by decide
theorem check177_211 : t177_211.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node194 check177_194 check195_211
theorem node176 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,20,42⟩ = true := by decide
theorem check141_211 : t141_211.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node176 check141_176 check177_211
theorem check212_220 : t212_220.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check221_229 : t221_229.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node220 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,6,0⟩ = true := by decide
theorem check212_229 : t212_229.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node220 check212_220 check221_229
theorem check230_246 : t230_246.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node229 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,15,7⟩ = true := by decide
theorem check212_246 : t212_246.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node229 check212_229 check230_246
theorem check247_255 : t247_255.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check256_264 : t256_264.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node255 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,3,23⟩ = true := by decide
theorem check247_264 : t247_264.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node255 check247_255 check256_264
theorem check265_281 : t265_281.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node264 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,11,33⟩ = true := by decide
theorem check247_281 : t247_281.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node264 check247_264 check265_281
theorem node246 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,0,12⟩ = true := by decide
theorem check212_281 : t212_281.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node246 check212_246 check247_281
theorem node211 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,1,5⟩ = true := by decide
theorem check141_281 : t141_281.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node211 check141_211 check212_281
theorem node140 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,17,37⟩ = true := by decide
theorem check0_281 : t0_281.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node140 check0_140 check141_281
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_281
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M028
