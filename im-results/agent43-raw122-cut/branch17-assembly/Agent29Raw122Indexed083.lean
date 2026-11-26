import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M083
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def t0_9 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,7,8⟩ .empty) ⟨0,false,7,21⟩ (.node .empty ⟨0,false,7,24⟩ .empty)) ⟨0,false,9,7⟩ (.node (.node (.node .empty ⟨0,false,9,10⟩ .empty) ⟨0,false,9,21⟩ .empty) ⟨0,false,9,23⟩ (.node .empty ⟨0,false,9,34⟩ .empty)))
def t10_18 : Tree := (.node (.node (.node (.node .empty ⟨0,false,22,23⟩ .empty) ⟨0,false,22,41⟩ .empty) ⟨0,false,31,0⟩ (.node .empty ⟨0,false,31,3⟩ .empty)) ⟨0,false,31,9⟩ (.node (.node .empty ⟨0,false,31,22⟩ .empty) ⟨1,false,1,0⟩ (.node .empty ⟨1,false,10,3⟩ .empty)))
def t0_18 : Tree := .node t0_9 ⟨0,false,22,10⟩ t10_18
def t19_27 : Tree := (.node (.node (.node (.node .empty ⟨1,false,10,22⟩ .empty) ⟨1,false,10,30⟩ .empty) ⟨1,false,23,9⟩ (.node .empty ⟨1,false,23,22⟩ .empty)) ⟨1,false,23,40⟩ (.node (.node .empty ⟨1,false,32,0⟩ .empty) ⟨1,false,32,1⟩ (.node .empty ⟨1,false,32,8⟩ .empty)))
def t28_36 : Tree := (.node (.node (.node (.node .empty ⟨1,true,8,7⟩ .empty) ⟨1,true,8,10⟩ .empty) ⟨1,true,8,21⟩ (.node .empty ⟨1,true,8,23⟩ .empty)) ⟨1,true,8,34⟩ (.node (.node .empty ⟨1,true,10,10⟩ .empty) ⟨1,true,10,23⟩ (.node .empty ⟨1,true,10,41⟩ .empty)))
def t19_36 : Tree := .node t19_27 ⟨1,false,32,21⟩ t28_36
def t0_36 : Tree := .node t0_18 ⟨1,false,10,9⟩ t19_36
def t37_45 : Tree := (.node (.node (.node (.node .empty ⟨2,false,1,10⟩ .empty) ⟨2,false,1,15⟩ .empty) ⟨2,false,1,26⟩ (.node .empty ⟨2,false,2,0⟩ .empty)) ⟨2,false,8,32⟩ (.node (.node .empty ⟨2,false,11,1⟩ .empty) ⟨2,false,11,8⟩ (.node .empty ⟨2,false,11,21⟩ .empty)))
def t46_54 : Tree := (.node (.node (.node (.node .empty ⟨2,false,14,0⟩ .empty) ⟨2,false,14,1⟩ .empty) ⟨2,false,14,8⟩ (.node .empty ⟨2,false,14,21⟩ .empty)) ⟨2,false,16,19⟩ (.node (.node .empty ⟨2,false,16,32⟩ .empty) ⟨2,false,16,36⟩ (.node .empty ⟨2,false,19,5⟩ .empty)))
def t37_54 : Tree := .node t37_45 ⟨2,false,11,23⟩ t46_54
def t55_63 : Tree := (.node (.node (.node (.node .empty ⟨2,false,19,32⟩ .empty) ⟨2,false,24,8⟩ .empty) ⟨2,false,24,21⟩ (.node .empty ⟨2,false,24,39⟩ .empty)) ⟨2,false,27,1⟩ (.node (.node .empty ⟨2,false,27,8⟩ .empty) ⟨2,false,27,12⟩ (.node .empty ⟨2,false,27,21⟩ .empty)))
def t64_72 : Tree := (.node (.node (.node (.node .empty ⟨2,false,30,0⟩ .empty) ⟨2,false,30,1⟩ .empty) ⟨2,false,30,8⟩ (.node .empty ⟨2,false,30,21⟩ .empty)) ⟨2,false,35,19⟩ (.node (.node .empty ⟨2,false,35,32⟩ .empty) ⟨2,true,6,9⟩ (.node .empty ⟨2,true,6,22⟩ .empty)))
def t55_72 : Tree := .node t55_63 ⟨2,false,27,35⟩ t64_72
def t37_72 : Tree := .node t37_54 ⟨2,false,19,19⟩ t55_72
def t0_72 : Tree := .node t0_36 ⟨2,false,1,5⟩ t37_72
def t73_81 : Tree := (.node (.node (.node (.node .empty ⟨2,true,7,11⟩ .empty) ⟨2,true,7,17⟩ .empty) ⟨2,true,7,22⟩ (.node .empty ⟨2,true,7,30⟩ .empty)) ⟨2,true,9,11⟩ (.node (.node .empty ⟨2,true,9,30⟩ .empty) ⟨2,true,9,42⟩ (.node .empty ⟨2,true,30,0⟩ .empty)))
def t82_90 : Tree := (.node (.node (.node (.node .empty ⟨2,true,30,10⟩ .empty) ⟨2,true,30,23⟩ .empty) ⟨3,false,1,12⟩ (.node .empty ⟨3,false,1,27⟩ .empty)) ⟨3,false,2,1⟩ (.node (.node .empty ⟨3,false,3,0⟩ .empty) ⟨3,false,4,9⟩ (.node .empty ⟨3,false,4,25⟩ .empty)))
def t73_90 : Tree := .node t73_81 ⟨2,true,30,7⟩ t82_90
def t91_99 : Tree := (.node (.node (.node (.node .empty ⟨3,false,12,22⟩ .empty) ⟨3,false,14,1⟩ .empty) ⟨3,false,15,0⟩ (.node .empty ⟨3,false,30,1⟩ .empty)) ⟨3,false,31,0⟩ (.node (.node .empty ⟨3,true,0,13⟩ .empty) ⟨3,true,0,28⟩ (.node .empty ⟨3,true,1,2⟩ .empty)))
def t100_108 : Tree := (.node (.node (.node (.node .empty ⟨3,true,4,14⟩ .empty) ⟨3,true,4,29⟩ .empty) ⟨3,true,10,13⟩ (.node .empty ⟨3,true,12,0⟩ .empty)) ⟨3,true,12,7⟩ (.node (.node .empty ⟨3,true,12,10⟩ .empty) ⟨3,true,12,23⟩ (.node .empty ⟨3,true,13,2⟩ .empty)))
def t91_108 : Tree := .node t91_99 ⟨3,true,4,4⟩ t100_108
def t73_108 : Tree := .node t73_90 ⟨3,false,11,35⟩ t91_108
def t109_117 : Tree := (.node (.node (.node (.node .empty ⟨3,true,15,7⟩ .empty) ⟨3,true,15,10⟩ .empty) ⟨3,true,15,23⟩ (.node .empty ⟨3,true,17,15⟩ .empty)) ⟨3,true,17,18⟩ (.node (.node .empty ⟨3,true,17,31⟩ .empty) ⟨3,true,20,4⟩ (.node .empty ⟨3,true,20,18⟩ .empty)))
def t118_126 : Tree := (.node (.node (.node (.node .empty ⟨3,true,25,7⟩ .empty) ⟨3,true,25,10⟩ .empty) ⟨3,true,25,23⟩ (.node .empty ⟨3,true,25,38⟩ .empty)) ⟨3,true,28,0⟩ (.node (.node .empty ⟨3,true,28,7⟩ .empty) ⟨3,true,28,9⟩ (.node .empty ⟨3,true,28,10⟩ .empty)))
def t109_126 : Tree := .node t109_117 ⟨3,true,20,31⟩ t118_126
def t127_135 : Tree := (.node (.node (.node (.node .empty ⟨3,true,28,23⟩ .empty) ⟨3,true,29,2⟩ .empty) ⟨3,true,31,0⟩ (.node .empty ⟨3,true,31,7⟩ .empty)) ⟨3,true,31,10⟩ (.node (.node .empty ⟨3,true,31,23⟩ .empty) ⟨3,true,32,2⟩ (.node .empty ⟨3,true,33,31⟩ .empty)))
def t136_144 : Tree := (.node (.node (.node (.node .empty ⟨3,true,36,31⟩ .empty) ⟨4,false,0,6⟩ .empty) ⟨4,false,0,11⟩ (.node .empty ⟨4,false,0,16⟩ .empty)) ⟨4,false,5,12⟩ (.node (.node .empty ⟨4,false,5,27⟩ .empty) ⟨4,false,5,35⟩ (.node .empty ⟨4,false,6,20⟩ .empty)))
def t127_144 : Tree := .node t127_135 ⟨3,true,36,18⟩ t136_144
def t109_144 : Tree := .node t109_126 ⟨3,true,28,22⟩ t127_144
def t73_144 : Tree := .node t73_108 ⟨3,true,15,0⟩ t109_144
def t0_144 : Tree := .node t0_72 ⟨2,true,6,25⟩ t73_144
def t145_153 : Tree := (.node (.node (.node (.node .empty ⟨4,false,6,37⟩ .empty) ⟨4,false,7,33⟩ .empty) ⟨4,false,13,0⟩ (.node .empty ⟨4,false,13,3⟩ .empty)) ⟨4,false,13,9⟩ (.node (.node .empty ⟨4,false,13,22⟩ .empty) ⟨4,false,18,6⟩ (.node .empty ⟨4,false,18,20⟩ .empty)))
def t154_162 : Tree := (.node (.node (.node (.node .empty ⟨4,false,21,6⟩ .empty) ⟨4,false,21,20⟩ .empty) ⟨4,false,21,33⟩ (.node .empty ⟨4,false,26,3⟩ .empty)) ⟨4,false,26,9⟩ (.node (.node .empty ⟨4,false,26,14⟩ .empty) ⟨4,false,26,22⟩ (.node .empty ⟨4,false,29,0⟩ .empty)))
def t145_162 : Tree := .node t145_153 ⟨4,false,18,33⟩ t154_162
def t163_171 : Tree := (.node (.node (.node (.node .empty ⟨4,false,29,8⟩ .empty) ⟨4,false,29,9⟩ .empty) ⟨4,false,29,21⟩ (.node .empty ⟨4,false,29,22⟩ .empty)) ⟨4,false,32,0⟩ (.node (.node .empty ⟨4,false,32,3⟩ .empty) ⟨4,false,32,9⟩ (.node .empty ⟨4,false,32,22⟩ .empty)))
def t172_180 : Tree := (.node (.node (.node (.node .empty ⟨4,false,34,33⟩ .empty) ⟨4,false,37,6⟩ .empty) ⟨4,false,37,20⟩ (.node .empty ⟨4,false,37,33⟩ .empty)) ⟨4,true,0,9⟩ (.node (.node .empty ⟨4,true,0,25⟩ .empty) ⟨4,true,1,12⟩ (.node .empty ⟨4,true,1,27⟩ .empty)))
def t163_180 : Tree := .node t163_171 ⟨4,false,34,20⟩ t172_180
def t145_180 : Tree := .node t145_162 ⟨4,false,29,3⟩ t163_180
def t181_189 : Tree := (.node (.node (.node (.node .empty ⟨4,true,2,1⟩ .empty) ⟨4,true,5,3⟩ .empty) ⟨4,true,5,30⟩ (.node .empty ⟨4,true,6,22⟩ .empty)) ⟨4,true,6,40⟩ (.node (.node .empty ⟨4,true,7,22⟩ .empty) ⟨4,true,10,6⟩ (.node .empty ⟨4,true,10,20⟩ .empty)))
def t190_198 : Tree := (.node (.node (.node (.node .empty ⟨4,true,11,12⟩ .empty) ⟨4,true,11,35⟩ .empty) ⟨4,true,13,6⟩ (.node .empty ⟨4,true,13,20⟩ .empty)) ⟨4,true,13,33⟩ (.node (.node .empty ⟨4,true,14,1⟩ .empty) ⟨4,true,18,9⟩ (.node .empty ⟨4,true,18,14⟩ .empty)))
def t181_198 : Tree := .node t181_189 ⟨4,true,10,33⟩ t190_198
def t199_207 : Tree := (.node (.node (.node (.node .empty ⟨4,true,21,3⟩ .empty) ⟨4,true,21,9⟩ .empty) ⟨4,true,21,22⟩ (.node .empty ⟨4,true,23,20⟩ .empty)) ⟨4,true,23,33⟩ (.node (.node .empty ⟨4,true,26,6⟩ .empty) ⟨4,true,26,20⟩ (.node .empty ⟨4,true,26,33⟩ .empty)))
def t208_216 : Tree := (.node (.node (.node (.node .empty ⟨4,true,29,20⟩ .empty) ⟨4,true,29,33⟩ .empty) ⟨4,true,30,1⟩ (.node .empty ⟨4,true,32,6⟩ .empty)) ⟨4,true,32,20⟩ (.node (.node .empty ⟨4,true,32,33⟩ .empty) ⟨4,true,34,22⟩ (.node .empty ⟨4,true,37,9⟩ .empty)))
def t199_216 : Tree := .node t199_207 ⟨4,true,29,6⟩ t208_216
def t181_216 : Tree := .node t181_198 ⟨4,true,18,22⟩ t199_216
def t145_216 : Tree := .node t145_180 ⟨4,true,1,35⟩ t181_216
def t217_225 : Tree := (.node (.node (.node (.node .empty ⟨5,false,0,5⟩ .empty) ⟨5,false,0,10⟩ .empty) ⟨5,false,0,15⟩ (.node .empty ⟨5,false,0,26⟩ .empty)) ⟨5,false,1,8⟩ (.node (.node .empty ⟨5,false,1,24⟩ .empty) ⟨5,false,6,23⟩ (.node .empty ⟨5,false,7,19⟩ .empty)))
def t226_234 : Tree := (.node (.node (.node (.node .empty ⟨5,false,7,36⟩ .empty) ⟨5,false,8,21⟩ .empty) ⟨5,false,9,32⟩ (.node .empty ⟨5,false,11,5⟩ .empty)) ⟨5,false,11,19⟩ (.node (.node .empty ⟨5,false,11,32⟩ .empty) ⟨5,false,14,5⟩ (.node .empty ⟨5,false,14,19⟩ .empty)))
def t217_234 : Tree := .node t217_225 ⟨5,false,7,32⟩ t226_234
def t235_243 : Tree := (.node (.node (.node (.node .empty ⟨5,false,16,21⟩ .empty) ⟨5,false,16,39⟩ .empty) ⟨5,false,19,8⟩ (.node .empty ⟨5,false,19,21⟩ .empty)) ⟨5,false,24,19⟩ (.node (.node .empty ⟨5,false,24,32⟩ .empty) ⟨5,false,27,5⟩ (.node .empty ⟨5,false,27,19⟩ .empty)))
def t244_252 : Tree := (.node (.node (.node (.node .empty ⟨5,false,30,5⟩ .empty) ⟨5,false,30,19⟩ .empty) ⟨5,false,30,32⟩ (.node .empty ⟨5,false,35,21⟩ .empty)) ⟨5,true,0,4⟩ (.node (.node .empty ⟨5,true,0,14⟩ .empty) ⟨5,true,0,29⟩ (.node .empty ⟨5,true,1,3⟩ .empty)))
def t235_252 : Tree := .node t235_243 ⟨5,false,27,32⟩ t244_252
def t217_252 : Tree := .node t217_234 ⟨5,false,14,32⟩ t235_252
def t253_261 : Tree := (.node (.node (.node (.node .empty ⟨5,true,4,21⟩ .empty) ⟨5,true,4,34⟩ .empty) ⟨5,true,5,23⟩ (.node .empty ⟨5,true,5,41⟩ .empty)) ⟨5,true,9,15⟩ (.node (.node .empty ⟨5,true,9,18⟩ .empty) ⟨5,true,9,31⟩ (.node .empty ⟨5,true,10,14⟩ .empty)))
def t262_270 : Tree := (.node (.node (.node (.node .empty ⟨5,true,12,18⟩ .empty) ⟨5,true,12,31⟩ .empty) ⟨5,true,13,3⟩ (.node .empty ⟨5,true,15,4⟩ .empty)) ⟨5,true,15,18⟩ (.node (.node .empty ⟨5,true,15,31⟩ .empty) ⟨5,true,17,10⟩ (.node .empty ⟨5,true,17,23⟩ .empty)))
def t253_270 : Tree := .node t253_261 ⟨5,true,12,4⟩ t262_270
def t271_279 : Tree := (.node (.node (.node (.node .empty ⟨5,true,20,7⟩ .empty) ⟨5,true,20,10⟩ .empty) ⟨5,true,20,23⟩ (.node .empty ⟨5,true,22,31⟩ .empty)) ⟨5,true,25,18⟩ (.node (.node .empty ⟨5,true,25,31⟩ .empty) ⟨5,true,28,4⟩ (.node .empty ⟨5,true,28,18⟩ .empty)))
def t280_288 : Tree := (.node (.node (.node (.node .empty ⟨5,true,29,3⟩ .empty) ⟨5,true,31,4⟩ .empty) ⟨5,true,31,18⟩ (.node .empty ⟨5,true,31,31⟩ .empty)) ⟨5,true,32,3⟩ (.node (.node .empty ⟨5,true,33,23⟩ .empty) ⟨5,true,36,10⟩ (.node .empty ⟨5,true,36,23⟩ .empty)))
def t271_288 : Tree := .node t271_279 ⟨5,true,28,31⟩ t280_288
def t253_288 : Tree := .node t253_270 ⟨5,true,17,38⟩ t271_288
def t217_288 : Tree := .node t217_252 ⟨5,true,4,7⟩ t253_288
def t145_288 : Tree := .node t145_216 ⟨4,true,37,22⟩ t217_288
def t0_288 : Tree := .node t0_144 ⟨4,false,6,33⟩ t145_288
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 0, 0, 0, 0, 5, 0, 6, 7, 16, 9, 8, 33, 0, 22, 10, 0, 11, 12, 0, 0, 13, 0, 14, 15, 0, 0, 13, 17, 0, 0, 18, 0, 19, 20, 0, 0, 21, 0, 19, 0, 23, 0, 24, 25, 0, 0, 26, 0, 27, 28, 0, 0, 29, 0, 30, 31, 0, 0, 32, 0, 30, 0, 34, 0, 35, 36, 0, 0, 37, 0, 19],#[0, 1, 3, 2, 0, 0, 7, 4, 0, 5, 6, 0, 18, 0, 17, 8, 9, 0, 10, 12, 11, 21, 0, 0, 14, 13, 0, 0, 38, 15, 16, 36, 0, 0, 0, 0, 0, 19, 20, 0, 31, 0, 22, 24, 23, 35, 30, 21, 25, 0, 26, 27, 16, 0, 29, 28, 0, 0, 0, 26, 34, 0, 0, 32, 33, 0, 31, 0, 17, 24, 14, 13, 37, 0, 0, 0, 0, 39, 40, 0, 41, 0, 42, 34, 0, 0],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,4)],[(true,5)],[(false,6)],[(true,7)],[(false,7)],[(true,9)],[(true,10)],[(false,11)],[(true,12),(true,15)],[(true,13)],[(false,14)],[(true,6)],[(false,16)],[(true,17)],[(true,18),(true,21),(true,37)],[(false,19)],[(true,20)],[(false,9)],[(true,22)],[(true,23)],[(false,24)],[(true,25)],[(true,26)],[(false,27)],[(true,28)],[(true,29),(true,32)],[(false,30)],[(true,31)],[(false,8)],[(true,33)],[(true,34)],[(false,35)],[(true,36)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3)],[(true,4)],[(false,5)],[(false,3)],[(true,7)],[(false,8)],[(false,9)],[(false,10)],[(true,9)],[(true,12),(true,35)],[(false,12),(false,35)],[(true,14)],[(false,15),(false,26)],[(false,7),(false,34)],[(false,6)],[(true,18)],[(false,19)],[(true,10),(true,23)],[(false,21)],[(false,22)],[(true,21),(true,34)],[(false,24)],[(false,25),(true,29)],[(true,25)],[(true,27)],[(false,27)],[(false,23)],[(false,20),(false,33)],[(true,31)],[(false,32)],[(false,30),(true,41)],[(true,22)],[(true,15)],[(false,36)],[(false,14)],[(true,38)],[(false,39)],[(false,40)],[(false,41)]],
  t0_288⟩
theorem check0_9 : t0_9.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check10_18 : t10_18.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node9 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,22,10⟩ = true := by decide
theorem check0_18 : t0_18.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node9 check0_9 check10_18
theorem check19_27 : t19_27.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check28_36 : t28_36.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node27 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,32,21⟩ = true := by decide
theorem check19_36 : t19_36.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node27 check19_27 check28_36
theorem node18 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,10,9⟩ = true := by decide
theorem check0_36 : t0_36.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node18 check0_18 check19_36
theorem check37_45 : t37_45.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check46_54 : t46_54.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node45 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,11,23⟩ = true := by decide
theorem check37_54 : t37_54.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node45 check37_45 check46_54
theorem check55_63 : t55_63.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check64_72 : t64_72.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node63 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,27,35⟩ = true := by decide
theorem check55_72 : t55_72.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node63 check55_63 check64_72
theorem node54 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,19,19⟩ = true := by decide
theorem check37_72 : t37_72.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node54 check37_54 check55_72
theorem node36 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,1,5⟩ = true := by decide
theorem check0_72 : t0_72.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node36 check0_36 check37_72
theorem check73_81 : t73_81.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check82_90 : t82_90.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node81 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,30,7⟩ = true := by decide
theorem check73_90 : t73_90.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node81 check73_81 check82_90
theorem check91_99 : t91_99.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check100_108 : t100_108.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node99 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,4,4⟩ = true := by decide
theorem check91_108 : t91_108.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node99 check91_99 check100_108
theorem node90 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,11,35⟩ = true := by decide
theorem check73_108 : t73_108.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node90 check73_90 check91_108
theorem check109_117 : t109_117.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check118_126 : t118_126.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node117 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,20,31⟩ = true := by decide
theorem check109_126 : t109_126.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node117 check109_117 check118_126
theorem check127_135 : t127_135.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check136_144 : t136_144.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node135 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,36,18⟩ = true := by decide
theorem check127_144 : t127_144.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node135 check127_135 check136_144
theorem node126 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,28,22⟩ = true := by decide
theorem check109_144 : t109_144.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node126 check109_126 check127_144
theorem node108 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,15,0⟩ = true := by decide
theorem check73_144 : t73_144.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node108 check73_108 check109_144
theorem node72 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,6,25⟩ = true := by decide
theorem check0_144 : t0_144.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node72 check0_72 check73_144
theorem check145_153 : t145_153.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check154_162 : t154_162.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node153 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,18,33⟩ = true := by decide
theorem check145_162 : t145_162.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node153 check145_153 check154_162
theorem check163_171 : t163_171.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check172_180 : t172_180.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node171 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,34,20⟩ = true := by decide
theorem check163_180 : t163_180.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node171 check163_171 check172_180
theorem node162 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,29,3⟩ = true := by decide
theorem check145_180 : t145_180.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node162 check145_162 check163_180
theorem check181_189 : t181_189.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check190_198 : t190_198.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node189 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,10,33⟩ = true := by decide
theorem check181_198 : t181_198.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node189 check181_189 check190_198
theorem check199_207 : t199_207.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check208_216 : t208_216.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node207 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,29,6⟩ = true := by decide
theorem check199_216 : t199_216.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node207 check199_207 check208_216
theorem node198 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,18,22⟩ = true := by decide
theorem check181_216 : t181_216.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node198 check181_198 check199_216
theorem node180 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,1,35⟩ = true := by decide
theorem check145_216 : t145_216.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node180 check145_180 check181_216
theorem check217_225 : t217_225.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check226_234 : t226_234.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node225 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,7,32⟩ = true := by decide
theorem check217_234 : t217_234.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node225 check217_225 check226_234
theorem check235_243 : t235_243.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check244_252 : t244_252.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node243 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,27,32⟩ = true := by decide
theorem check235_252 : t235_252.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node243 check235_243 check244_252
theorem node234 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,14,32⟩ = true := by decide
theorem check217_252 : t217_252.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node234 check217_234 check235_252
theorem check253_261 : t253_261.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check262_270 : t262_270.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node261 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,12,4⟩ = true := by decide
theorem check253_270 : t253_270.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node261 check253_261 check262_270
theorem check271_279 : t271_279.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check280_288 : t280_288.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node279 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,28,31⟩ = true := by decide
theorem check271_288 : t271_288.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node279 check271_279 check280_288
theorem node270 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,17,38⟩ = true := by decide
theorem check253_288 : t253_288.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node270 check253_270 check271_288
theorem node252 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,4,7⟩ = true := by decide
theorem check217_288 : t217_288.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node252 check217_252 check253_288
theorem node216 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,37,22⟩ = true := by decide
theorem check145_288 : t145_288.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node216 check145_216 check217_288
theorem node144 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,6,33⟩ = true := by decide
theorem check0_288 : t0_288.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node144 check0_144 check145_288
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_288
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M083
