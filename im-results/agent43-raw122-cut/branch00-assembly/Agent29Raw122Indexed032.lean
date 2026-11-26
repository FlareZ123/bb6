import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M032
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_9 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,13⟩ .empty) ⟨0,false,3,13⟩ (.node .empty ⟨0,false,4,7⟩ .empty)) ⟨0,false,6,7⟩ (.node (.node (.node .empty ⟨0,false,7,4⟩ .empty) ⟨0,false,7,16⟩ .empty) ⟨0,false,8,13⟩ (.node .empty ⟨0,false,10,7⟩ .empty)))
def t10_18 : Tree := (.node (.node (.node (.node .empty ⟨0,false,11,16⟩ .empty) ⟨0,false,12,13⟩ .empty) ⟨0,false,13,13⟩ (.node .empty ⟨0,false,21,4⟩ .empty)) ⟨0,false,21,16⟩ (.node (.node .empty ⟨0,false,22,13⟩ .empty) ⟨0,false,23,13⟩ (.node .empty ⟨0,false,24,7⟩ .empty)))
def t0_18 : Tree := .node t0_9 ⟨0,false,11,4⟩ t10_18
def t19_27 : Tree := (.node (.node (.node (.node .empty ⟨0,false,26,16⟩ .empty) ⟨0,false,28,13⟩ .empty) ⟨0,false,29,7⟩ (.node .empty ⟨0,false,31,13⟩ .empty)) ⟨0,true,0,4⟩ (.node (.node .empty ⟨0,true,0,16⟩ .empty) ⟨0,true,3,4⟩ (.node .empty ⟨0,true,3,16⟩ .empty)))
def t28_36 : Tree := (.node (.node (.node (.node .empty ⟨0,true,6,10⟩ .empty) ⟨0,true,8,4⟩ .empty) ⟨0,true,8,16⟩ (.node .empty ⟨0,true,10,10⟩ .empty)) ⟨0,true,12,4⟩ (.node (.node .empty ⟨0,true,12,16⟩ .empty) ⟨0,true,13,16⟩ (.node .empty ⟨0,true,22,4⟩ .empty)))
def t19_36 : Tree := .node t19_27 ⟨0,true,4,10⟩ t28_36
def t0_36 : Tree := .node t0_18 ⟨0,false,26,4⟩ t19_36
def t37_45 : Tree := (.node (.node (.node (.node .empty ⟨0,true,23,16⟩ .empty) ⟨0,true,24,10⟩ .empty) ⟨0,true,28,4⟩ (.node .empty ⟨0,true,28,16⟩ .empty)) ⟨0,true,29,10⟩ (.node (.node .empty ⟨0,true,31,4⟩ .empty) ⟨0,true,31,16⟩ (.node .empty ⟨1,false,0,6⟩ .empty)))
def t46_54 : Tree := (.node (.node (.node (.node .empty ⟨1,false,1,0⟩ .empty) ⟨1,false,1,10⟩ .empty) ⟨1,false,1,18⟩ (.node .empty ⟨1,false,2,18⟩ .empty)) ⟨1,false,5,3⟩ (.node (.node .empty ⟨1,false,5,4⟩ .empty) ⟨1,false,5,15⟩ (.node .empty ⟨1,false,5,16⟩ .empty)))
def t37_54 : Tree := .node t37_45 ⟨1,false,0,18⟩ t46_54
def t55_63 : Tree := (.node (.node (.node (.node .empty ⟨1,false,7,18⟩ .empty) ⟨1,false,9,0⟩ .empty) ⟨1,false,9,10⟩ (.node .empty ⟨1,false,9,15⟩ .empty)) ⟨1,false,9,18⟩ (.node (.node .empty ⟨1,false,11,18⟩ .empty) ⟨1,false,14,3⟩ (.node .empty ⟨1,false,14,4⟩ .empty)))
def t64_72 : Tree := (.node (.node (.node (.node .empty ⟨1,false,14,16⟩ .empty) ⟨1,false,14,18⟩ .empty) ⟨1,false,16,10⟩ (.node .empty ⟨1,false,19,0⟩ .empty)) ⟨1,false,19,10⟩ (.node (.node .empty ⟨1,false,19,15⟩ .empty) ⟨1,false,19,18⟩ (.node .empty ⟨1,false,20,3⟩ .empty)))
def t55_72 : Tree := .node t55_63 ⟨1,false,14,15⟩ t64_72
def t37_72 : Tree := .node t37_54 ⟨1,false,5,18⟩ t55_72
def t0_72 : Tree := .node t0_36 ⟨0,true,22,16⟩ t37_72
def t73_81 : Tree := (.node (.node (.node (.node .empty ⟨1,false,20,18⟩ .empty) ⟨1,false,21,18⟩ .empty) ⟨1,false,25,4⟩ (.node .empty ⟨1,false,25,15⟩ .empty)) ⟨1,false,25,16⟩ (.node (.node .empty ⟨1,false,25,18⟩ .empty) ⟨1,false,26,18⟩ (.node .empty ⟨1,false,27,18⟩ .empty)))
def t82_90 : Tree := (.node (.node (.node (.node .empty ⟨1,true,0,12⟩ .empty) ⟨1,true,1,6⟩ .empty) ⟨1,true,1,18⟩ (.node .empty ⟨1,true,2,12⟩ .empty)) ⟨1,true,3,12⟩ (.node (.node .empty ⟨1,true,4,12⟩ .empty) ⟨1,true,5,6⟩ (.node .empty ⟨1,true,5,18⟩ .empty)))
def t73_90 : Tree := .node t73_81 ⟨1,false,30,18⟩ t82_90
def t91_99 : Tree := (.node (.node (.node (.node .empty ⟨1,true,7,12⟩ .empty) ⟨1,true,8,12⟩ .empty) ⟨1,true,9,6⟩ (.node .empty ⟨1,true,9,18⟩ .empty)) ⟨1,true,10,12⟩ (.node (.node .empty ⟨1,true,11,12⟩ .empty) ⟨1,true,12,12⟩ (.node .empty ⟨1,true,14,6⟩ .empty)))
def t100_108 : Tree := (.node (.node (.node (.node .empty ⟨1,true,19,6⟩ .empty) ⟨1,true,19,18⟩ .empty) ⟨1,true,20,6⟩ (.node .empty ⟨1,true,20,18⟩ .empty)) ⟨1,true,21,12⟩ (.node (.node .empty ⟨1,true,22,12⟩ .empty) ⟨1,true,24,12⟩ (.node .empty ⟨1,true,25,6⟩ .empty)))
def t91_108 : Tree := .node t91_99 ⟨1,true,14,18⟩ t100_108
def t73_108 : Tree := .node t73_90 ⟨1,true,6,12⟩ t91_108
def t109_117 : Tree := (.node (.node (.node (.node .empty ⟨1,true,26,12⟩ .empty) ⟨1,true,27,6⟩ .empty) ⟨1,true,27,18⟩ (.node .empty ⟨1,true,28,12⟩ .empty)) ⟨1,true,29,12⟩ (.node (.node .empty ⟨1,true,30,12⟩ .empty) ⟨1,true,31,12⟩ (.node .empty ⟨2,false,1,5⟩ .empty)))
def t118_126 : Tree := (.node (.node (.node (.node .empty ⟨2,false,2,0⟩ .empty) ⟨2,false,2,9⟩ .empty) ⟨2,false,2,17⟩ (.node .empty ⟨2,false,7,1⟩ .empty)) ⟨2,false,7,3⟩ (.node (.node .empty ⟨2,false,7,8⟩ .empty) ⟨2,false,7,15⟩ (.node .empty ⟨2,false,7,17⟩ .empty)))
def t109_126 : Tree := .node t109_117 ⟨2,false,1,17⟩ t118_126
def t127_135 : Tree := (.node (.node (.node (.node .empty ⟨2,false,11,8⟩ .empty) ⟨2,false,11,9⟩ .empty) ⟨2,false,11,17⟩ (.node .empty ⟨2,false,17,9⟩ .empty)) ⟨2,false,20,17⟩ (.node (.node .empty ⟨2,false,21,1⟩ .empty) ⟨2,false,21,8⟩ (.node .empty ⟨2,false,21,17⟩ .empty)))
def t136_144 : Tree := (.node (.node (.node (.node .empty ⟨2,false,26,8⟩ .empty) ⟨2,false,26,15⟩ .empty) ⟨2,false,26,17⟩ (.node .empty ⟨2,false,27,17⟩ .empty)) ⟨2,false,30,17⟩ (.node (.node .empty ⟨3,false,2,1⟩ .empty) ⟨3,false,2,8⟩ (.node .empty ⟨3,false,3,0⟩ .empty)))
def t127_144 : Tree := .node t127_135 ⟨2,false,26,3⟩ t136_144
def t109_144 : Tree := .node t109_126 ⟨2,false,11,0⟩ t127_144
def t73_144 : Tree := .node t73_108 ⟨1,true,25,18⟩ t109_144
def t0_144 : Tree := .node t0_72 ⟨1,false,20,15⟩ t73_144
def t145_153 : Tree := (.node (.node (.node (.node .empty ⟨3,false,3,14⟩ .empty) ⟨3,false,7,2⟩ .empty) ⟨3,false,7,14⟩ (.node .empty ⟨3,false,8,1⟩ .empty)) ⟨3,false,8,8⟩ (.node (.node .empty ⟨3,false,11,1⟩ .empty) ⟨3,false,11,8⟩ (.node .empty ⟨3,false,12,0⟩ .empty)))
def t154_162 : Tree := (.node (.node (.node (.node .empty ⟨3,false,12,14⟩ .empty) ⟨3,false,17,8⟩ .empty) ⟨3,false,18,2⟩ (.node .empty ⟨3,false,18,14⟩ .empty)) ⟨3,false,26,2⟩ (.node (.node .empty ⟨3,false,26,14⟩ .empty) ⟨3,false,28,1⟩ (.node .empty ⟨3,false,28,8⟩ .empty)))
def t145_162 : Tree := .node t145_153 ⟨3,false,12,2⟩ t154_162
def t163_171 : Tree := (.node (.node (.node (.node .empty ⟨3,true,1,14⟩ .empty) ⟨3,true,3,16⟩ .empty) ⟨3,true,4,4⟩ (.node .empty ⟨3,true,4,16⟩ .empty)) ⟨3,true,5,8⟩ (.node (.node .empty ⟨3,true,8,0⟩ .empty) ⟨3,true,8,2⟩ (.node .empty ⟨3,true,8,14⟩ .empty)))
def t172_180 : Tree := (.node (.node (.node (.node .empty ⟨3,true,9,2⟩ .empty) ⟨3,true,9,14⟩ .empty) ⟨3,true,12,2⟩ (.node .empty ⟨3,true,12,14⟩ .empty)) ⟨3,true,12,16⟩ (.node (.node .empty ⟨3,true,14,8⟩ .empty) ⟨3,true,16,14⟩ (.node .empty ⟨3,true,19,2⟩ .empty)))
def t163_180 : Tree := .node t163_171 ⟨3,true,8,16⟩ t172_180
def t145_180 : Tree := .node t145_162 ⟨3,true,1,2⟩ t163_180
def t181_189 : Tree := (.node (.node (.node (.node .empty ⟨3,true,22,0⟩ .empty) ⟨3,true,22,2⟩ .empty) ⟨3,true,22,14⟩ (.node .empty ⟨3,true,22,16⟩ .empty)) ⟨3,true,24,16⟩ (.node (.node .empty ⟨3,true,25,8⟩ .empty) ⟨3,true,28,2⟩ (.node .empty ⟨3,true,28,14⟩ .empty)))
def t190_198 : Tree := (.node (.node (.node (.node .empty ⟨3,true,31,16⟩ .empty) ⟨4,false,0,11⟩ .empty) ⟨4,false,3,11⟩ (.node .empty ⟨4,false,4,5⟩ .empty)) ⟨4,false,4,17⟩ (.node (.node .empty ⟨4,false,5,3⟩ .empty) ⟨4,false,5,15⟩ (.node .empty ⟨4,false,6,5⟩ .empty)))
def t181_198 : Tree := .node t181_189 ⟨3,true,28,16⟩ t190_198
def t199_207 : Tree := (.node (.node (.node (.node .empty ⟨4,false,8,11⟩ .empty) ⟨4,false,9,0⟩ .empty) ⟨4,false,9,15⟩ (.node .empty ⟨4,false,10,5⟩ .empty)) ⟨4,false,10,17⟩ (.node (.node .empty ⟨4,false,12,11⟩ .empty) ⟨4,false,13,11⟩ (.node .empty ⟨4,false,19,15⟩ .empty)))
def t208_216 : Tree := (.node (.node (.node (.node .empty ⟨4,false,23,11⟩ .empty) ⟨4,false,24,5⟩ .empty) ⟨4,false,24,17⟩ (.node .empty ⟨4,false,25,15⟩ .empty)) ⟨4,false,28,11⟩ (.node (.node .empty ⟨4,false,29,5⟩ .empty) ⟨4,false,29,17⟩ (.node .empty ⟨4,false,31,11⟩ .empty)))
def t199_216 : Tree := .node t199_207 ⟨4,false,22,11⟩ t208_216
def t181_216 : Tree := .node t181_198 ⟨4,false,6,17⟩ t199_216
def t145_216 : Tree := .node t145_180 ⟨3,true,19,14⟩ t181_216
def t217_225 : Tree := (.node (.node (.node (.node .empty ⟨4,true,2,8⟩ .empty) ⟨4,true,7,2⟩ .empty) ⟨4,true,7,14⟩ (.node .empty ⟨4,true,9,1⟩ .empty)) ⟨4,true,9,8⟩ (.node (.node .empty ⟨4,true,11,1⟩ .empty) ⟨4,true,11,8⟩ (.node .empty ⟨4,true,17,8⟩ .empty)))
def t226_234 : Tree := (.node (.node (.node (.node .empty ⟨4,true,26,14⟩ .empty) ⟨5,false,0,5⟩ .empty) ⟨5,false,0,17⟩ (.node .empty ⟨5,false,1,11⟩ .empty)) ⟨5,false,2,5⟩ (.node (.node .empty ⟨5,false,2,17⟩ .empty) ⟨5,false,3,17⟩ (.node .empty ⟨5,false,4,17⟩ .empty)))
def t217_234 : Tree := .node t217_225 ⟨4,true,26,2⟩ t226_234
def t235_243 : Tree := (.node (.node (.node (.node .empty ⟨5,false,6,1⟩ .empty) ⟨5,false,6,8⟩ .empty) ⟨5,false,6,17⟩ (.node .empty ⟨5,false,7,5⟩ .empty)) ⟨5,false,7,17⟩ (.node (.node .empty ⟨5,false,8,17⟩ .empty) ⟨5,false,9,11⟩ (.node .empty ⟨5,false,10,0⟩ .empty)))
def t244_252 : Tree := (.node (.node (.node (.node .empty ⟨5,false,10,17⟩ .empty) ⟨5,false,11,5⟩ .empty) ⟨5,false,11,17⟩ (.node .empty ⟨5,false,12,17⟩ .empty)) ⟨5,false,14,11⟩ (.node (.node .empty ⟨5,false,19,11⟩ .empty) ⟨5,false,20,11⟩ (.node .empty ⟨5,false,21,5⟩ .empty)))
def t235_252 : Tree := .node t235_243 ⟨5,false,10,8⟩ t244_252
def t217_252 : Tree := .node t217_234 ⟨5,false,5,11⟩ t235_252
def t253_261 : Tree := (.node (.node (.node (.node .empty ⟨5,false,22,17⟩ .empty) ⟨5,false,24,17⟩ .empty) ⟨5,false,25,11⟩ (.node .empty ⟨5,false,26,5⟩ .empty)) ⟨5,false,26,17⟩ (.node (.node .empty ⟨5,false,27,11⟩ .empty) ⟨5,false,28,17⟩ (.node .empty ⟨5,false,29,8⟩ .empty)))
def t262_270 : Tree := (.node (.node (.node (.node .empty ⟨5,false,30,5⟩ .empty) ⟨5,false,30,17⟩ .empty) ⟨5,false,31,17⟩ (.node .empty ⟨5,true,0,10⟩ .empty)) ⟨5,true,1,3⟩ (.node (.node .empty ⟨5,true,1,15⟩ .empty) ⟨5,true,5,9⟩ (.node .empty ⟨5,true,8,3⟩ .empty)))
def t253_270 : Tree := .node t253_261 ⟨5,false,29,17⟩ t262_270
def t271_279 : Tree := (.node (.node (.node (.node .empty ⟨5,true,9,3⟩ .empty) ⟨5,true,9,15⟩ .empty) ⟨5,true,12,3⟩ (.node .empty ⟨5,true,12,15⟩ .empty)) ⟨5,true,13,4⟩ (.node (.node .empty ⟨5,true,13,16⟩ .empty) ⟨5,true,14,9⟩ (.node .empty ⟨5,true,15,10⟩ .empty)))
def t280_288 : Tree := (.node (.node (.node (.node .empty ⟨5,true,19,3⟩ .empty) ⟨5,true,19,15⟩ .empty) ⟨5,true,22,3⟩ (.node .empty ⟨5,true,22,15⟩ .empty)) ⟨5,true,23,10⟩ (.node (.node .empty ⟨5,true,25,9⟩ .empty) ⟨5,true,28,3⟩ (.node .empty ⟨5,true,28,15⟩ .empty)))
def t271_288 : Tree := .node t271_279 ⟨5,true,16,15⟩ t280_288
def t253_288 : Tree := .node t253_270 ⟨5,true,8,15⟩ t271_288
def t217_288 : Tree := .node t217_252 ⟨5,false,21,17⟩ t253_288
def t145_288 : Tree := .node t145_216 ⟨4,true,2,1⟩ t217_288
def t0_288 : Tree := .node t0_144 ⟨3,false,3,2⟩ t145_288
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 27, 23, 19, 13, 5, 6, 7, 13, 14, 8, 20, 23, 9, 10, 11, 13, 14, 12, 20, 23, 9, 15, 16, 6, 7, 0, 0, 0, 17, 18, 0, 0, 0, 10, 11, 24, 21, 22, 20, 23, 9, 15, 16, 13, 25, 29, 26, 28, 20, 24, 30, 23, 9, 13, 14, 31, 27, 23, 19],#[0, 1, 3, 2, 9, 8, 4, 0, 7, 5, 6, 0, 0, 0, 0, 0, 15, 14, 10, 0, 13, 11, 12, 0, 0, 0, 0, 0, 9, 8, 16, 0, 7, 17, 18, 0, 0, 0],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,4)],[(false,5),(false,14)],[(true,5),(true,14)],[(false,7)],[(true,8),(true,12),(true,22),(true,28)],[(false,9),(false,19)],[(true,9),(true,19)],[(false,11)],[(false,4),(false,6),(false,10),(false,24),(false,29)],[(true,6),(true,10),(true,29)],[(false,13),(false,23)],[(true,13),(true,23)],[(true,16)],[(false,17)],[(true,3),(true,31)],[(true,7),(true,11),(true,21),(true,26)],[(true,20)],[(false,21)],[(false,3),(false,8),(false,12),(false,22),(false,28),(false,31)],[(false,20),(false,27)],[(true,24)],[(true,25)],[(true,2),(true,30)],[(false,26)],[(false,25)],[(true,27)],[(false,30)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(true,4)],[(false,5)],[(false,4),(false,16)],[(true,2),(true,14)],[(false,2),(false,14)],[(false,9)],[(true,10)],[(false,11)],[(false,10)],[(true,8)],[(false,8)],[(false,15)],[(true,16)],[(false,17)]],
  t0_288⟩
theorem check0_9 : t0_9.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check10_18 : t10_18.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node9 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,11,4⟩ = true := by decide
theorem check0_18 : t0_18.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node9 check0_9 check10_18
theorem check19_27 : t19_27.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check28_36 : t28_36.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node27 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,4,10⟩ = true := by decide
theorem check19_36 : t19_36.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node27 check19_27 check28_36
theorem node18 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,26,4⟩ = true := by decide
theorem check0_36 : t0_36.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node18 check0_18 check19_36
theorem check37_45 : t37_45.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check46_54 : t46_54.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node45 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,0,18⟩ = true := by decide
theorem check37_54 : t37_54.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node45 check37_45 check46_54
theorem check55_63 : t55_63.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check64_72 : t64_72.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node63 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,14,15⟩ = true := by decide
theorem check55_72 : t55_72.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node63 check55_63 check64_72
theorem node54 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,5,18⟩ = true := by decide
theorem check37_72 : t37_72.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node54 check37_54 check55_72
theorem node36 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,22,16⟩ = true := by decide
theorem check0_72 : t0_72.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node36 check0_36 check37_72
theorem check73_81 : t73_81.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check82_90 : t82_90.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node81 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,30,18⟩ = true := by decide
theorem check73_90 : t73_90.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node81 check73_81 check82_90
theorem check91_99 : t91_99.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check100_108 : t100_108.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node99 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,14,18⟩ = true := by decide
theorem check91_108 : t91_108.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node99 check91_99 check100_108
theorem node90 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,6,12⟩ = true := by decide
theorem check73_108 : t73_108.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node90 check73_90 check91_108
theorem check109_117 : t109_117.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check118_126 : t118_126.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node117 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,1,17⟩ = true := by decide
theorem check109_126 : t109_126.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node117 check109_117 check118_126
theorem check127_135 : t127_135.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check136_144 : t136_144.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node135 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,26,3⟩ = true := by decide
theorem check127_144 : t127_144.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node135 check127_135 check136_144
theorem node126 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,11,0⟩ = true := by decide
theorem check109_144 : t109_144.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node126 check109_126 check127_144
theorem node108 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,25,18⟩ = true := by decide
theorem check73_144 : t73_144.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node108 check73_108 check109_144
theorem node72 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,20,15⟩ = true := by decide
theorem check0_144 : t0_144.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node72 check0_72 check73_144
theorem check145_153 : t145_153.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check154_162 : t154_162.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node153 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,12,2⟩ = true := by decide
theorem check145_162 : t145_162.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node153 check145_153 check154_162
theorem check163_171 : t163_171.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check172_180 : t172_180.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node171 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,8,16⟩ = true := by decide
theorem check163_180 : t163_180.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node171 check163_171 check172_180
theorem node162 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,1,2⟩ = true := by decide
theorem check145_180 : t145_180.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node162 check145_162 check163_180
theorem check181_189 : t181_189.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check190_198 : t190_198.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node189 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,28,16⟩ = true := by decide
theorem check181_198 : t181_198.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node189 check181_189 check190_198
theorem check199_207 : t199_207.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check208_216 : t208_216.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node207 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,22,11⟩ = true := by decide
theorem check199_216 : t199_216.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node207 check199_207 check208_216
theorem node198 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,6,17⟩ = true := by decide
theorem check181_216 : t181_216.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node198 check181_198 check199_216
theorem node180 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,19,14⟩ = true := by decide
theorem check145_216 : t145_216.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node180 check145_180 check181_216
theorem check217_225 : t217_225.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check226_234 : t226_234.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node225 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,26,2⟩ = true := by decide
theorem check217_234 : t217_234.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node225 check217_225 check226_234
theorem check235_243 : t235_243.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check244_252 : t244_252.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node243 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,10,8⟩ = true := by decide
theorem check235_252 : t235_252.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node243 check235_243 check244_252
theorem node234 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,5,11⟩ = true := by decide
theorem check217_252 : t217_252.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node234 check217_234 check235_252
theorem check253_261 : t253_261.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check262_270 : t262_270.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node261 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,29,17⟩ = true := by decide
theorem check253_270 : t253_270.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node261 check253_261 check262_270
theorem check271_279 : t271_279.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check280_288 : t280_288.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node279 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,16,15⟩ = true := by decide
theorem check271_288 : t271_288.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node279 check271_279 check280_288
theorem node270 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,8,15⟩ = true := by decide
theorem check253_288 : t253_288.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node270 check253_270 check271_288
theorem node252 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,21,17⟩ = true := by decide
theorem check217_288 : t217_288.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node252 check217_252 check253_288
theorem node216 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,2,1⟩ = true := by decide
theorem check145_288 : t145_288.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node216 check145_216 check217_288
theorem node144 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,3,2⟩ = true := by decide
theorem check0_288 : t0_288.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node144 check0_144 check145_288
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_288
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M032
