import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M079
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def t0_9 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,6⟩ .empty) ⟨0,false,3,17⟩ (.node .empty ⟨0,false,16,26⟩ .empty)) ⟨0,false,16,43⟩ (.node (.node (.node .empty ⟨0,false,21,43⟩ .empty) ⟨0,false,21,46⟩ .empty) ⟨0,false,26,43⟩ (.node .empty ⟨0,false,26,46⟩ .empty)))
def t10_18 : Tree := (.node (.node (.node (.node .empty ⟨0,true,1,42⟩ .empty) ⟨0,true,5,7⟩ .empty) ⟨0,true,14,32⟩ (.node .empty ⟨0,true,14,54⟩ .empty)) ⟨0,true,14,63⟩ (.node (.node .empty ⟨1,false,1,0⟩ .empty) ⟨1,false,1,5⟩ (.node .empty ⟨1,false,1,14⟩ .empty)))
def t0_18 : Tree := .node t0_9 ⟨0,true,1,24⟩ t10_18
def t19_27 : Tree := (.node (.node (.node (.node .empty ⟨1,false,10,16⟩ .empty) ⟨1,false,10,34⟩ .empty) ⟨1,false,14,23⟩ (.node .empty ⟨1,false,14,41⟩ .empty)) ⟨1,false,14,56⟩ (.node (.node .empty ⟨1,false,14,65⟩ .empty) ⟨1,false,20,9⟩ (.node .empty ⟨1,false,20,35⟩ .empty)))
def t28_36 : Tree := (.node (.node (.node (.node .empty ⟨1,false,20,55⟩ .empty) ⟨1,false,20,58⟩ .empty) ⟨1,false,20,64⟩ (.node .empty ⟨1,false,25,35⟩ .empty)) ⟨1,false,25,40⟩ (.node (.node .empty ⟨1,false,25,45⟩ .empty) ⟨1,false,25,55⟩ (.node .empty ⟨1,false,25,58⟩ .empty)))
def t19_36 : Tree := .node t19_27 ⟨1,false,20,40⟩ t28_36
def t0_36 : Tree := .node t0_18 ⟨1,false,7,0⟩ t19_36
def t37_45 : Tree := (.node (.node (.node (.node .empty ⟨2,false,2,0⟩ .empty) ⟨2,false,3,33⟩ .empty) ⟨2,false,4,1⟩ (.node .empty ⟨2,false,4,10⟩ .empty)) ⟨2,false,4,41⟩ (.node (.node .empty ⟨2,false,4,56⟩ .empty) ⟨2,false,4,65⟩ (.node .empty ⟨2,false,8,0⟩ .empty)))
def t46_54 : Tree := (.node (.node (.node (.node .empty ⟨2,false,12,32⟩ .empty) ⟨2,false,12,39⟩ .empty) ⟨2,false,12,54⟩ (.node .empty ⟨2,false,12,63⟩ .empty)) ⟨2,false,17,19⟩ (.node (.node .empty ⟨2,false,17,37⟩ .empty) ⟨2,false,17,53⟩ (.node .empty ⟨2,false,17,60⟩ .empty)))
def t37_54 : Tree := .node t37_45 ⟨2,false,12,8⟩ t46_54
def t55_63 : Tree := (.node (.node (.node (.node .empty ⟨2,false,22,7⟩ .empty) ⟨2,false,22,31⟩ .empty) ⟨2,false,22,37⟩ (.node .empty ⟨2,false,22,51⟩ .empty)) ⟨2,false,22,53⟩ (.node (.node .empty ⟨2,false,22,60⟩ .empty) ⟨2,false,22,61⟩ (.node .empty ⟨2,false,27,29⟩ .empty)))
def t64_72 : Tree := (.node (.node (.node (.node .empty ⟨2,false,27,37⟩ .empty) ⟨2,false,27,49⟩ .empty) ⟨2,false,27,51⟩ (.node .empty ⟨2,false,27,53⟩ .empty)) ⟨2,false,27,60⟩ (.node (.node .empty ⟨2,false,27,61⟩ .empty) ⟨2,true,2,4⟩ (.node .empty ⟨2,true,2,13⟩ .empty)))
def t55_72 : Tree := .node t55_63 ⟨2,false,27,31⟩ t64_72
def t37_72 : Tree := .node t37_54 ⟨2,false,17,61⟩ t55_72
def t0_72 : Tree := .node t0_36 ⟨1,false,25,64⟩ t37_72
def t73_81 : Tree := (.node (.node (.node (.node .empty ⟨2,true,3,12⟩ .empty) ⟨2,true,3,42⟩ .empty) ⟨2,true,11,15⟩ (.node .empty ⟨2,true,11,33⟩ .empty)) ⟨2,true,15,22⟩ (.node (.node .empty ⟨2,true,15,40⟩ .empty) ⟨2,true,15,55⟩ (.node .empty ⟨2,true,15,64⟩ .empty)))
def t82_90 : Tree := (.node (.node (.node (.node .empty ⟨2,true,16,39⟩ .empty) ⟨2,true,16,54⟩ .empty) ⟨2,true,16,63⟩ (.node .empty ⟨2,true,21,8⟩ .empty)) ⟨2,true,21,32⟩ (.node (.node .empty ⟨2,true,21,39⟩ .empty) ⟨2,true,21,54⟩ (.node .empty ⟨2,true,21,57⟩ .empty)))
def t73_90 : Tree := .node t73_81 ⟨2,true,16,21⟩ t82_90
def t91_99 : Tree := (.node (.node (.node (.node .empty ⟨2,true,26,32⟩ .empty) ⟨2,true,26,39⟩ .empty) ⟨2,true,26,44⟩ (.node .empty ⟨2,true,26,54⟩ .empty)) ⟨2,true,26,57⟩ (.node (.node .empty ⟨2,true,26,63⟩ .empty) ⟨3,false,1,33⟩ (.node .empty ⟨3,false,2,1⟩ .empty)))
def t100_108 : Tree := (.node (.node (.node (.node .empty ⟨3,false,2,56⟩ .empty) ⟨3,false,2,65⟩ .empty) ⟨3,false,3,0⟩ (.node .empty ⟨3,false,3,9⟩ .empty)) ⟨3,false,3,35⟩ (.node (.node .empty ⟨3,false,3,55⟩ .empty) ⟨3,false,3,64⟩ (.node .empty ⟨3,false,4,8⟩ .empty)))
def t91_108 : Tree := .node t91_99 ⟨3,false,2,10⟩ t100_108
def t73_108 : Tree := .node t73_90 ⟨2,true,21,63⟩ t91_108
def t109_117 : Tree := (.node (.node (.node (.node .empty ⟨3,false,4,54⟩ .empty) ⟨3,false,4,63⟩ .empty) ⟨3,false,8,1⟩ (.node .empty ⟨3,false,9,0⟩ .empty)) ⟨3,false,11,19⟩ (.node (.node .empty ⟨3,false,11,37⟩ .empty) ⟨3,false,11,60⟩ (.node .empty ⟨3,false,11,61⟩ .empty)))
def t118_126 : Tree := (.node (.node (.node (.node .empty ⟨3,false,12,36⟩ .empty) ⟨3,false,12,38⟩ .empty) ⟨3,false,12,59⟩ (.node .empty ⟨3,false,12,62⟩ .empty)) ⟨3,false,13,7⟩ (.node (.node .empty ⟨3,false,13,31⟩ .empty) ⟨3,false,13,37⟩ (.node .empty ⟨3,false,13,53⟩ .empty)))
def t109_126 : Tree := .node t109_117 ⟨3,false,12,18⟩ t118_126
def t127_135 : Tree := (.node (.node (.node (.node .empty ⟨3,false,13,61⟩ .empty) ⟨3,false,21,27⟩ .empty) ⟨3,false,22,5⟩ (.node .empty ⟨3,false,23,4⟩ .empty)) ⟨3,false,26,47⟩ (.node (.node .empty ⟨3,false,27,28⟩ .empty) ⟨3,false,27,48⟩ (.node .empty ⟨3,false,28,27⟩ .empty)))
def t136_144 : Tree := (.node (.node (.node (.node .empty ⟨3,true,0,25⟩ .empty) ⟨3,true,0,34⟩ .empty) ⟨3,true,1,2⟩ (.node .empty ⟨3,true,1,11⟩ .empty)) ⟨3,true,5,0⟩ (.node (.node .empty ⟨3,true,5,9⟩ .empty) ⟨3,true,5,35⟩ (.node .empty ⟨3,true,5,40⟩ .empty)))
def t127_144 : Tree := .node t127_135 ⟨3,false,28,47⟩ t136_144
def t109_144 : Tree := .node t109_126 ⟨3,false,13,60⟩ t127_144
def t73_144 : Tree := .node t73_108 ⟨3,false,4,32⟩ t109_144
def t0_144 : Tree := .node t0_72 ⟨2,true,3,3⟩ t73_144
def t145_153 : Tree := (.node (.node (.node (.node .empty ⟨3,true,5,64⟩ .empty) ⟨3,true,7,2⟩ .empty) ⟨3,true,10,20⟩ (.node .empty ⟨3,true,10,38⟩ .empty)) ⟨3,true,10,62⟩ (.node (.node .empty ⟨3,true,18,18⟩ .empty) ⟨3,true,18,36⟩ (.node .empty ⟨3,true,18,38⟩ .empty)))
def t154_162 : Tree := (.node (.node (.node (.node .empty ⟨3,true,18,59⟩ .empty) ⟨3,true,18,62⟩ .empty) ⟨3,true,20,28⟩ (.node .empty ⟨3,true,23,30⟩ .empty)) ⟨3,true,23,36⟩ (.node (.node .empty ⟨3,true,23,38⟩ .empty) ⟨3,true,23,50⟩ (.node .empty ⟨3,true,23,52⟩ .empty)))
def t145_162 : Tree := .node t145_153 ⟨3,true,18,52⟩ t154_162
def t163_171 : Tree := (.node (.node (.node (.node .empty ⟨3,true,23,62⟩ .empty) ⟨3,true,25,48⟩ .empty) ⟨3,true,28,30⟩ (.node .empty ⟨3,true,28,36⟩ .empty)) ⟨3,true,28,38⟩ (.node (.node .empty ⟨3,true,28,50⟩ .empty) ⟨3,true,28,52⟩ (.node .empty ⟨3,true,28,59⟩ .empty)))
def t172_180 : Tree := (.node (.node (.node (.node .empty ⟨4,false,1,24⟩ .empty) ⟨4,false,1,42⟩ .empty) ⟨4,false,6,0⟩ (.node .empty ⟨4,true,1,33⟩ .empty)) ⟨4,true,2,1⟩ (.node (.node .empty ⟨4,true,2,10⟩ .empty) ⟨4,true,2,56⟩ (.node .empty ⟨4,true,2,65⟩ .empty)))
def t163_180 : Tree := .node t163_171 ⟨3,true,28,62⟩ t172_180
def t145_180 : Tree := .node t145_162 ⟨3,true,23,59⟩ t163_180
def t181_189 : Tree := (.node (.node (.node (.node .empty ⟨4,true,6,32⟩ .empty) ⟨4,true,6,39⟩ .empty) ⟨4,true,6,54⟩ (.node .empty ⟨4,true,6,63⟩ .empty)) ⟨4,true,8,1⟩ (.node (.node .empty ⟨4,true,11,19⟩ .empty) ⟨4,true,11,37⟩ (.node .empty ⟨4,true,11,60⟩ .empty)))
def t190_198 : Tree := (.node (.node (.node (.node .empty ⟨4,true,19,7⟩ .empty) ⟨4,true,19,31⟩ .empty) ⟨4,true,19,37⟩ (.node .empty ⟨4,true,19,51⟩ .empty)) ⟨4,true,19,53⟩ (.node (.node .empty ⟨4,true,19,60⟩ .empty) ⟨4,true,19,61⟩ (.node .empty ⟨4,true,21,27⟩ .empty)))
def t181_198 : Tree := .node t181_189 ⟨4,true,11,61⟩ t190_198
def t199_207 : Tree := (.node (.node (.node (.node .empty ⟨4,true,24,31⟩ .empty) ⟨4,true,24,37⟩ .empty) ⟨4,true,24,49⟩ (.node .empty ⟨4,true,24,51⟩ .empty)) ⟨4,true,24,53⟩ (.node (.node .empty ⟨4,true,24,60⟩ .empty) ⟨4,true,24,61⟩ (.node .empty ⟨4,true,26,47⟩ .empty)))
def t208_216 : Tree := (.node (.node (.node (.node .empty ⟨5,false,0,14⟩ .empty) ⟨5,false,2,23⟩ .empty) ⟨5,false,2,41⟩ (.node .empty ⟨5,false,2,65⟩ .empty)) ⟨5,false,4,16⟩ (.node (.node .empty ⟨5,false,4,34⟩ .empty) ⟨5,false,6,4⟩ (.node .empty ⟨5,false,15,31⟩ .empty)))
def t199_216 : Tree := .node t199_207 ⟨5,false,0,5⟩ t208_216
def t181_216 : Tree := .node t181_198 ⟨4,true,24,29⟩ t199_216
def t145_216 : Tree := .node t145_180 ⟨4,true,6,8⟩ t181_216
def t217_225 : Tree := (.node (.node (.node (.node .empty ⟨5,false,15,60⟩ .empty) ⟨5,false,17,9⟩ .empty) ⟨5,false,17,35⟩ (.node .empty ⟨5,false,17,40⟩ .empty)) ⟨5,false,17,55⟩ (.node (.node .empty ⟨5,false,17,58⟩ .empty) ⟨5,false,17,64⟩ (.node .empty ⟨5,false,22,35⟩ .empty)))
def t226_234 : Tree := (.node (.node (.node (.node .empty ⟨5,false,22,45⟩ .empty) ⟨5,false,22,55⟩ .empty) ⟨5,false,22,58⟩ (.node .empty ⟨5,false,22,64⟩ .empty)) ⟨5,false,27,35⟩ (.node (.node .empty ⟨5,false,27,40⟩ .empty) ⟨5,false,27,45⟩ (.node .empty ⟨5,false,27,55⟩ .empty)))
def t217_234 : Tree := .node t217_225 ⟨5,false,22,40⟩ t226_234
def t235_243 : Tree := (.node (.node (.node (.node .empty ⟨5,false,27,64⟩ .empty) ⟨5,true,0,4⟩ .empty) ⟨5,true,0,13⟩ (.node .empty ⟨5,true,1,3⟩ .empty)) ⟨5,true,1,12⟩ (.node (.node .empty ⟨5,true,1,42⟩ .empty) ⟨5,true,3,22⟩ (.node .empty ⟨5,true,3,40⟩ .empty)))
def t244_252 : Tree := (.node (.node (.node (.node .empty ⟨5,true,5,15⟩ .empty) ⟨5,true,5,33⟩ .empty) ⟨5,true,7,3⟩ (.node .empty ⟨5,true,10,21⟩ .empty)) ⟨5,true,10,39⟩ (.node (.node .empty ⟨5,true,10,63⟩ .empty) ⟨5,true,16,30⟩ (.node .empty ⟨5,true,16,52⟩ .empty)))
def t235_252 : Tree := .node t235_243 ⟨5,true,3,64⟩ t244_252
def t217_252 : Tree := .node t217_234 ⟨5,false,27,58⟩ t235_252
def t253_261 : Tree := (.node (.node (.node (.node .empty ⟨5,true,16,62⟩ .empty) ⟨5,true,18,8⟩ .empty) ⟨5,true,18,32⟩ (.node .empty ⟨5,true,18,39⟩ .empty)) ⟨5,true,18,54⟩ (.node (.node .empty ⟨5,true,18,57⟩ .empty) ⟨5,true,18,63⟩ (.node .empty ⟨5,true,20,29⟩ .empty)))
def t262_270 : Tree := (.node (.node (.node (.node .empty ⟨5,true,20,53⟩ .empty) ⟨5,true,20,60⟩ .empty) ⟨5,true,21,50⟩ (.node .empty ⟨5,true,21,52⟩ .empty)) ⟨5,true,21,59⟩ (.node (.node .empty ⟨5,true,21,62⟩ .empty) ⟨5,true,23,32⟩ (.node .empty ⟨5,true,23,39⟩ .empty)))
def t253_270 : Tree := .node t253_261 ⟨5,true,20,51⟩ t262_270
def t271_279 : Tree := (.node (.node (.node (.node .empty ⟨5,true,23,54⟩ .empty) ⟨5,true,23,57⟩ .empty) ⟨5,true,23,63⟩ (.node .empty ⟨5,true,25,49⟩ .empty)) ⟨5,true,25,51⟩ (.node (.node .empty ⟨5,true,25,53⟩ .empty) ⟨5,true,25,60⟩ (.node .empty ⟨5,true,26,50⟩ .empty)))
def t280_288 : Tree := (.node (.node (.node (.node .empty ⟨5,true,26,59⟩ .empty) ⟨5,true,26,62⟩ .empty) ⟨5,true,28,32⟩ (.node .empty ⟨5,true,28,39⟩ .empty)) ⟨5,true,28,44⟩ (.node (.node .empty ⟨5,true,28,54⟩ .empty) ⟨5,true,28,57⟩ (.node .empty ⟨5,true,28,63⟩ .empty)))
def t271_288 : Tree := .node t271_279 ⟨5,true,26,52⟩ t280_288
def t253_288 : Tree := .node t253_270 ⟨5,true,23,44⟩ t271_288
def t217_288 : Tree := .node t217_252 ⟨5,true,16,59⟩ t253_288
def t145_288 : Tree := .node t145_216 ⟨5,false,15,53⟩ t217_288
def t0_288 : Tree := .node t0_144 ⟨3,true,5,55⟩ t145_288
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 14, 2, 3, 0, 4, 10, 5, 0, 0, 6, 7, 0, 0, 8, 9, 0, 0, 0, 0, 11, 12, 0, 13, 0, 0, 0, 0, 15, 16, 0, 17, 20, 18, 0, 0, 19, 0, 0, 0, 21, 22, 25, 23, 0, 0, 24, 0, 0, 0, 26, 27, 25, 28, 0, 0, 24],#[0, 1, 3, 2, 0, 0, 0, 4, 7, 5, 6, 27, 0, 0, 8, 18, 15, 9, 26, 10, 12, 11, 0, 0, 0, 13, 0, 14, 6, 0, 0, 16, 17, 0, 0, 0, 0, 19, 21, 20, 0, 0, 0, 22, 0, 23, 24, 0, 25, 0, 0, 0, 0, 0, 29, 28, 0, 47, 44, 30, 0, 31, 32, 36, 33, 35, 13, 34, 17, 0, 43, 10, 0, 37, 39, 38, 0, 61, 15, 40, 43, 41, 42, 0, 25, 13, 0, 0, 0, 45, 46, 0, 0, 0, 49, 48, 0, 47, 44, 50, 0, 51, 57, 52, 0, 53, 54, 59, 33, 55, 43, 56, 42, 11, 0, 58, 43, 0, 0, 60, 63, 62, 63, 38, 0, 60, 33, 64, 43, 65, 42, 11],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,3)],[(false,4)],[(true,5)],[(false,6)],[(true,7)],[(false,8)],[(true,3)],[(true,10)],[(false,11)],[(false,12)],[(false,1)],[(true,14)],[(false,15)],[(false,16)],[(false,17)],[(true,18)],[(true,16)],[(true,20)],[(false,21)],[(false,22)],[(true,23),(true,28)],[(true,21),(true,26)],[(true,25)],[(false,26)],[(false,27)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3)],[(true,4)],[(false,5),(false,14)],[(false,4)],[(false,7)],[(true,8)],[(true,9),(true,35)],[(true,10),(true,56),(true,65)],[(false,10)],[(false,33),(true,12),(true,42)],[(true,13)],[(false,8),(false,39)],[(true,15)],[(false,16),(false,34)],[(true,7)],[(true,18)],[(true,19)],[(false,19)],[(true,21)],[(true,22)],[(false,23)],[(false,24),(false,42)],[(false,9)],[(true,5)],[(true,27)],[(false,27)],[(true,29)],[(true,30)],[(false,31)],[(false,32),(false,54),(false,63)],[(true,33)],[(true,32)],[(true,31)],[(true,36)],[(true,37),(true,61)],[(false,37)],[(true,39)],[(true,40)],[(false,41),(false,56),(false,65)],[(false,35),(false,40),(false,55),(false,58),(false,64)],[(false,29),(false,49)],[(true,44)],[(false,45)],[(true,28),(true,48)],[(true,47)],[(false,47)],[(true,49)],[(true,50)],[(true,51)],[(true,52)],[(false,53)],[(true,54)],[(true,55)],[(false,51)],[(true,57)],[(true,53)],[(true,59),(true,62)],[(true,38)],[(true,60)],[(false,60),(false,61)],[(true,63)],[(true,64)]],
  t0_288⟩
theorem check0_9 : t0_9.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check10_18 : t10_18.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node9 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,1,24⟩ = true := by decide
theorem check0_18 : t0_18.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node9 check0_9 check10_18
theorem check19_27 : t19_27.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check28_36 : t28_36.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node27 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,20,40⟩ = true := by decide
theorem check19_36 : t19_36.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node27 check19_27 check28_36
theorem node18 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,7,0⟩ = true := by decide
theorem check0_36 : t0_36.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node18 check0_18 check19_36
theorem check37_45 : t37_45.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check46_54 : t46_54.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node45 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,12,8⟩ = true := by decide
theorem check37_54 : t37_54.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node45 check37_45 check46_54
theorem check55_63 : t55_63.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check64_72 : t64_72.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node63 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,27,31⟩ = true := by decide
theorem check55_72 : t55_72.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node63 check55_63 check64_72
theorem node54 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,17,61⟩ = true := by decide
theorem check37_72 : t37_72.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node54 check37_54 check55_72
theorem node36 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,25,64⟩ = true := by decide
theorem check0_72 : t0_72.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node36 check0_36 check37_72
theorem check73_81 : t73_81.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check82_90 : t82_90.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node81 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,16,21⟩ = true := by decide
theorem check73_90 : t73_90.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node81 check73_81 check82_90
theorem check91_99 : t91_99.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check100_108 : t100_108.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node99 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,2,10⟩ = true := by decide
theorem check91_108 : t91_108.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node99 check91_99 check100_108
theorem node90 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,21,63⟩ = true := by decide
theorem check73_108 : t73_108.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node90 check73_90 check91_108
theorem check109_117 : t109_117.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check118_126 : t118_126.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node117 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,12,18⟩ = true := by decide
theorem check109_126 : t109_126.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node117 check109_117 check118_126
theorem check127_135 : t127_135.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check136_144 : t136_144.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node135 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,28,47⟩ = true := by decide
theorem check127_144 : t127_144.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node135 check127_135 check136_144
theorem node126 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,13,60⟩ = true := by decide
theorem check109_144 : t109_144.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node126 check109_126 check127_144
theorem node108 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,4,32⟩ = true := by decide
theorem check73_144 : t73_144.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node108 check73_108 check109_144
theorem node72 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,3,3⟩ = true := by decide
theorem check0_144 : t0_144.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node72 check0_72 check73_144
theorem check145_153 : t145_153.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check154_162 : t154_162.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node153 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,18,52⟩ = true := by decide
theorem check145_162 : t145_162.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node153 check145_153 check154_162
theorem check163_171 : t163_171.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check172_180 : t172_180.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node171 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,28,62⟩ = true := by decide
theorem check163_180 : t163_180.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node171 check163_171 check172_180
theorem node162 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,23,59⟩ = true := by decide
theorem check145_180 : t145_180.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node162 check145_162 check163_180
theorem check181_189 : t181_189.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check190_198 : t190_198.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node189 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,11,61⟩ = true := by decide
theorem check181_198 : t181_198.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node189 check181_189 check190_198
theorem check199_207 : t199_207.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check208_216 : t208_216.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node207 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,0,5⟩ = true := by decide
theorem check199_216 : t199_216.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node207 check199_207 check208_216
theorem node198 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,24,29⟩ = true := by decide
theorem check181_216 : t181_216.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node198 check181_198 check199_216
theorem node180 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,6,8⟩ = true := by decide
theorem check145_216 : t145_216.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node180 check145_180 check181_216
theorem check217_225 : t217_225.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check226_234 : t226_234.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node225 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,22,40⟩ = true := by decide
theorem check217_234 : t217_234.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node225 check217_225 check226_234
theorem check235_243 : t235_243.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check244_252 : t244_252.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node243 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,3,64⟩ = true := by decide
theorem check235_252 : t235_252.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node243 check235_243 check244_252
theorem node234 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,27,58⟩ = true := by decide
theorem check217_252 : t217_252.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node234 check217_234 check235_252
theorem check253_261 : t253_261.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check262_270 : t262_270.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node261 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,20,51⟩ = true := by decide
theorem check253_270 : t253_270.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node261 check253_261 check262_270
theorem check271_279 : t271_279.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check280_288 : t280_288.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node279 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,26,52⟩ = true := by decide
theorem check271_288 : t271_288.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node279 check271_279 check280_288
theorem node270 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,23,44⟩ = true := by decide
theorem check253_288 : t253_288.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node270 check253_270 check271_288
theorem node252 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,16,59⟩ = true := by decide
theorem check217_288 : t217_288.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node252 check217_252 check253_288
theorem node216 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,15,53⟩ = true := by decide
theorem check145_288 : t145_288.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node216 check145_216 check217_288
theorem node144 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,5,55⟩ = true := by decide
theorem check0_288 : t0_288.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node144 check0_144 check145_288
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_288
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M079
