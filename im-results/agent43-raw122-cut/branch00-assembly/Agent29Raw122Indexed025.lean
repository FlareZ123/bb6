import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M025
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_8 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,5⟩ .empty) ⟨0,false,0,17⟩ (.node .empty ⟨0,false,0,21⟩ .empty)) ⟨0,false,1,14⟩ (.node (.node .empty ⟨0,false,1,32⟩ .empty) ⟨0,false,4,4⟩ (.node .empty ⟨0,false,4,20⟩ .empty)))
def t9_17 : Tree := (.node (.node (.node (.node .empty ⟨0,false,6,20⟩ .empty) ⟨0,false,6,25⟩ .empty) ⟨0,false,6,36⟩ (.node .empty ⟨0,false,8,5⟩ .empty)) ⟨0,false,9,0⟩ (.node (.node .empty ⟨0,false,15,20⟩ .empty) ⟨0,false,15,25⟩ (.node .empty ⟨0,false,15,26⟩ .empty)))
def t0_17 : Tree := .node t0_8 ⟨0,false,6,8⟩ t9_17
def t18_26 : Tree := (.node (.node (.node (.node .empty ⟨0,false,17,41⟩ .empty) ⟨0,false,18,5⟩ .empty) ⟨0,false,18,27⟩ (.node .empty ⟨0,false,18,41⟩ .empty)) ⟨0,false,20,14⟩ (.node (.node .empty ⟨0,false,20,53⟩ .empty) ⟨0,false,21,4⟩ (.node .empty ⟨0,false,21,40⟩ .empty)))
def t27_35 : Tree := (.node (.node (.node (.node .empty ⟨0,false,23,50⟩ .empty) ⟨0,false,25,5⟩ .empty) ⟨0,false,25,13⟩ (.node .empty ⟨0,false,25,52⟩ .empty)) ⟨0,false,26,0⟩ (.node (.node .empty ⟨0,false,35,20⟩ .empty) ⟨0,false,35,25⟩ (.node .empty ⟨0,false,35,26⟩ .empty)))
def t18_35 : Tree := .node t18_26 ⟨0,false,23,8⟩ t27_35
def t0_35 : Tree := .node t0_17 ⟨0,false,15,36⟩ t18_35
def t36_44 : Tree := (.node (.node (.node (.node .empty ⟨0,true,0,4⟩ .empty) ⟨0,true,0,20⟩ .empty) ⟨0,true,4,13⟩ (.node .empty ⟨0,true,4,18⟩ .empty)) ⟨0,true,4,31⟩ (.node (.node .empty ⟨0,true,5,12⟩ .empty) ⟨0,true,5,30⟩ (.node .empty ⟨0,true,5,32⟩ .empty)))
def t45_53 : Tree := (.node (.node (.node (.node .empty ⟨0,true,6,11⟩ .empty) ⟨0,true,6,18⟩ .empty) ⟨0,true,6,29⟩ (.node .empty ⟨0,true,6,31⟩ .empty)) ⟨0,true,6,48⟩ (.node (.node .empty ⟨0,true,9,4⟩ .empty) ⟨0,true,14,30⟩ (.node .empty ⟨0,true,14,32⟩ .empty)))
def t36_53 : Tree := .node t36_44 ⟨0,true,5,49⟩ t45_53
def t54_62 : Tree := (.node (.node (.node (.node .empty ⟨0,true,14,49⟩ .empty) ⟨0,true,15,18⟩ .empty) ⟨0,true,15,29⟩ (.node .empty ⟨0,true,15,31⟩ .empty)) ⟨0,true,15,46⟩ (.node (.node .empty ⟨0,true,15,48⟩ .empty) ⟨0,true,16,17⟩ (.node .empty ⟨0,true,16,56⟩ .empty)))
def t63_71 : Tree := (.node (.node (.node (.node .empty ⟨0,true,21,13⟩ .empty) ⟨0,true,21,52⟩ .empty) ⟨0,true,22,12⟩ (.node .empty ⟨0,true,22,51⟩ .empty)) ⟨0,true,23,11⟩ (.node (.node .empty ⟨0,true,23,16⟩ .empty) ⟨0,true,23,55⟩ (.node .empty ⟨0,true,26,4⟩ .empty)))
def t54_71 : Tree := .node t54_62 ⟨0,true,18,40⟩ t63_71
def t36_71 : Tree := .node t36_53 ⟨0,true,14,47⟩ t54_71
def t0_71 : Tree := .node t0_35 ⟨0,false,35,36⟩ t36_71
def t72_80 : Tree := (.node (.node (.node (.node .empty ⟨0,true,26,51⟩ .empty) ⟨0,true,32,30⟩ .empty) ⟨0,true,32,32⟩ (.node .empty ⟨0,true,32,47⟩ .empty)) ⟨0,true,32,49⟩ (.node (.node .empty ⟨0,true,35,18⟩ .empty) ⟨0,true,35,29⟩ (.node .empty ⟨0,true,35,31⟩ .empty)))
def t81_89 : Tree := (.node (.node (.node (.node .empty ⟨0,true,35,48⟩ .empty) ⟨0,true,36,17⟩ .empty) ⟨0,true,36,56⟩ (.node .empty ⟨1,false,1,0⟩ .empty)) ⟨1,false,1,16⟩ (.node (.node .empty ⟨1,false,1,34⟩ .empty) ⟨1,false,5,3⟩ (.node .empty ⟨1,false,5,19⟩ .empty)))
def t72_89 : Tree := .node t72_80 ⟨0,true,35,46⟩ t81_89
def t90_98 : Tree := (.node (.node (.node (.node .empty ⟨1,false,14,7⟩ .empty) ⟨1,false,14,19⟩ .empty) ⟨1,false,14,24⟩ (.node .empty ⟨1,false,14,35⟩ .empty)) ⟨1,false,19,17⟩ (.node (.node .empty ⟨1,false,19,56⟩ .empty) ⟨1,false,22,3⟩ (.node .empty ⟨1,false,22,39⟩ .empty)))
def t99_107 : Tree := (.node (.node (.node (.node .empty ⟨1,false,28,25⟩ .empty) ⟨1,false,28,58⟩ .empty) ⟨1,false,32,19⟩ (.node .empty ⟨1,false,32,24⟩ .empty)) ⟨1,false,32,35⟩ (.node (.node .empty ⟨1,false,32,43⟩ .empty) ⟨1,true,1,4⟩ (.node .empty ⟨1,true,1,20⟩ .empty)))
def t90_107 : Tree := .node t90_98 ⟨1,false,28,7⟩ t99_107
def t72_107 : Tree := .node t72_89 ⟨1,false,10,0⟩ t90_107
def t108_116 : Tree := (.node (.node (.node (.node .empty ⟨1,true,2,18⟩ .empty) ⟨1,true,2,31⟩ .empty) ⟨1,true,13,4⟩ (.node .empty ⟨1,true,19,4⟩ .empty)) ⟨1,true,19,40⟩ (.node (.node .empty ⟨1,true,20,40⟩ .empty) ⟨1,true,27,4⟩ (.node .empty ⟨1,true,27,12⟩ .empty)))
def t117_125 : Tree := (.node (.node (.node (.node .empty ⟨1,true,31,13⟩ .empty) ⟨1,true,31,52⟩ .empty) ⟨1,true,32,17⟩ (.node .empty ⟨1,true,32,56⟩ .empty)) ⟨2,false,2,0⟩ (.node (.node .empty ⟨2,false,2,15⟩ .empty) ⟨2,false,2,33⟩ (.node .empty ⟨2,false,6,1⟩ .empty)))
def t108_125 : Tree := .node t108_116 ⟨1,true,27,51⟩ t117_125
def t126_134 : Tree := (.node (.node (.node (.node .empty ⟨2,false,6,32⟩ .empty) ⟨2,false,6,49⟩ .empty) ⟨2,false,11,0⟩ (.node .empty ⟨2,false,15,6⟩ .empty)) ⟨2,false,15,12⟩ (.node (.node .empty ⟨2,false,15,14⟩ .empty) ⟨2,false,15,30⟩ (.node .empty ⟨2,false,15,32⟩ .empty)))
def t135_143 : Tree := (.node (.node (.node (.node .empty ⟨2,false,15,49⟩ .empty) ⟨2,false,23,1⟩ .empty) ⟨2,false,23,37⟩ (.node .empty ⟨2,false,29,6⟩ .empty)) ⟨2,false,29,24⟩ (.node (.node .empty ⟨2,false,29,57⟩ .empty) ⟨2,false,33,16⟩ (.node .empty ⟨2,false,33,55⟩ .empty)))
def t126_143 : Tree := .node t126_134 ⟨2,false,15,47⟩ t135_143
def t108_143 : Tree := .node t108_125 ⟨2,false,6,14⟩ t126_143
def t72_143 : Tree := .node t72_107 ⟨1,true,2,13⟩ t108_143
def t0_143 : Tree := .node t0_71 ⟨0,true,26,12⟩ t72_143
def t144_152 : Tree := (.node (.node (.node (.node .empty ⟨2,false,35,14⟩ .empty) ⟨2,false,35,30⟩ .empty) ⟨2,false,35,32⟩ (.node .empty ⟨2,false,35,42⟩ .empty)) ⟨2,false,35,47⟩ (.node (.node .empty ⟨2,false,35,49⟩ .empty) ⟨3,false,2,1⟩ (.node .empty ⟨3,false,2,14⟩ .empty)))
def t153_161 : Tree := (.node (.node (.node (.node .empty ⟨3,false,3,0⟩ .empty) ⟨3,false,3,13⟩ .empty) ⟨3,false,3,18⟩ (.node .empty ⟨3,false,3,31⟩ .empty)) ⟨3,false,11,1⟩ (.node (.node .empty ⟨3,false,12,0⟩ .empty) ⟨3,false,15,5⟩ (.node .empty ⟨3,false,16,4⟩ .empty)))
def t144_161 : Tree := .node t144_152 ⟨3,false,2,32⟩ t153_161
def t162_170 : Tree := (.node (.node (.node (.node .empty ⟨3,false,29,13⟩ .empty) ⟨3,false,29,52⟩ .empty) ⟨3,false,30,4⟩ (.node .empty ⟨3,false,30,12⟩ .empty)) ⟨3,false,30,51⟩ (.node (.node .empty ⟨3,false,33,37⟩ .empty) ⟨3,false,34,15⟩ (.node .empty ⟨3,false,34,54⟩ .empty)))
def t171_179 : Tree := (.node (.node (.node (.node .empty ⟨3,false,36,40⟩ .empty) ⟨3,true,1,2⟩ .empty) ⟨3,true,1,18⟩ (.node .empty ⟨3,true,7,0⟩ .empty)) ⟨3,true,7,13⟩ (.node (.node .empty ⟨3,true,7,18⟩ .empty) ⟨3,true,7,31⟩ (.node .empty ⟨3,true,7,48⟩ .empty)))
def t162_179 : Tree := .node t162_170 ⟨3,false,35,41⟩ t171_179
def t144_179 : Tree := .node t144_161 ⟨3,false,29,5⟩ t162_179
def t180_188 : Tree := (.node (.node (.node (.node .empty ⟨3,true,14,9⟩ .empty) ⟨3,true,16,11⟩ .empty) ⟨3,true,16,13⟩ (.node .empty ⟨3,true,16,18⟩ .empty)) ⟨3,true,16,29⟩ (.node (.node .empty ⟨3,true,16,31⟩ .empty) ⟨3,true,16,46⟩ (.node .empty ⟨3,true,16,48⟩ .empty)))
def t189_197 : Tree := (.node (.node (.node (.node .empty ⟨3,true,24,0⟩ .empty) ⟨3,true,24,15⟩ .empty) ⟨3,true,24,54⟩ (.node .empty ⟨3,true,28,9⟩ .empty)) ⟨3,true,28,14⟩ (.node (.node .empty ⟨3,true,28,53⟩ .empty) ⟨3,true,32,44⟩ (.node .empty ⟨3,true,36,11⟩ .empty)))
def t180_197 : Tree := .node t180_188 ⟨3,true,19,38⟩ t189_197
def t198_206 : Tree := (.node (.node (.node (.node .empty ⟨3,true,36,18⟩ .empty) ⟨3,true,36,29⟩ .empty) ⟨3,true,36,31⟩ (.node .empty ⟨3,true,36,46⟩ .empty)) ⟨3,true,36,48⟩ (.node (.node .empty ⟨4,false,1,6⟩ .empty) ⟨4,false,1,22⟩ (.node .empty ⟨4,false,8,0⟩ .empty)))
def t207_215 : Tree := (.node (.node (.node (.node .empty ⟨4,false,17,28⟩ .empty) ⟨4,false,17,45⟩ .empty) ⟨4,false,20,6⟩ (.node .empty ⟨4,false,20,42⟩ .empty)) ⟨4,false,25,0⟩ (.node (.node .empty ⟨4,false,25,13⟩ .empty) ⟨4,false,25,52⟩ (.node .empty ⟨4,true,0,6⟩ .empty)))
def t198_215 : Tree := .node t198_206 ⟨4,false,17,10⟩ t207_215
def t180_215 : Tree := .node t180_197 ⟨3,true,36,13⟩ t198_215
def t144_215 : Tree := .node t144_179 ⟨3,true,10,2⟩ t180_215
def t216_224 : Tree := (.node (.node (.node (.node .empty ⟨4,true,1,15⟩ .empty) ⟨4,true,1,33⟩ .empty) ⟨4,true,2,1⟩ (.node .empty ⟨4,true,2,14⟩ .empty)) ⟨4,true,2,32⟩ (.node (.node .empty ⟨4,true,2,49⟩ .empty) ⟨4,true,8,6⟩ (.node .empty ⟨4,true,8,12⟩ .empty)))
def t225_233 : Tree := (.node (.node (.node (.node .empty ⟨4,true,8,30⟩ .empty) ⟨4,true,8,32⟩ .empty) ⟨4,true,8,47⟩ (.node .empty ⟨4,true,8,49⟩ .empty)) ⟨4,true,11,1⟩ (.node (.node .empty ⟨4,true,15,5⟩ .empty) ⟨4,true,15,27⟩ (.node .empty ⟨4,true,17,12⟩ .empty)))
def t216_233 : Tree := .node t216_224 ⟨4,true,8,14⟩ t225_233
def t234_242 : Tree := (.node (.node (.node (.node .empty ⟨4,true,17,30⟩ .empty) ⟨4,true,17,32⟩ .empty) ⟨4,true,17,42⟩ (.node .empty ⟨4,true,17,47⟩ .empty)) ⟨4,true,17,49⟩ (.node (.node .empty ⟨4,true,18,6⟩ .empty) ⟨4,true,18,42⟩ (.node .empty ⟨4,true,20,15⟩ .empty)))
def t243_251 : Tree := (.node (.node (.node (.node .empty ⟨4,true,25,6⟩ .empty) ⟨4,true,25,24⟩ .empty) ⟨4,true,25,57⟩ (.node .empty ⟨4,true,29,5⟩ .empty)) ⟨4,true,29,13⟩ (.node (.node .empty ⟨4,true,29,52⟩ .empty) ⟨4,true,33,37⟩ (.node .empty ⟨4,true,35,27⟩ .empty)))
def t234_251 : Tree := .node t234_242 ⟨4,true,20,54⟩ t243_251
def t216_251 : Tree := .node t216_233 ⟨4,true,17,14⟩ t234_251
def t252_260 : Tree := (.node (.node (.node (.node .empty ⟨5,false,0,7⟩ .empty) ⟨5,false,0,23⟩ .empty) ⟨5,false,17,7⟩ (.node .empty ⟨5,false,17,43⟩ .empty)) ⟨5,true,0,16⟩ (.node (.node .empty ⟨5,true,0,34⟩ .empty) ⟨5,true,1,3⟩ (.node .empty ⟨5,true,1,19⟩ .empty)))
def t261_269 : Tree := (.node (.node (.node (.node .empty ⟨5,true,7,19⟩ .empty) ⟨5,true,7,24⟩ .empty) ⟨5,true,7,35⟩ (.node .empty ⟨5,true,10,3⟩ .empty)) ⟨5,true,14,10⟩ (.node (.node .empty ⟨5,true,14,28⟩ .empty) ⟨5,true,16,19⟩ (.node .empty ⟨5,true,16,24⟩ .empty)))
def t252_269 : Tree := .node t252_260 ⟨5,true,7,7⟩ t261_269
def t270_286 : Tree := (.node (.node (.node (.node (.node .empty ⟨5,true,16,43⟩ .empty) ⟨5,true,17,16⟩ .empty) ⟨5,true,17,55⟩ (.node .empty ⟨5,true,19,39⟩ .empty)) ⟨5,true,24,7⟩ (.node (.node .empty ⟨5,true,24,25⟩ .empty) ⟨5,true,24,58⟩ (.node .empty ⟨5,true,28,10⟩ .empty))) ⟨5,true,28,15⟩ (.node (.node (.node .empty ⟨5,true,28,54⟩ .empty) ⟨5,true,32,28⟩ (.node .empty ⟨5,true,32,45⟩ .empty)) ⟨5,true,36,19⟩ (.node (.node .empty ⟨5,true,36,24⟩ .empty) ⟨5,true,36,35⟩ (.node .empty ⟨5,true,36,43⟩ .empty))))
def t252_286 : Tree := .node t252_269 ⟨5,true,16,35⟩ t270_286
def t216_286 : Tree := .node t216_251 ⟨4,true,35,41⟩ t252_286
def t144_286 : Tree := .node t144_215 ⟨4,true,0,22⟩ t216_286
def t0_286 : Tree := .node t0_143 ⟨2,false,35,12⟩ t144_286
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 0, 0, 0, 0, 5, 0, 6, 7, 14, 0, 8, 9, 13, 0, 10, 0, 11, 12, 0, 0, 0, 0, 0, 0, 15, 16, 32, 0, 17, 18, 20, 0, 19, 0, 33, 21, 31, 0, 22, 0, 23, 24, 28, 0, 25, 26, 27, 0, 10, 0, 0, 0, 29, 30, 0, 0, 0, 0, 0, 0, 35, 34, 0, 0, 0, 36, 32, 0, 17],#[0, 1, 3, 2, 0, 0, 4, 0, 6, 5, 10, 9, 7, 0, 8, 0, 0, 0, 0, 0, 11, 0, 0, 12, 24, 13, 15, 14, 19, 18, 16, 37, 17, 51, 27, 26, 33, 32, 20, 0, 22, 21, 0, 0, 23, 0, 0, 0, 25, 0, 50, 0, 0, 0, 28, 0, 29, 0, 0, 30, 35, 31, 33, 32, 19, 18, 34, 0, 21, 0, 36, 0, 0, 0, 39, 38, 0, 0, 40, 0, 42, 41, 45, 44, 43, 0, 26, 0, 0, 0, 46, 0, 0, 47, 35, 48, 0, 49, 19, 18, 0, 0, 57, 52, 54, 53, 0, 0, 55, 37, 56, 51, 27, 26, 58, 0, 50, 0],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,4)],[(true,5)],[(false,6)],[(true,7)],[(false,8)],[(true,9),(true,26)],[(true,10)],[(false,11)],[(true,8)],[(true,6)],[(true,14)],[(false,15)],[(true,16),(true,36)],[(false,17)],[(true,18)],[(true,17)],[(false,20)],[(true,21)],[(true,22)],[(false,23)],[(true,24)],[(false,25)],[(true,25)],[(true,23)],[(true,28)],[(false,29)],[(true,20)],[(true,15),(true,35)],[(true,19)],[(false,33)],[(true,32)],[(false,35)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(true,4)],[(false,4)],[(false,6)],[(false,7)],[(true,5)],[(false,5)],[(false,10)],[(true,11)],[(true,12)],[(true,13)],[(false,13)],[(false,15)],[(false,16)],[(true,14),(true,32),(true,49)],[(false,14),(false,32),(false,49)],[(false,19)],[(false,34),(true,20)],[(false,20)],[(false,22)],[(false,12)],[(false,24)],[(false,43),(true,17),(true,56)],[(false,17),(false,56)],[(false,27)],[(false,28)],[(true,29)],[(true,30)],[(true,18),(true,31)],[(false,18),(false,31)],[(false,33)],[(false,30),(false,47)],[(false,35)],[(true,15),(true,54)],[(true,37)],[(false,37)],[(false,39)],[(true,40)],[(false,40)],[(false,42)],[(true,41)],[(false,41)],[(false,45)],[(true,46)],[(true,47)],[(true,48)],[(false,25),(false,58)],[(true,16),(true,55)],[(true,51)],[(true,52)],[(false,52)],[(false,54)],[(false,55)],[(false,51)],[(false,57)]],
  t0_286⟩
theorem check0_8 : t0_8.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check9_17 : t9_17.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node8 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,6,8⟩ = true := by decide
theorem check0_17 : t0_17.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node8 check0_8 check9_17
theorem check18_26 : t18_26.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check27_35 : t27_35.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node26 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,23,8⟩ = true := by decide
theorem check18_35 : t18_35.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node26 check18_26 check27_35
theorem node17 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,15,36⟩ = true := by decide
theorem check0_35 : t0_35.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node17 check0_17 check18_35
theorem check36_44 : t36_44.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check45_53 : t45_53.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node44 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,5,49⟩ = true := by decide
theorem check36_53 : t36_53.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node44 check36_44 check45_53
theorem check54_62 : t54_62.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check63_71 : t63_71.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node62 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,18,40⟩ = true := by decide
theorem check54_71 : t54_71.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node62 check54_62 check63_71
theorem node53 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,14,47⟩ = true := by decide
theorem check36_71 : t36_71.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node53 check36_53 check54_71
theorem node35 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,35,36⟩ = true := by decide
theorem check0_71 : t0_71.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node35 check0_35 check36_71
theorem check72_80 : t72_80.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check81_89 : t81_89.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node80 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,35,46⟩ = true := by decide
theorem check72_89 : t72_89.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node80 check72_80 check81_89
theorem check90_98 : t90_98.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check99_107 : t99_107.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node98 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,28,7⟩ = true := by decide
theorem check90_107 : t90_107.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node98 check90_98 check99_107
theorem node89 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,10,0⟩ = true := by decide
theorem check72_107 : t72_107.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node89 check72_89 check90_107
theorem check108_116 : t108_116.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check117_125 : t117_125.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node116 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,27,51⟩ = true := by decide
theorem check108_125 : t108_125.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node116 check108_116 check117_125
theorem check126_134 : t126_134.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check135_143 : t135_143.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node134 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,15,47⟩ = true := by decide
theorem check126_143 : t126_143.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node134 check126_134 check135_143
theorem node125 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,6,14⟩ = true := by decide
theorem check108_143 : t108_143.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node125 check108_125 check126_143
theorem node107 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,2,13⟩ = true := by decide
theorem check72_143 : t72_143.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node107 check72_107 check108_143
theorem node71 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,26,12⟩ = true := by decide
theorem check0_143 : t0_143.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node71 check0_71 check72_143
theorem check144_152 : t144_152.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check153_161 : t153_161.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node152 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,2,32⟩ = true := by decide
theorem check144_161 : t144_161.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node152 check144_152 check153_161
theorem check162_170 : t162_170.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check171_179 : t171_179.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node170 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,35,41⟩ = true := by decide
theorem check162_179 : t162_179.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node170 check162_170 check171_179
theorem node161 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,29,5⟩ = true := by decide
theorem check144_179 : t144_179.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node161 check144_161 check162_179
theorem check180_188 : t180_188.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check189_197 : t189_197.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node188 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,19,38⟩ = true := by decide
theorem check180_197 : t180_197.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node188 check180_188 check189_197
theorem check198_206 : t198_206.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check207_215 : t207_215.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node206 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,17,10⟩ = true := by decide
theorem check198_215 : t198_215.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node206 check198_206 check207_215
theorem node197 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,36,13⟩ = true := by decide
theorem check180_215 : t180_215.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node197 check180_197 check198_215
theorem node179 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,10,2⟩ = true := by decide
theorem check144_215 : t144_215.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node179 check144_179 check180_215
theorem check216_224 : t216_224.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check225_233 : t225_233.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node224 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,8,14⟩ = true := by decide
theorem check216_233 : t216_233.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node224 check216_224 check225_233
theorem check234_242 : t234_242.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check243_251 : t243_251.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node242 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,20,54⟩ = true := by decide
theorem check234_251 : t234_251.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node242 check234_242 check243_251
theorem node233 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,17,14⟩ = true := by decide
theorem check216_251 : t216_251.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node233 check216_233 check234_251
theorem check252_260 : t252_260.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check261_269 : t261_269.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node260 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,7,7⟩ = true := by decide
theorem check252_269 : t252_269.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node260 check252_260 check261_269
theorem check270_286 : t270_286.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node269 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,16,35⟩ = true := by decide
theorem check252_286 : t252_286.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node269 check252_269 check270_286
theorem node251 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,35,41⟩ = true := by decide
theorem check216_286 : t216_286.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node251 check216_251 check252_286
theorem node215 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,0,22⟩ = true := by decide
theorem check144_286 : t144_286.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node215 check144_215 check216_286
theorem node143 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,35,12⟩ = true := by decide
theorem check0_286 : t0_286.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node143 check0_143 check144_286
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_286
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M025
