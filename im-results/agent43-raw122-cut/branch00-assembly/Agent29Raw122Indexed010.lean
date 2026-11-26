import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M010
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_12 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,9⟩ (.node .empty ⟨0,false,0,23⟩ .empty)) ⟨0,false,3,13⟩ (.node (.node .empty ⟨0,false,3,42⟩ .empty) ⟨0,false,5,5⟩ .empty)) ⟨0,false,5,37⟩ (.node (.node (.node .empty ⟨0,false,5,47⟩ .empty) ⟨0,false,6,0⟩ .empty) ⟨0,false,6,17⟩ (.node (.node .empty ⟨0,false,6,32⟩ .empty) ⟨0,false,6,42⟩ .empty)))
def t13_24 : Tree := (.node (.node (.node (.node .empty ⟨0,false,9,18⟩ .empty) ⟨0,false,9,37⟩ .empty) ⟨0,false,9,47⟩ (.node (.node .empty ⟨0,false,10,4⟩ .empty) ⟨0,false,10,17⟩ .empty)) ⟨0,false,10,32⟩ (.node (.node (.node .empty ⟨0,false,10,36⟩ .empty) ⟨0,false,10,42⟩ .empty) ⟨0,false,10,46⟩ (.node (.node .empty ⟨0,false,20,18⟩ .empty) ⟨0,false,20,37⟩ .empty)))
def t0_24 : Tree := .node t0_12 ⟨0,false,6,46⟩ t13_24
def t25_37 : Tree := (.node (.node (.node (.node .empty ⟨0,false,21,4⟩ .empty) ⟨0,false,21,13⟩ (.node .empty ⟨0,false,21,17⟩ .empty)) ⟨0,false,21,32⟩ (.node (.node .empty ⟨0,false,21,36⟩ .empty) ⟨0,false,21,42⟩ .empty)) ⟨0,false,21,46⟩ (.node (.node (.node .empty ⟨0,false,22,5⟩ .empty) ⟨0,true,0,4⟩ .empty) ⟨0,true,0,26⟩ (.node (.node .empty ⟨0,true,1,22⟩ .empty) ⟨0,true,3,17⟩ .empty)))
def t38_49 : Tree := (.node (.node (.node (.node .empty ⟨0,true,5,12⟩ .empty) ⟨0,true,5,41⟩ .empty) ⟨0,true,6,4⟩ (.node (.node .empty ⟨0,true,6,36⟩ .empty) ⟨0,true,6,46⟩ .empty)) ⟨0,true,9,31⟩ (.node (.node (.node .empty ⟨0,true,9,41⟩ .empty) ⟨0,true,10,17⟩ .empty) ⟨0,true,10,36⟩ (.node (.node .empty ⟨0,true,10,46⟩ .empty) ⟨0,true,20,31⟩ .empty)))
def t25_49 : Tree := .node t25_37 ⟨0,true,3,46⟩ t38_49
def t0_49 : Tree := .node t0_24 ⟨0,false,20,47⟩ t25_49
def t50_62 : Tree := (.node (.node (.node (.node .empty ⟨0,true,21,17⟩ .empty) ⟨0,true,21,36⟩ (.node .empty ⟨0,true,21,46⟩ .empty)) ⟨0,true,22,12⟩ (.node (.node .empty ⟨0,true,23,4⟩ .empty) ⟨1,false,0,5⟩ .empty)) ⟨1,false,0,27⟩ (.node (.node (.node .empty ⟨1,false,1,0⟩ .empty) ⟨1,false,1,8⟩ .empty) ⟨1,false,1,22⟩ (.node (.node .empty ⟨1,false,2,18⟩ .empty) ⟨1,false,2,47⟩ .empty)))
def t63_74 : Tree := (.node (.node (.node (.node .empty ⟨1,false,5,41⟩ .empty) ⟨1,false,6,4⟩ .empty) ⟨1,false,6,36⟩ (.node (.node .empty ⟨1,false,6,46⟩ .empty) ⟨1,false,9,0⟩ .empty)) ⟨1,false,9,16⟩ (.node (.node (.node .empty ⟨1,false,9,31⟩ .empty) ⟨1,false,9,41⟩ .empty) ⟨1,false,9,45⟩ (.node (.node .empty ⟨1,false,10,17⟩ .empty) ⟨1,false,10,36⟩ .empty)))
def t50_74 : Tree := .node t50_62 ⟨1,false,5,12⟩ t63_74
def t75_87 : Tree := (.node (.node (.node (.node .empty ⟨1,false,20,3⟩ .empty) ⟨1,false,20,12⟩ (.node .empty ⟨1,false,20,16⟩ .empty)) ⟨1,false,20,31⟩ (.node (.node .empty ⟨1,false,20,35⟩ .empty) ⟨1,false,20,41⟩ .empty)) ⟨1,false,20,45⟩ (.node (.node (.node .empty ⟨1,false,21,13⟩ .empty) ⟨1,false,21,17⟩ .empty) ⟨1,false,21,36⟩ (.node (.node .empty ⟨1,false,21,46⟩ .empty) ⟨1,false,23,4⟩ .empty)))
def t88_99 : Tree := (.node (.node (.node (.node .empty ⟨1,true,0,23⟩ .empty) ⟨1,true,3,13⟩ .empty) ⟨1,true,3,42⟩ (.node (.node .empty ⟨1,true,5,5⟩ .empty) ⟨1,true,5,37⟩ .empty)) ⟨1,true,5,47⟩ (.node (.node (.node .empty ⟨1,true,6,0⟩ .empty) ⟨1,true,6,19⟩ .empty) ⟨1,true,6,32⟩ (.node (.node .empty ⟨1,true,6,42⟩ .empty) ⟨1,true,6,48⟩ .empty)))
def t75_99 : Tree := .node t75_87 ⟨1,false,24,0⟩ t88_99
def t50_99 : Tree := .node t50_74 ⟨1,false,10,46⟩ t75_99
def t0_99 : Tree := .node t0_49 ⟨0,true,20,41⟩ t50_99
def t100_112 : Tree := (.node (.node (.node (.node .empty ⟨1,true,9,37⟩ .empty) ⟨1,true,9,47⟩ (.node .empty ⟨1,true,10,32⟩ .empty)) ⟨1,true,10,42⟩ (.node (.node .empty ⟨1,true,20,18⟩ .empty) ⟨1,true,20,37⟩ .empty)) ⟨1,true,20,47⟩ (.node (.node (.node .empty ⟨1,true,21,32⟩ .empty) ⟨1,true,21,42⟩ .empty) ⟨1,true,22,5⟩ (.node (.node .empty ⟨2,false,1,4⟩ .empty) ⟨2,false,1,26⟩ .empty)))
def t113_124 : Tree := (.node (.node (.node (.node .empty ⟨2,false,2,6⟩ .empty) ⟨2,false,2,21⟩ .empty) ⟨2,false,2,28⟩ (.node (.node .empty ⟨2,false,6,11⟩ .empty) ⟨2,false,6,40⟩ .empty)) ⟨2,false,9,3⟩ (.node (.node (.node .empty ⟨2,false,9,35⟩ .empty) ⟨2,false,9,45⟩ .empty) ⟨2,false,10,0⟩ (.node (.node .empty ⟨2,false,10,10⟩ .empty) ⟨2,false,10,30⟩ .empty)))
def t100_124 : Tree := .node t100_112 ⟨2,false,2,0⟩ t113_124
def t125_137 : Tree := (.node (.node (.node (.node .empty ⟨2,false,10,40⟩ .empty) ⟨2,false,10,49⟩ (.node .empty ⟨2,false,17,17⟩ .empty)) ⟨2,false,17,46⟩ (.node (.node .empty ⟨2,false,20,12⟩ .empty) ⟨2,false,20,16⟩ .empty)) ⟨2,false,20,35⟩ (.node (.node (.node .empty ⟨2,false,20,45⟩ .empty) ⟨2,false,21,1⟩ .empty) ⟨2,false,21,10⟩ (.node (.node .empty ⟨2,false,21,11⟩ .empty) ⟨2,false,21,29⟩ .empty)))
def t138_149 : Tree := (.node (.node (.node (.node .empty ⟨2,false,21,39⟩ .empty) ⟨2,false,21,40⟩ .empty) ⟨2,false,21,49⟩ (.node (.node .empty ⟨2,false,24,3⟩ .empty) ⟨2,false,25,0⟩ .empty)) ⟨3,false,1,6⟩ (.node (.node (.node .empty ⟨3,false,1,21⟩ .empty) ⟨3,false,1,28⟩ .empty) ⟨3,false,2,1⟩ (.node (.node .empty ⟨3,false,2,20⟩ .empty) ⟨3,false,3,0⟩ .empty)))
def t125_149 : Tree := .node t125_137 ⟨2,false,21,30⟩ t138_149
def t100_149 : Tree := .node t100_124 ⟨2,false,10,39⟩ t125_149
def t150_162 : Tree := (.node (.node (.node (.node .empty ⟨3,false,3,48⟩ .empty) ⟨3,false,4,3⟩ (.node .empty ⟨3,false,4,25⟩ .empty)) ⟨3,false,6,10⟩ (.node (.node .empty ⟨3,false,6,39⟩ .empty) ⟨3,false,7,2⟩ .empty)) ⟨3,false,7,34⟩ (.node (.node (.node .empty ⟨3,false,7,44⟩ .empty) ⟨3,false,8,0⟩ .empty) ⟨3,false,8,30⟩ (.node (.node .empty ⟨3,false,8,40⟩ .empty) ⟨3,false,9,2⟩ .empty)))
def t163_174 : Tree := (.node (.node (.node (.node .empty ⟨3,false,9,44⟩ .empty) ⟨3,false,10,1⟩ .empty) ⟨3,false,10,29⟩ (.node (.node .empty ⟨3,false,10,39⟩ .empty) ⟨3,false,10,49⟩ .empty)) ⟨3,false,11,0⟩ (.node (.node (.node .empty ⟨3,false,11,14⟩ .empty) ⟨3,false,11,15⟩ .empty) ⟨3,false,11,34⟩ (.node (.node .empty ⟨3,false,11,44⟩ .empty) ⟨3,false,13,3⟩ .empty)))
def t150_174 : Tree := .node t150_162 ⟨3,false,9,34⟩ t163_174
def t175_186 : Tree := (.node (.node (.node (.node .empty ⟨3,false,13,45⟩ .empty) ⟨3,false,14,1⟩ .empty) ⟨3,false,14,29⟩ (.node (.node .empty ⟨3,false,14,39⟩ .empty) ⟨3,false,14,49⟩ .empty)) ⟨3,false,16,11⟩ (.node (.node (.node .empty ⟨3,false,16,40⟩ .empty) ⟨3,false,17,19⟩ .empty) ⟨3,false,17,48⟩ (.node (.node .empty ⟨3,false,18,16⟩ .empty) ⟨3,false,18,45⟩ .empty)))
def t187_198 : Tree := (.node (.node (.node (.node .empty ⟨3,false,19,40⟩ .empty) ⟨3,false,20,14⟩ .empty) ⟨3,false,20,15⟩ (.node (.node .empty ⟨3,false,20,34⟩ .empty) ⟨3,false,20,44⟩ .empty)) ⟨3,false,21,10⟩ (.node (.node (.node .empty ⟨3,false,21,29⟩ .empty) ⟨3,false,21,39⟩ .empty) ⟨3,false,21,49⟩ (.node (.node .empty ⟨3,false,22,2⟩ .empty) ⟨3,false,22,14⟩ .empty)))
def t175_198 : Tree := .node t175_186 ⟨3,false,19,30⟩ t187_198
def t150_198 : Tree := .node t150_174 ⟨3,false,13,35⟩ t175_198
def t100_198 : Tree := .node t100_149 ⟨3,false,3,19⟩ t150_198
def t0_198 : Tree := .node t0_99 ⟨1,true,9,18⟩ t100_198
def t199_211 : Tree := (.node (.node (.node (.node .empty ⟨3,false,22,34⟩ .empty) ⟨3,false,22,44⟩ (.node .empty ⟨3,false,23,30⟩ .empty)) ⟨3,false,23,40⟩ (.node (.node .empty ⟨3,false,24,2⟩ .empty) ⟨3,false,25,1⟩ .empty)) ⟨3,false,26,0⟩ (.node (.node (.node .empty ⟨3,false,28,3⟩ .empty) ⟨3,false,29,1⟩ .empty) ⟨3,false,30,10⟩ (.node (.node .empty ⟨3,false,30,11⟩ .empty) ⟨3,false,30,29⟩ .empty)))
def t212_223 : Tree := (.node (.node (.node (.node .empty ⟨3,false,30,49⟩ .empty) ⟨3,false,31,16⟩ .empty) ⟨3,false,31,35⟩ (.node (.node .empty ⟨3,false,31,45⟩ .empty) ⟨3,true,0,7⟩ .empty)) ⟨3,true,1,2⟩ (.node (.node (.node .empty ⟨3,true,1,24⟩ .empty) ⟨3,true,2,20⟩ .empty) ⟨3,true,3,3⟩ (.node (.node .empty ⟨3,true,3,25⟩ .empty) ⟨3,true,5,15⟩ .empty)))
def t199_223 : Tree := .node t199_211 ⟨3,false,30,39⟩ t212_223
def t224_236 : Tree := (.node (.node (.node (.node .empty ⟨3,true,6,10⟩ .empty) ⟨3,true,6,39⟩ (.node .empty ⟨3,true,7,1⟩ .empty)) ⟨3,true,7,33⟩ (.node (.node .empty ⟨3,true,7,43⟩ .empty) ⟨3,true,9,2⟩ .empty)) ⟨3,true,9,34⟩ (.node (.node (.node .empty ⟨3,true,9,44⟩ .empty) ⟨3,true,10,29⟩ .empty) ⟨3,true,10,39⟩ (.node (.node .empty ⟨3,true,10,49⟩ .empty) ⟨3,true,11,2⟩ .empty)))
def t237_248 : Tree := (.node (.node (.node (.node .empty ⟨3,true,11,33⟩ .empty) ⟨3,true,11,34⟩ .empty) ⟨3,true,11,43⟩ (.node (.node .empty ⟨3,true,11,44⟩ .empty) ⟨3,true,12,6⟩ .empty)) ⟨3,true,12,38⟩ (.node (.node (.node .empty ⟨3,true,12,48⟩ .empty) ⟨3,true,14,19⟩ .empty) ⟨3,true,14,38⟩ (.node (.node .empty ⟨3,true,14,48⟩ .empty) ⟨3,true,15,14⟩ .empty)))
def t224_248 : Tree := .node t224_236 ⟨3,true,11,15⟩ t237_248
def t199_248 : Tree := .node t199_223 ⟨3,true,5,44⟩ t224_248
def t249_261 : Tree := (.node (.node (.node (.node .empty ⟨3,true,20,15⟩ .empty) ⟨3,true,20,34⟩ (.node .empty ⟨3,true,20,44⟩ .empty)) ⟨3,true,21,29⟩ (.node (.node .empty ⟨3,true,21,39⟩ .empty) ⟨3,true,21,49⟩ .empty)) ⟨3,true,22,0⟩ (.node (.node (.node .empty ⟨3,true,22,2⟩ .empty) ⟨3,true,22,14⟩ .empty) ⟨3,true,22,15⟩ (.node (.node .empty ⟨3,true,22,33⟩ .empty) ⟨3,true,22,34⟩ .empty)))
def t262_273 : Tree := (.node (.node (.node (.node .empty ⟨3,true,22,44⟩ .empty) ⟨3,true,23,10⟩ .empty) ⟨3,true,24,2⟩ (.node (.node .empty ⟨3,true,27,6⟩ .empty) ⟨3,true,30,19⟩ .empty)) ⟨3,true,30,38⟩ (.node (.node (.node .empty ⟨3,true,30,48⟩ .empty) ⟨4,false,5,1⟩ .empty) ⟨4,false,5,20⟩ (.node (.node .empty ⟨4,false,23,0⟩ .empty) ⟨4,true,1,6⟩ .empty)))
def t249_273 : Tree := .node t249_261 ⟨3,true,22,43⟩ t262_273
def t274_286 : Tree := (.node (.node (.node (.node .empty ⟨4,true,1,28⟩ .empty) ⟨4,true,2,1⟩ (.node .empty ⟨4,true,2,20⟩ .empty)) ⟨4,true,6,10⟩ (.node (.node .empty ⟨4,true,6,39⟩ .empty) ⟨4,true,6,49⟩ .empty)) ⟨4,true,8,0⟩ (.node (.node (.node .empty ⟨4,true,8,30⟩ .empty) ⟨4,true,8,40⟩ .empty) ⟨4,true,9,2⟩ (.node (.node .empty ⟨4,true,9,34⟩ .empty) ⟨4,true,9,44⟩ .empty)))
def t287_298 : Tree := (.node (.node (.node (.node .empty ⟨4,true,10,29⟩ .empty) ⟨4,true,10,39⟩ .empty) ⟨4,true,10,49⟩ (.node (.node .empty ⟨4,true,13,3⟩ .empty) ⟨4,true,13,35⟩ .empty)) ⟨4,true,13,45⟩ (.node (.node (.node .empty ⟨4,true,16,11⟩ .empty) ⟨4,true,16,40⟩ .empty) ⟨4,true,17,19⟩ (.node (.node .empty ⟨4,true,17,48⟩ .empty) ⟨4,true,19,1⟩ .empty)))
def t274_298 : Tree := .node t274_286 ⟨4,true,10,1⟩ t287_298
def t249_298 : Tree := .node t249_273 ⟨4,true,1,21⟩ t274_298
def t199_298 : Tree := .node t199_248 ⟨3,true,15,43⟩ t249_298
def t299_311 : Tree := (.node (.node (.node (.node .empty ⟨4,true,19,29⟩ .empty) ⟨4,true,19,30⟩ (.node .empty ⟨4,true,19,39⟩ .empty)) ⟨4,true,19,40⟩ (.node (.node .empty ⟨4,true,19,49⟩ .empty) ⟨4,true,20,14⟩ .empty)) ⟨4,true,20,15⟩ (.node (.node (.node .empty ⟨4,true,20,34⟩ .empty) ⟨4,true,20,44⟩ .empty) ⟨4,true,21,10⟩ (.node (.node .empty ⟨4,true,21,29⟩ .empty) ⟨4,true,21,39⟩ .empty)))
def t312_323 : Tree := (.node (.node (.node (.node .empty ⟨4,true,23,1⟩ .empty) ⟨4,true,23,10⟩ .empty) ⟨4,true,23,11⟩ (.node (.node .empty ⟨4,true,23,29⟩ .empty) ⟨4,true,23,30⟩ .empty)) ⟨4,true,23,39⟩ (.node (.node (.node .empty ⟨4,true,23,40⟩ .empty) ⟨4,true,23,49⟩ .empty) ⟨4,true,24,2⟩ (.node (.node .empty ⟨4,true,25,1⟩ .empty) ⟨4,true,28,3⟩ .empty)))
def t299_323 : Tree := .node t299_311 ⟨4,true,21,49⟩ t312_323
def t324_336 : Tree := (.node (.node (.node (.node .empty ⟨4,true,31,35⟩ .empty) ⟨4,true,31,45⟩ (.node .empty ⟨5,false,0,22⟩ .empty)) ⟨5,false,7,0⟩ (.node (.node .empty ⟨5,false,7,31⟩ .empty) ⟨5,false,7,41⟩ .empty)) ⟨5,false,11,31⟩ (.node (.node (.node .empty ⟨5,false,11,41⟩ .empty) ⟨5,false,12,4⟩ .empty) ⟨5,false,12,36⟩ (.node (.node .empty ⟨5,false,12,46⟩ .empty) ⟨5,false,14,17⟩ .empty)))
def t337_348 : Tree := (.node (.node (.node (.node .empty ⟨5,false,14,46⟩ .empty) ⟨5,false,15,12⟩ .empty) ⟨5,false,15,41⟩ (.node (.node .empty ⟨5,false,22,31⟩ .empty) ⟨5,false,22,41⟩ .empty)) ⟨5,false,27,4⟩ (.node (.node (.node .empty ⟨5,false,30,17⟩ .empty) ⟨5,false,30,36⟩ .empty) ⟨5,false,30,46⟩ (.node (.node .empty ⟨5,true,0,8⟩ .empty) ⟨5,true,0,22⟩ .empty)))
def t324_348 : Tree := .node t324_336 ⟨5,false,14,36⟩ t337_348
def t299_348 : Tree := .node t299_323 ⟨4,true,31,16⟩ t324_348
def t349_361 : Tree := (.node (.node (.node (.node .empty ⟨5,true,1,25⟩ .empty) ⟨5,true,2,21⟩ (.node .empty ⟨5,true,5,16⟩ .empty)) ⟨5,true,5,45⟩ (.node (.node .empty ⟨5,true,6,11⟩ .empty) ⟨5,true,6,40⟩ .empty)) ⟨5,true,7,0⟩ (.node (.node (.node .empty ⟨5,true,7,16⟩ .empty) ⟨5,true,7,31⟩ .empty) ⟨5,true,7,41⟩ (.node (.node .empty ⟨5,true,7,45⟩ .empty) ⟨5,true,9,3⟩ .empty)))
def t362_373 : Tree := (.node (.node (.node (.node .empty ⟨5,true,9,45⟩ .empty) ⟨5,true,10,30⟩ .empty) ⟨5,true,10,40⟩ (.node (.node .empty ⟨5,true,11,3⟩ .empty) ⟨5,true,11,16⟩ .empty)) ⟨5,true,11,31⟩ (.node (.node (.node .empty ⟨5,true,11,35⟩ .empty) ⟨5,true,11,41⟩ .empty) ⟨5,true,11,45⟩ (.node (.node .empty ⟨5,true,12,4⟩ .empty) ⟨5,true,12,36⟩ .empty)))
def t349_373 : Tree := .node t349_361 ⟨5,true,9,35⟩ t362_373
def t374_385 : Tree := (.node (.node (.node (.node .empty ⟨5,true,14,17⟩ .empty) ⟨5,true,14,36⟩ .empty) ⟨5,true,14,46⟩ (.node (.node .empty ⟨5,true,15,12⟩ .empty) ⟨5,true,15,41⟩ .empty)) ⟨5,true,20,16⟩ (.node (.node (.node .empty ⟨5,true,20,35⟩ .empty) ⟨5,true,20,45⟩ .empty) ⟨5,true,21,30⟩ (.node (.node .empty ⟨5,true,21,40⟩ .empty) ⟨5,true,22,3⟩ .empty)))
def t386_397 : Tree := (.node (.node (.node (.node .empty ⟨5,true,22,16⟩ .empty) ⟨5,true,22,31⟩ .empty) ⟨5,true,22,35⟩ (.node (.node .empty ⟨5,true,22,41⟩ .empty) ⟨5,true,22,45⟩ .empty)) ⟨5,true,23,11⟩ (.node (.node (.node .empty ⟨5,true,24,3⟩ .empty) ⟨5,true,27,4⟩ .empty) ⟨5,true,30,17⟩ (.node (.node .empty ⟨5,true,30,36⟩ .empty) ⟨5,true,30,46⟩ .empty)))
def t374_397 : Tree := .node t374_385 ⟨5,true,22,12⟩ t386_397
def t349_397 : Tree := .node t349_373 ⟨5,true,12,46⟩ t374_397
def t299_397 : Tree := .node t299_348 ⟨5,true,1,3⟩ t349_397
def t199_397 : Tree := .node t199_298 ⟨4,true,19,10⟩ t299_397
def t0_397 : Tree := .node t0_198 ⟨3,false,22,15⟩ t199_397
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 17, 15, 5, 0, 0, 12, 6, 7, 9, 0, 8, 0, 0, 14, 10, 11, 20, 0, 19, 0, 13, 0, 0, 0, 31, 0, 16, 0, 0, 18, 0, 0, 0, 0, 0, 30, 21, 22, 20, 27, 23, 0, 24, 29, 25, 26, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 31, 0, 0],#[0, 1, 3, 2, 11, 10, 4, 6, 5, 0, 0, 0, 8, 7, 0, 0, 9, 0, 0, 0, 16, 15, 12, 14, 13, 0, 0, 0, 30, 29, 30, 49, 17, 19, 18, 0, 0, 0, 21, 20, 25, 24, 22, 7, 23, 0, 0, 0, 0, 0, 26, 28, 27, 0, 0, 0, 8, 7, 35, 34, 31, 33, 32, 0, 0, 0, 0, 0, 40, 39, 36, 38, 37, 0, 0, 0, 0, 0, 45, 44, 41, 43, 42, 0, 0, 0, 0, 0, 40, 39, 46, 48, 47, 0, 0, 0, 21, 20, 45, 44],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,3)],[(true,5)],[(false,6)],[(true,7)],[(true,6)],[(true,9)],[(false,10)],[(false,5)],[(true,12)],[(false,9)],[(false,3)],[(true,15)],[(true,2)],[(false,17)],[(true,11)],[(true,10),(true,21)],[(true,20)],[(false,21)],[(true,22)],[(true,23)],[(true,24)],[(false,25)],[(false,22)],[(true,27)],[(false,24)],[(false,20)],[(true,14),(true,30)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(false,4)],[(true,3)],[(true,6),(true,21),(true,28)],[(false,6),(false,28)],[(false,8)],[(true,2)],[(false,2)],[(false,11)],[(false,12)],[(true,11)],[(true,10)],[(false,10)],[(false,16)],[(false,17)],[(true,16)],[(true,19),(true,48)],[(false,19),(false,48)],[(false,21)],[(false,22)],[(true,20)],[(false,20)],[(false,25)],[(false,26)],[(true,25)],[(true,14)],[(false,14),(false,15)],[(false,30)],[(false,31)],[(true,30)],[(true,29)],[(false,29)],[(false,35)],[(false,36)],[(true,35)],[(true,34),(true,44)],[(false,34),(false,44)],[(false,40)],[(false,41)],[(true,40)],[(true,39),(true,49)],[(false,39),(false,49)],[(false,45)],[(false,46)],[(true,45)],[(true,15)]],
  t0_397⟩
theorem check0_12 : t0_12.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check13_24 : t13_24.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node12 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,6,46⟩ = true := by decide
theorem check0_24 : t0_24.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node12 check0_12 check13_24
theorem check25_37 : t25_37.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check38_49 : t38_49.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node37 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,3,46⟩ = true := by decide
theorem check25_49 : t25_49.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node37 check25_37 check38_49
theorem node24 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,20,47⟩ = true := by decide
theorem check0_49 : t0_49.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node24 check0_24 check25_49
theorem check50_62 : t50_62.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check63_74 : t63_74.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node62 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,5,12⟩ = true := by decide
theorem check50_74 : t50_74.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node62 check50_62 check63_74
theorem check75_87 : t75_87.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check88_99 : t88_99.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node87 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,24,0⟩ = true := by decide
theorem check75_99 : t75_99.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node87 check75_87 check88_99
theorem node74 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,10,46⟩ = true := by decide
theorem check50_99 : t50_99.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node74 check50_74 check75_99
theorem node49 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,20,41⟩ = true := by decide
theorem check0_99 : t0_99.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node49 check0_49 check50_99
theorem check100_112 : t100_112.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check113_124 : t113_124.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node112 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,2,0⟩ = true := by decide
theorem check100_124 : t100_124.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node112 check100_112 check113_124
theorem check125_137 : t125_137.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check138_149 : t138_149.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node137 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,21,30⟩ = true := by decide
theorem check125_149 : t125_149.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node137 check125_137 check138_149
theorem node124 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,10,39⟩ = true := by decide
theorem check100_149 : t100_149.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node124 check100_124 check125_149
theorem check150_162 : t150_162.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check163_174 : t163_174.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node162 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,9,34⟩ = true := by decide
theorem check150_174 : t150_174.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node162 check150_162 check163_174
theorem check175_186 : t175_186.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check187_198 : t187_198.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node186 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,19,30⟩ = true := by decide
theorem check175_198 : t175_198.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node186 check175_186 check187_198
theorem node174 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,13,35⟩ = true := by decide
theorem check150_198 : t150_198.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node174 check150_174 check175_198
theorem node149 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,3,19⟩ = true := by decide
theorem check100_198 : t100_198.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node149 check100_149 check150_198
theorem node99 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,9,18⟩ = true := by decide
theorem check0_198 : t0_198.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node99 check0_99 check100_198
theorem check199_211 : t199_211.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check212_223 : t212_223.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node211 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,30,39⟩ = true := by decide
theorem check199_223 : t199_223.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node211 check199_211 check212_223
theorem check224_236 : t224_236.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check237_248 : t237_248.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node236 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,11,15⟩ = true := by decide
theorem check224_248 : t224_248.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node236 check224_236 check237_248
theorem node223 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,5,44⟩ = true := by decide
theorem check199_248 : t199_248.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node223 check199_223 check224_248
theorem check249_261 : t249_261.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check262_273 : t262_273.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node261 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,22,43⟩ = true := by decide
theorem check249_273 : t249_273.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node261 check249_261 check262_273
theorem check274_286 : t274_286.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check287_298 : t287_298.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node286 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,10,1⟩ = true := by decide
theorem check274_298 : t274_298.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node286 check274_286 check287_298
theorem node273 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,1,21⟩ = true := by decide
theorem check249_298 : t249_298.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node273 check249_273 check274_298
theorem node248 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,15,43⟩ = true := by decide
theorem check199_298 : t199_298.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node248 check199_248 check249_298
theorem check299_311 : t299_311.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check312_323 : t312_323.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node311 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,21,49⟩ = true := by decide
theorem check299_323 : t299_323.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node311 check299_311 check312_323
theorem check324_336 : t324_336.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check337_348 : t337_348.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node336 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,14,36⟩ = true := by decide
theorem check324_348 : t324_348.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node336 check324_336 check337_348
theorem node323 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,31,16⟩ = true := by decide
theorem check299_348 : t299_348.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node323 check299_323 check324_348
theorem check349_361 : t349_361.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check362_373 : t362_373.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node361 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,9,35⟩ = true := by decide
theorem check349_373 : t349_373.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node361 check349_361 check362_373
theorem check374_385 : t374_385.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check386_397 : t386_397.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node385 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,22,12⟩ = true := by decide
theorem check374_397 : t374_397.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node385 check374_385 check386_397
theorem node373 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,12,46⟩ = true := by decide
theorem check349_397 : t349_397.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node373 check349_373 check374_397
theorem node348 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,1,3⟩ = true := by decide
theorem check299_397 : t299_397.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node348 check299_348 check349_397
theorem node298 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,19,10⟩ = true := by decide
theorem check199_397 : t199_397.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node298 check199_298 check299_397
theorem node198 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,22,15⟩ = true := by decide
theorem check0_397 : t0_397.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node198 check0_198 check199_397
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_397
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M010
