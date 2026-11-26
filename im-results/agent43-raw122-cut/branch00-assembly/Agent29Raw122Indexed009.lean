import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M009
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
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_9 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,9⟩ .empty) ⟨0,false,0,18⟩ (.node .empty ⟨0,false,3,5⟩ .empty)) ⟨0,false,5,0⟩ (.node (.node (.node .empty ⟨0,false,7,37⟩ .empty) ⟨0,false,7,57⟩ .empty) ⟨0,false,7,72⟩ (.node .empty ⟨0,false,8,52⟩ .empty)))
def t10_18 : Tree := (.node (.node (.node (.node .empty ⟨0,false,8,67⟩ .empty) ⟨0,false,8,77⟩ .empty) ⟨0,false,16,32⟩ (.node .empty ⟨0,false,16,41⟩ .empty)) ⟨0,false,16,52⟩ (.node (.node .empty ⟨0,false,16,56⟩ .empty) ⟨0,false,16,57⟩ (.node .empty ⟨0,false,16,62⟩ .empty)))
def t0_18 : Tree := .node t0_9 ⟨0,false,8,57⟩ t10_18
def t19_28 : Tree := (.node (.node (.node (.node .empty ⟨0,false,16,76⟩ .empty) ⟨0,false,17,27⟩ .empty) ⟨0,false,17,32⟩ (.node .empty ⟨0,false,17,42⟩ .empty)) ⟨0,false,17,52⟩ (.node (.node (.node .empty ⟨0,false,17,57⟩ .empty) ⟨0,false,17,67⟩ .empty) ⟨0,false,17,77⟩ (.node .empty ⟨0,false,18,13⟩ .empty)))
def t29_37 : Tree := (.node (.node (.node (.node .empty ⟨0,false,19,5⟩ .empty) ⟨0,false,19,13⟩ .empty) ⟨0,false,20,5⟩ (.node .empty ⟨0,false,21,0⟩ .empty)) ⟨0,false,33,13⟩ (.node (.node .empty ⟨0,false,33,27⟩ .empty) ⟨0,false,33,31⟩ (.node .empty ⟨0,false,33,32⟩ .empty)))
def t19_37 : Tree := .node t19_28 ⟨0,false,18,27⟩ t29_37
def t0_37 : Tree := .node t0_18 ⟨0,false,16,72⟩ t19_37
def t38_47 : Tree := (.node (.node (.node (.node .empty ⟨0,false,33,51⟩ .empty) ⟨0,false,33,52⟩ .empty) ⟨0,false,33,56⟩ (.node .empty ⟨0,false,33,57⟩ .empty)) ⟨0,false,33,62⟩ (.node (.node (.node .empty ⟨0,false,33,66⟩ .empty) ⟨0,false,33,72⟩ .empty) ⟨0,false,33,76⟩ (.node .empty ⟨0,false,36,5⟩ .empty)))
def t48_56 : Tree := (.node (.node (.node (.node .empty ⟨0,false,36,32⟩ .empty) ⟨0,false,36,42⟩ .empty) ⟨0,false,36,52⟩ (.node .empty ⟨0,false,36,57⟩ .empty)) ⟨0,false,36,67⟩ (.node (.node .empty ⟨0,false,36,77⟩ .empty) ⟨0,false,37,12⟩ (.node .empty ⟨0,false,37,13⟩ .empty)))
def t38_56 : Tree := .node t38_47 ⟨0,false,36,27⟩ t48_56
def t57_66 : Tree := (.node (.node (.node (.node .empty ⟨0,false,37,31⟩ .empty) ⟨0,false,37,32⟩ .empty) ⟨0,false,37,37⟩ (.node .empty ⟨0,false,37,41⟩ .empty)) ⟨0,false,37,51⟩ (.node (.node (.node .empty ⟨0,false,37,52⟩ .empty) ⟨0,false,37,56⟩ .empty) ⟨0,false,37,57⟩ (.node .empty ⟨0,false,37,62⟩ .empty)))
def t67_75 : Tree := (.node (.node (.node (.node .empty ⟨0,false,37,72⟩ .empty) ⟨0,false,37,76⟩ .empty) ⟨0,false,44,5⟩ (.node .empty ⟨0,false,44,27⟩ .empty)) ⟨0,false,44,32⟩ (.node (.node .empty ⟨0,false,44,42⟩ .empty) ⟨0,false,44,52⟩ (.node .empty ⟨0,false,44,57⟩ .empty)))
def t57_75 : Tree := .node t57_66 ⟨0,false,37,66⟩ t67_75
def t38_75 : Tree := .node t38_56 ⟨0,false,37,26⟩ t57_75
def t0_75 : Tree := .node t0_37 ⟨0,false,33,37⟩ t38_75
def t76_85 : Tree := (.node (.node (.node (.node .empty ⟨0,false,44,77⟩ .empty) ⟨0,false,45,0⟩ .empty) ⟨0,false,45,4⟩ (.node .empty ⟨0,false,45,12⟩ .empty)) ⟨0,false,45,13⟩ (.node (.node (.node .empty ⟨0,false,45,26⟩ .empty) ⟨0,false,45,27⟩ .empty) ⟨0,false,45,31⟩ (.node .empty ⟨0,false,45,32⟩ .empty)))
def t86_94 : Tree := (.node (.node (.node (.node .empty ⟨0,false,45,41⟩ .empty) ⟨0,false,45,51⟩ .empty) ⟨0,false,45,52⟩ (.node .empty ⟨0,false,45,56⟩ .empty)) ⟨0,false,45,57⟩ (.node (.node .empty ⟨0,false,45,62⟩ .empty) ⟨0,false,45,66⟩ (.node .empty ⟨0,false,45,72⟩ .empty)))
def t76_94 : Tree := .node t76_85 ⟨0,false,45,37⟩ t86_94
def t95_104 : Tree := (.node (.node (.node (.node .empty ⟨0,false,46,13⟩ .empty) ⟨0,false,46,27⟩ .empty) ⟨0,false,47,5⟩ (.node .empty ⟨0,false,47,13⟩ .empty)) ⟨0,false,48,0⟩ (.node (.node (.node .empty ⟨0,false,48,5⟩ .empty) ⟨0,true,0,4⟩ .empty) ⟨0,true,0,21⟩ (.node .empty ⟨0,true,1,17⟩ .empty)))
def t105_113 : Tree := (.node (.node (.node (.node .empty ⟨0,true,3,46⟩ .empty) ⟨0,true,5,4⟩ .empty) ⟨0,true,6,0⟩ (.node .empty ⟨0,true,6,14⟩ .empty)) ⟨0,true,6,48⟩ (.node (.node .empty ⟨0,true,7,41⟩ .empty) ⟨0,true,7,56⟩ (.node .empty ⟨0,true,7,76⟩ .empty)))
def t95_113 : Tree := .node t95_104 ⟨0,true,3,12⟩ t105_113
def t76_113 : Tree := .node t76_94 ⟨0,false,45,76⟩ t95_113
def t114_123 : Tree := (.node (.node (.node (.node .empty ⟨0,true,8,56⟩ .empty) ⟨0,true,8,71⟩ .empty) ⟨0,true,16,51⟩ (.node .empty ⟨0,true,16,56⟩ .empty)) ⟨0,true,16,66⟩ (.node (.node (.node .empty ⟨0,true,16,76⟩ .empty) ⟨0,true,17,1⟩ .empty) ⟨0,true,17,31⟩ (.node .empty ⟨0,true,17,40⟩ .empty)))
def t124_132 : Tree := (.node (.node (.node (.node .empty ⟨0,true,17,55⟩ .empty) ⟨0,true,17,56⟩ .empty) ⟨0,true,17,61⟩ (.node .empty ⟨0,true,17,71⟩ .empty)) ⟨0,true,17,75⟩ (.node (.node .empty ⟨0,true,18,26⟩ .empty) ⟨0,true,18,31⟩ (.node .empty ⟨0,true,19,12⟩ .empty)))
def t114_132 : Tree := .node t114_123 ⟨0,true,17,51⟩ t124_132
def t133_141 : Tree := (.node (.node (.node (.node .empty ⟨0,true,20,4⟩ .empty) ⟨0,true,20,12⟩ .empty) ⟨0,true,21,4⟩ (.node .empty ⟨0,true,33,26⟩ .empty)) ⟨0,true,33,31⟩ (.node (.node .empty ⟨0,true,33,41⟩ .empty) ⟨0,true,33,51⟩ (.node .empty ⟨0,true,33,56⟩ .empty)))
def t142_150 : Tree := (.node (.node (.node (.node .empty ⟨0,true,33,76⟩ .empty) ⟨0,true,36,12⟩ .empty) ⟨0,true,36,31⟩ (.node .empty ⟨0,true,36,36⟩ .empty)) ⟨0,true,36,51⟩ (.node (.node .empty ⟨0,true,36,56⟩ .empty) ⟨0,true,36,61⟩ (.node .empty ⟨0,true,36,71⟩ .empty)))
def t133_150 : Tree := .node t133_141 ⟨0,true,33,66⟩ t142_150
def t114_150 : Tree := .node t114_132 ⟨0,true,19,26⟩ t133_150
def t76_150 : Tree := .node t76_113 ⟨0,true,8,36⟩ t114_150
def t0_150 : Tree := .node t0_75 ⟨0,false,44,67⟩ t76_150
def t151_160 : Tree := (.node (.node (.node (.node .empty ⟨0,true,37,26⟩ .empty) ⟨0,true,37,31⟩ .empty) ⟨0,true,37,41⟩ (.node .empty ⟨0,true,37,51⟩ .empty)) ⟨0,true,37,56⟩ (.node (.node (.node .empty ⟨0,true,37,66⟩ .empty) ⟨0,true,37,76⟩ .empty) ⟨0,true,44,12⟩ (.node .empty ⟨0,true,44,31⟩ .empty)))
def t161_169 : Tree := (.node (.node (.node (.node .empty ⟨0,true,44,51⟩ .empty) ⟨0,true,44,56⟩ .empty) ⟨0,true,44,61⟩ (.node .empty ⟨0,true,44,71⟩ .empty)) ⟨0,true,45,4⟩ (.node (.node .empty ⟨0,true,45,26⟩ .empty) ⟨0,true,45,31⟩ (.node .empty ⟨0,true,45,41⟩ .empty)))
def t151_169 : Tree := .node t151_160 ⟨0,true,44,36⟩ t161_169
def t170_179 : Tree := (.node (.node (.node (.node .empty ⟨0,true,45,56⟩ .empty) ⟨0,true,45,66⟩ .empty) ⟨0,true,45,76⟩ (.node .empty ⟨0,true,46,26⟩ .empty)) ⟨0,true,46,31⟩ (.node (.node (.node .empty ⟨0,true,47,12⟩ .empty) ⟨0,true,47,26⟩ .empty) ⟨0,true,48,4⟩ (.node .empty ⟨0,true,48,12⟩ .empty)))
def t180_188 : Tree := (.node (.node (.node (.node .empty ⟨1,false,0,5⟩ .empty) ⟨1,false,0,22⟩ .empty) ⟨1,false,1,0⟩ (.node .empty ⟨1,false,1,8⟩ .empty)) ⟨1,false,1,17⟩ (.node (.node .empty ⟨1,false,2,13⟩ .empty) ⟨1,false,2,47⟩ (.node .empty ⟨1,false,5,4⟩ .empty)))
def t170_188 : Tree := .node t170_179 ⟨0,true,49,4⟩ t180_188
def t151_188 : Tree := .node t151_169 ⟨0,true,45,51⟩ t170_188
def t189_198 : Tree := (.node (.node (.node (.node .empty ⟨1,false,5,57⟩ .empty) ⟨1,false,5,77⟩ .empty) ⟨1,false,6,0⟩ (.node .empty ⟨1,false,8,36⟩ .empty)) ⟨1,false,8,56⟩ (.node (.node (.node .empty ⟨1,false,8,71⟩ .empty) ⟨1,false,16,27⟩ .empty) ⟨1,false,16,32⟩ (.node .empty ⟨1,false,16,51⟩ .empty)))
def t199_207 : Tree := (.node (.node (.node (.node .empty ⟨1,false,16,66⟩ .empty) ⟨1,false,16,76⟩ .empty) ⟨1,false,17,31⟩ (.node .empty ⟨1,false,17,40⟩ .empty)) ⟨1,false,17,51⟩ (.node (.node .empty ⟨1,false,17,55⟩ .empty) ⟨1,false,17,56⟩ (.node .empty ⟨1,false,17,61⟩ .empty)))
def t189_207 : Tree := .node t189_198 ⟨1,false,16,56⟩ t199_207
def t208_216 : Tree := (.node (.node (.node (.node .empty ⟨1,false,17,75⟩ .empty) ⟨1,false,19,12⟩ .empty) ⟨1,false,19,26⟩ (.node .empty ⟨1,false,20,4⟩ .empty)) ⟨1,false,20,12⟩ (.node (.node .empty ⟨1,false,21,4⟩ .empty) ⟨1,false,22,0⟩ (.node .empty ⟨1,false,33,26⟩ .empty)))
def t217_225 : Tree := (.node (.node (.node (.node .empty ⟨1,false,33,41⟩ .empty) ⟨1,false,33,51⟩ .empty) ⟨1,false,33,56⟩ (.node .empty ⟨1,false,33,66⟩ .empty)) ⟨1,false,33,76⟩ (.node (.node .empty ⟨1,false,36,12⟩ .empty) ⟨1,false,36,26⟩ (.node .empty ⟨1,false,36,30⟩ .empty)))
def t208_225 : Tree := .node t208_216 ⟨1,false,33,31⟩ t217_225
def t189_225 : Tree := .node t189_207 ⟨1,false,17,71⟩ t208_225
def t151_225 : Tree := .node t151_188 ⟨1,false,5,42⟩ t189_225
def t226_235 : Tree := (.node (.node (.node (.node .empty ⟨1,false,36,36⟩ .empty) ⟨1,false,36,50⟩ .empty) ⟨1,false,36,51⟩ (.node .empty ⟨1,false,36,55⟩ .empty)) ⟨1,false,36,56⟩ (.node (.node (.node .empty ⟨1,false,36,61⟩ .empty) ⟨1,false,36,65⟩ .empty) ⟨1,false,36,71⟩ (.node .empty ⟨1,false,36,75⟩ .empty)))
def t236_244 : Tree := (.node (.node (.node (.node .empty ⟨1,false,37,26⟩ .empty) ⟨1,false,37,31⟩ .empty) ⟨1,false,37,41⟩ (.node .empty ⟨1,false,37,51⟩ .empty)) ⟨1,false,37,56⟩ (.node (.node .empty ⟨1,false,37,66⟩ .empty) ⟨1,false,37,76⟩ (.node .empty ⟨1,false,44,0⟩ .empty)))
def t226_244 : Tree := .node t226_235 ⟨1,false,37,4⟩ t236_244
def t245_254 : Tree := (.node (.node (.node (.node .empty ⟨1,false,44,11⟩ .empty) ⟨1,false,44,12⟩ .empty) ⟨1,false,44,25⟩ (.node .empty ⟨1,false,44,26⟩ .empty)) ⟨1,false,44,30⟩ (.node (.node (.node .empty ⟨1,false,44,31⟩ .empty) ⟨1,false,44,36⟩ .empty) ⟨1,false,44,40⟩ (.node .empty ⟨1,false,44,50⟩ .empty)))
def t255_263 : Tree := (.node (.node (.node (.node .empty ⟨1,false,44,55⟩ .empty) ⟨1,false,44,56⟩ .empty) ⟨1,false,44,61⟩ (.node .empty ⟨1,false,44,65⟩ .empty)) ⟨1,false,44,71⟩ (.node (.node .empty ⟨1,false,44,75⟩ .empty) ⟨1,false,45,4⟩ (.node .empty ⟨1,false,45,26⟩ .empty)))
def t245_263 : Tree := .node t245_254 ⟨1,false,44,51⟩ t255_263
def t226_263 : Tree := .node t226_244 ⟨1,false,44,3⟩ t245_263
def t264_273 : Tree := (.node (.node (.node (.node .empty ⟨1,false,45,31⟩ .empty) ⟨1,false,45,32⟩ .empty) ⟨1,false,45,41⟩ (.node .empty ⟨1,false,45,51⟩ .empty)) ⟨1,false,45,56⟩ (.node (.node (.node .empty ⟨1,false,45,66⟩ .empty) ⟨1,false,45,76⟩ .empty) ⟨1,false,47,12⟩ (.node .empty ⟨1,false,47,26⟩ .empty)))
def t274_282 : Tree := (.node (.node (.node (.node .empty ⟨1,false,48,12⟩ .empty) ⟨1,false,49,0⟩ .empty) ⟨1,false,49,4⟩ (.node .empty ⟨1,true,0,18⟩ .empty)) ⟨1,true,3,5⟩ (.node (.node .empty ⟨1,true,5,0⟩ .empty) ⟨1,true,5,16⟩ (.node .empty ⟨1,true,7,37⟩ .empty)))
def t264_282 : Tree := .node t264_273 ⟨1,false,48,4⟩ t274_282
def t283_291 : Tree := (.node (.node (.node (.node .empty ⟨1,true,7,72⟩ .empty) ⟨1,true,8,52⟩ .empty) ⟨1,true,8,57⟩ (.node .empty ⟨1,true,8,67⟩ .empty)) ⟨1,true,8,77⟩ (.node (.node .empty ⟨1,true,16,3⟩ .empty) ⟨1,true,16,32⟩ (.node .empty ⟨1,true,16,41⟩ .empty)))
def t292_300 : Tree := (.node (.node (.node (.node .empty ⟨1,true,16,56⟩ .empty) ⟨1,true,16,57⟩ .empty) ⟨1,true,16,62⟩ (.node .empty ⟨1,true,16,72⟩ .empty)) ⟨1,true,16,76⟩ (.node (.node .empty ⟨1,true,17,27⟩ .empty) ⟨1,true,17,32⟩ (.node .empty ⟨1,true,17,42⟩ .empty)))
def t283_300 : Tree := .node t283_291 ⟨1,true,16,52⟩ t292_300
def t264_300 : Tree := .node t264_282 ⟨1,true,7,57⟩ t283_300
def t226_300 : Tree := .node t226_263 ⟨1,false,45,27⟩ t264_300
def t151_300 : Tree := .node t151_225 ⟨1,false,36,31⟩ t226_300
def t0_300 : Tree := .node t0_150 ⟨0,true,37,4⟩ t151_300
def t301_310 : Tree := (.node (.node (.node (.node .empty ⟨1,true,17,57⟩ .empty) ⟨1,true,17,67⟩ .empty) ⟨1,true,17,77⟩ (.node .empty ⟨1,true,18,13⟩ .empty)) ⟨1,true,18,27⟩ (.node (.node (.node .empty ⟨1,true,19,5⟩ .empty) ⟨1,true,19,13⟩ .empty) ⟨1,true,20,5⟩ (.node .empty ⟨1,true,33,13⟩ .empty)))
def t311_319 : Tree := (.node (.node (.node (.node .empty ⟨1,true,33,37⟩ .empty) ⟨1,true,33,52⟩ .empty) ⟨1,true,33,57⟩ (.node .empty ⟨1,true,33,62⟩ .empty)) ⟨1,true,33,72⟩ (.node (.node .empty ⟨1,true,36,5⟩ .empty) ⟨1,true,36,27⟩ (.node .empty ⟨1,true,36,32⟩ .empty)))
def t301_319 : Tree := .node t301_310 ⟨1,true,33,32⟩ t311_319
def t320_329 : Tree := (.node (.node (.node (.node .empty ⟨1,true,36,52⟩ .empty) ⟨1,true,36,57⟩ .empty) ⟨1,true,36,67⟩ (.node .empty ⟨1,true,36,77⟩ .empty)) ⟨1,true,37,13⟩ (.node (.node (.node .empty ⟨1,true,37,32⟩ .empty) ⟨1,true,37,37⟩ .empty) ⟨1,true,37,52⟩ (.node .empty ⟨1,true,37,57⟩ .empty)))
def t330_338 : Tree := (.node (.node (.node (.node .empty ⟨1,true,37,72⟩ .empty) ⟨1,true,44,5⟩ .empty) ⟨1,true,44,27⟩ (.node .empty ⟨1,true,44,32⟩ .empty)) ⟨1,true,44,42⟩ (.node (.node .empty ⟨1,true,44,52⟩ .empty) ⟨1,true,44,57⟩ (.node .empty ⟨1,true,44,67⟩ .empty)))
def t320_338 : Tree := .node t320_329 ⟨1,true,37,62⟩ t330_338
def t301_338 : Tree := .node t301_319 ⟨1,true,36,42⟩ t320_338
def t339_348 : Tree := (.node (.node (.node (.node .empty ⟨1,true,45,13⟩ .empty) ⟨1,true,45,32⟩ .empty) ⟨1,true,45,37⟩ (.node .empty ⟨1,true,45,52⟩ .empty)) ⟨1,true,45,57⟩ (.node (.node (.node .empty ⟨1,true,45,62⟩ .empty) ⟨1,true,45,72⟩ .empty) ⟨1,true,46,13⟩ (.node .empty ⟨1,true,46,27⟩ .empty)))
def t349_357 : Tree := (.node (.node (.node (.node .empty ⟨1,true,47,13⟩ .empty) ⟨1,true,48,5⟩ .empty) ⟨2,false,1,4⟩ (.node .empty ⟨2,false,1,21⟩ .empty)) ⟨2,false,2,0⟩ (.node (.node .empty ⟨2,false,2,6⟩ .empty) ⟨2,false,2,16⟩ (.node .empty ⟨2,false,2,23⟩ .empty)))
def t339_357 : Tree := .node t339_348 ⟨1,true,47,5⟩ t349_357
def t358_367 : Tree := (.node (.node (.node (.node .empty ⟨2,false,6,41⟩ .empty) ⟨2,false,6,56⟩ .empty) ⟨2,false,6,76⟩ (.node .empty ⟨2,false,9,0⟩ .empty)) ⟨2,false,14,12⟩ (.node (.node (.node .empty ⟨2,false,14,46⟩ .empty) ⟨2,false,16,35⟩ .empty) ⟨2,false,16,55⟩ (.node .empty ⟨2,false,16,70⟩ .empty)))
def t368_376 : Tree := (.node (.node (.node (.node .empty ⟨2,false,17,31⟩ .empty) ⟨2,false,17,50⟩ .empty) ⟨2,false,17,55⟩ (.node .empty ⟨2,false,17,65⟩ .empty)) ⟨2,false,17,75⟩ (.node (.node .empty ⟨2,false,20,11⟩ .empty) ⟨2,false,20,25⟩ (.node .empty ⟨2,false,21,3⟩ .empty)))
def t358_376 : Tree := .node t358_367 ⟨2,false,17,26⟩ t368_376
def t339_376 : Tree := .node t339_357 ⟨2,false,6,3⟩ t358_376
def t301_376 : Tree := .node t301_338 ⟨1,true,44,77⟩ t339_376
def t377_386 : Tree := (.node (.node (.node (.node .empty ⟨2,false,22,0⟩ .empty) ⟨2,false,22,3⟩ .empty) ⟨2,false,33,30⟩ (.node .empty ⟨2,false,33,34⟩ .empty)) ⟨2,false,33,49⟩ (.node (.node (.node .empty ⟨2,false,33,50⟩ .empty) ⟨2,false,33,54⟩ .empty) ⟨2,false,33,55⟩ (.node .empty ⟨2,false,33,60⟩ .empty)))
def t387_395 : Tree := (.node (.node (.node (.node .empty ⟨2,false,33,70⟩ .empty) ⟨2,false,36,25⟩ .empty) ⟨2,false,36,30⟩ (.node .empty ⟨2,false,36,40⟩ .empty)) ⟨2,false,36,50⟩ (.node (.node .empty ⟨2,false,36,55⟩ .empty) ⟨2,false,36,65⟩ (.node .empty ⟨2,false,36,75⟩ .empty)))
def t377_395 : Tree := .node t377_386 ⟨2,false,33,69⟩ t387_395
def t396_405 : Tree := (.node (.node (.node (.node .empty ⟨2,false,37,24⟩ .empty) ⟨2,false,37,25⟩ .empty) ⟨2,false,37,29⟩ (.node .empty ⟨2,false,37,30⟩ .empty)) ⟨2,false,37,35⟩ (.node (.node (.node .empty ⟨2,false,37,49⟩ .empty) ⟨2,false,37,50⟩ .empty) ⟨2,false,37,54⟩ (.node .empty ⟨2,false,37,55⟩ .empty)))
def t406_414 : Tree := (.node (.node (.node (.node .empty ⟨2,false,37,60⟩ .empty) ⟨2,false,37,69⟩ .empty) ⟨2,false,37,70⟩ (.node .empty ⟨2,false,44,3⟩ .empty)) ⟨2,false,44,25⟩ (.node (.node .empty ⟨2,false,44,26⟩ .empty) ⟨2,false,44,30⟩ (.node .empty ⟨2,false,44,31⟩ .empty)))
def t396_414 : Tree := .node t396_405 ⟨2,false,37,59⟩ t406_414
def t377_414 : Tree := .node t377_395 ⟨2,false,37,11⟩ t396_414
def t415_424 : Tree := (.node (.node (.node (.node .empty ⟨2,false,44,50⟩ .empty) ⟨2,false,44,55⟩ .empty) ⟨2,false,44,65⟩ (.node .empty ⟨2,false,44,75⟩ .empty)) ⟨2,false,45,0⟩ (.node (.node (.node .empty ⟨2,false,45,1⟩ .empty) ⟨2,false,45,2⟩ .empty) ⟨2,false,45,10⟩ (.node .empty ⟨2,false,45,11⟩ .empty)))
def t425_433 : Tree := (.node (.node (.node (.node .empty ⟨2,false,45,25⟩ .empty) ⟨2,false,45,29⟩ .empty) ⟨2,false,45,30⟩ (.node .empty ⟨2,false,45,34⟩ .empty)) ⟨2,false,45,35⟩ (.node (.node .empty ⟨2,false,45,49⟩ .empty) ⟨2,false,45,50⟩ (.node .empty ⟨2,false,45,54⟩ .empty)))
def t415_433 : Tree := .node t415_424 ⟨2,false,45,24⟩ t425_433
def t434_442 : Tree := (.node (.node (.node (.node .empty ⟨2,false,45,59⟩ .empty) ⟨2,false,45,60⟩ .empty) ⟨2,false,45,69⟩ (.node .empty ⟨2,false,45,70⟩ .empty)) ⟨2,false,48,11⟩ (.node (.node .empty ⟨2,false,48,25⟩ .empty) ⟨2,false,49,3⟩ (.node .empty ⟨2,false,49,11⟩ .empty)))
def t443_451 : Tree := (.node (.node (.node (.node .empty ⟨3,false,1,16⟩ .empty) ⟨3,false,1,23⟩ .empty) ⟨3,false,2,1⟩ (.node .empty ⟨3,false,2,15⟩ .empty)) ⟨3,false,3,0⟩ (.node (.node .empty ⟨3,false,3,14⟩ .empty) ⟨3,false,3,48⟩ (.node .empty ⟨3,false,4,3⟩ .empty)))
def t434_451 : Tree := .node t434_442 ⟨3,false,1,6⟩ t443_451
def t415_451 : Tree := .node t415_433 ⟨2,false,45,55⟩ t434_451
def t377_451 : Tree := .node t377_414 ⟨2,false,44,40⟩ t415_451
def t301_451 : Tree := .node t301_376 ⟨2,false,21,11⟩ t377_451
def t452_461 : Tree := (.node (.node (.node (.node .empty ⟨3,false,6,2⟩ .empty) ⟨3,false,6,43⟩ .empty) ⟨3,false,6,58⟩ (.node .empty ⟨3,false,6,78⟩ .empty)) ⟨3,false,8,0⟩ (.node (.node (.node .empty ⟨3,false,9,1⟩ .empty) ⟨3,false,10,0⟩ .empty) ⟨3,false,12,3⟩ (.node .empty ⟨3,false,13,1⟩ .empty)))
def t462_470 : Tree := (.node (.node (.node (.node .empty ⟨3,false,13,55⟩ .empty) ⟨3,false,13,75⟩ .empty) ⟨3,false,14,14⟩ (.node .empty ⟨3,false,14,48⟩ .empty)) ⟨3,false,15,11⟩ (.node (.node .empty ⟨3,false,15,45⟩ .empty) ⟨3,false,16,34⟩ (.node .empty ⟨3,false,16,54⟩ .empty)))
def t452_470 : Tree := .node t452_461 ⟨3,false,13,40⟩ t462_470
def t471_480 : Tree := (.node (.node (.node (.node .empty ⟨3,false,17,28⟩ .empty) ⟨3,false,17,33⟩ .empty) ⟨3,false,17,49⟩ (.node .empty ⟨3,false,17,54⟩ .empty)) ⟨3,false,17,64⟩ (.node (.node (.node .empty ⟨3,false,17,74⟩ .empty) ⟨3,false,18,28⟩ .empty) ⟨3,false,18,33⟩ (.node .empty ⟨3,false,18,49⟩ .empty)))
def t481_489 : Tree := (.node (.node (.node (.node .empty ⟨3,false,18,64⟩ .empty) ⟨3,false,18,74⟩ .empty) ⟨3,false,19,30⟩ (.node .empty ⟨3,false,19,34⟩ .empty)) ⟨3,false,19,49⟩ (.node (.node .empty ⟨3,false,19,50⟩ .empty) ⟨3,false,19,54⟩ (.node .empty ⟨3,false,19,55⟩ .empty)))
def t471_489 : Tree := .node t471_480 ⟨3,false,18,54⟩ t481_489
def t452_489 : Tree := .node t452_470 ⟨3,false,16,69⟩ t471_489
def t490_499 : Tree := (.node (.node (.node (.node .empty ⟨3,false,19,69⟩ .empty) ⟨3,false,19,70⟩ .empty) ⟨3,false,20,10⟩ (.node .empty ⟨3,false,20,24⟩ .empty)) ⟨3,false,21,2⟩ (.node (.node (.node .empty ⟨3,false,21,10⟩ .empty) ⟨3,false,22,1⟩ .empty) ⟨3,false,22,2⟩ (.node .empty ⟨3,false,23,2⟩ .empty)))
def t500_508 : Tree := (.node (.node (.node (.node .empty ⟨3,false,24,0⟩ .empty) ⟨3,false,24,1⟩ .empty) ⟨3,false,26,3⟩ (.node .empty ⟨3,false,26,11⟩ .empty)) ⟨3,false,27,1⟩ (.node (.node .empty ⟨3,false,27,2⟩ .empty) ⟨3,false,29,11⟩ (.node .empty ⟨3,false,29,25⟩ .empty)))
def t490_508 : Tree := .node t490_499 ⟨3,false,23,10⟩ t500_508
def t509_517 : Tree := (.node (.node (.node (.node .empty ⟨3,false,30,29⟩ .empty) ⟨3,false,30,30⟩ .empty) ⟨3,false,30,49⟩ (.node .empty ⟨3,false,30,54⟩ .empty)) ⟨3,false,30,59⟩ (.node (.node .empty ⟨3,false,30,69⟩ .empty) ⟨3,false,32,35⟩ (.node .empty ⟨3,false,32,55⟩ .empty)))
def t518_526 : Tree := (.node (.node (.node (.node .empty ⟨3,false,33,29⟩ .empty) ⟨3,false,33,49⟩ .empty) ⟨3,false,33,54⟩ (.node .empty ⟨3,false,33,59⟩ .empty)) ⟨3,false,33,69⟩ (.node (.node .empty ⟨3,false,34,24⟩ .empty) ⟨3,false,34,29⟩ (.node .empty ⟨3,false,34,39⟩ .empty)))
def t509_526 : Tree := .node t509_517 ⟨3,false,32,70⟩ t518_526
def t490_526 : Tree := .node t490_508 ⟨3,false,30,25⟩ t509_526
def t452_526 : Tree := .node t452_489 ⟨3,false,19,60⟩ t490_526
def t527_536 : Tree := (.node (.node (.node (.node .empty ⟨3,false,34,54⟩ .empty) ⟨3,false,34,64⟩ .empty) ⟨3,false,34,74⟩ (.node .empty ⟨3,false,35,11⟩ .empty)) ⟨3,false,35,30⟩ (.node (.node (.node .empty ⟨3,false,35,35⟩ .empty) ⟨3,false,35,50⟩ .empty) ⟨3,false,35,55⟩ (.node .empty ⟨3,false,35,60⟩ .empty)))
def t537_545 : Tree := (.node (.node (.node (.node .empty ⟨3,false,36,24⟩ .empty) ⟨3,false,36,29⟩ .empty) ⟨3,false,36,39⟩ (.node .empty ⟨3,false,36,49⟩ .empty)) ⟨3,false,36,54⟩ (.node (.node .empty ⟨3,false,36,64⟩ .empty) ⟨3,false,36,74⟩ (.node .empty ⟨3,false,37,10⟩ .empty)))
def t527_545 : Tree := .node t527_536 ⟨3,false,35,70⟩ t537_545
def t546_555 : Tree := (.node (.node (.node (.node .empty ⟨3,false,37,29⟩ .empty) ⟨3,false,37,34⟩ .empty) ⟨3,false,37,49⟩ (.node .empty ⟨3,false,37,54⟩ .empty)) ⟨3,false,37,59⟩ (.node (.node (.node .empty ⟨3,false,37,69⟩ .empty) ⟨3,false,38,2⟩ .empty) ⟨3,false,38,10⟩ (.node .empty ⟨3,false,38,24⟩ .empty)))
def t556_564 : Tree := (.node (.node (.node (.node .empty ⟨3,false,38,29⟩ .empty) ⟨3,false,38,33⟩ .empty) ⟨3,false,38,39⟩ (.node .empty ⟨3,false,38,49⟩ .empty)) ⟨3,false,38,54⟩ (.node (.node .empty ⟨3,false,38,64⟩ .empty) ⟨3,false,38,74⟩ (.node .empty ⟨3,false,39,25⟩ .empty)))
def t546_564 : Tree := .node t546_555 ⟨3,false,38,28⟩ t556_564
def t527_564 : Tree := .node t527_545 ⟨3,false,37,24⟩ t546_564
def t565_574 : Tree := (.node (.node (.node (.node .empty ⟨3,false,39,40⟩ .empty) ⟨3,false,39,50⟩ .empty) ⟨3,false,39,55⟩ (.node .empty ⟨3,false,39,65⟩ .empty)) ⟨3,false,39,75⟩ (.node (.node (.node .empty ⟨3,false,40,10⟩ .empty) ⟨3,false,40,24⟩ .empty) ⟨3,false,40,29⟩ (.node .empty ⟨3,false,40,34⟩ .empty)))
def t575_583 : Tree := (.node (.node (.node (.node .empty ⟨3,false,40,54⟩ .empty) ⟨3,false,40,59⟩ .empty) ⟨3,false,40,69⟩ (.node .empty ⟨3,false,42,50⟩ .empty)) ⟨3,false,42,55⟩ (.node (.node .empty ⟨3,false,42,65⟩ .empty) ⟨3,false,42,75⟩ (.node .empty ⟨3,false,43,11⟩ .empty)))
def t565_583 : Tree := .node t565_574 ⟨3,false,40,49⟩ t575_583
def t584_592 : Tree := (.node (.node (.node (.node .empty ⟨3,false,43,35⟩ .empty) ⟨3,false,43,50⟩ .empty) ⟨3,false,43,55⟩ (.node .empty ⟨3,false,43,60⟩ .empty)) ⟨3,false,43,70⟩ (.node (.node .empty ⟨3,false,44,2⟩ .empty) ⟨3,false,44,24⟩ (.node .empty ⟨3,false,44,28⟩ .empty)))
def t593_601 : Tree := (.node (.node (.node (.node .empty ⟨3,false,44,33⟩ .empty) ⟨3,false,44,39⟩ .empty) ⟨3,false,44,49⟩ (.node .empty ⟨3,false,44,54⟩ .empty)) ⟨3,false,44,64⟩ (.node (.node .empty ⟨3,false,44,74⟩ .empty) ⟨3,false,45,1⟩ (.node .empty ⟨3,false,45,10⟩ .empty)))
def t584_601 : Tree := .node t584_592 ⟨3,false,44,29⟩ t593_601
def t565_601 : Tree := .node t565_583 ⟨3,false,43,30⟩ t584_601
def t527_601 : Tree := .node t527_564 ⟨3,false,39,30⟩ t565_601
def t452_601 : Tree := .node t452_526 ⟨3,false,34,49⟩ t527_601
def t301_601 : Tree := .node t301_451 ⟨3,false,4,20⟩ t452_601
def t0_601 : Tree := .node t0_300 ⟨1,true,17,52⟩ t301_601
def t602_611 : Tree := (.node (.node (.node (.node .empty ⟨3,false,45,29⟩ .empty) ⟨3,false,45,34⟩ .empty) ⟨3,false,45,49⟩ (.node .empty ⟨3,false,45,54⟩ .empty)) ⟨3,false,45,59⟩ (.node (.node (.node .empty ⟨3,false,45,69⟩ .empty) ⟨3,false,46,0⟩ .empty) ⟨3,false,46,2⟩ (.node .empty ⟨3,false,46,10⟩ .empty)))
def t612_620 : Tree := (.node (.node (.node (.node .empty ⟨3,false,46,28⟩ .empty) ⟨3,false,46,29⟩ .empty) ⟨3,false,46,33⟩ (.node .empty ⟨3,false,46,39⟩ .empty)) ⟨3,false,46,49⟩ (.node (.node .empty ⟨3,false,46,54⟩ .empty) ⟨3,false,46,64⟩ (.node .empty ⟨3,false,46,74⟩ .empty)))
def t602_620 : Tree := .node t602_611 ⟨3,false,46,24⟩ t612_620
def t621_630 : Tree := (.node (.node (.node (.node .empty ⟨3,false,47,30⟩ .empty) ⟨3,false,47,35⟩ .empty) ⟨3,false,47,50⟩ (.node .empty ⟨3,false,47,55⟩ .empty)) ⟨3,false,47,60⟩ (.node (.node (.node .empty ⟨3,false,47,70⟩ .empty) ⟨3,false,48,10⟩ .empty) ⟨3,false,48,24⟩ (.node .empty ⟨3,false,49,2⟩ .empty)))
def t631_639 : Tree := (.node (.node (.node (.node .empty ⟨3,false,50,1⟩ .empty) ⟨3,false,50,10⟩ .empty) ⟨3,false,50,24⟩ (.node .empty ⟨3,false,50,25⟩ .empty)) ⟨3,false,50,29⟩ (.node (.node .empty ⟨3,false,50,30⟩ .empty) ⟨3,false,50,34⟩ (.node .empty ⟨3,false,50,49⟩ .empty)))
def t621_639 : Tree := .node t621_630 ⟨3,false,49,10⟩ t631_639
def t602_639 : Tree := .node t602_620 ⟨3,false,47,11⟩ t621_639
def t640_649 : Tree := (.node (.node (.node (.node .empty ⟨3,false,50,59⟩ .empty) ⟨3,false,50,69⟩ .empty) ⟨3,false,51,3⟩ (.node .empty ⟨3,false,51,25⟩ .empty)) ⟨3,false,51,30⟩ (.node (.node (.node .empty ⟨3,false,51,40⟩ .empty) ⟨3,false,51,50⟩ .empty) ⟨3,false,51,55⟩ (.node .empty ⟨3,false,51,65⟩ .empty)))
def t650_658 : Tree := (.node (.node (.node (.node .empty ⟨3,true,0,7⟩ .empty) ⟨3,true,1,2⟩ .empty) ⟨3,true,1,19⟩ (.node .empty ⟨3,true,2,15⟩ .empty)) ⟨3,true,3,3⟩ (.node (.node .empty ⟨3,true,3,20⟩ .empty) ⟨3,true,5,10⟩ (.node .empty ⟨3,true,5,44⟩ .empty)))
def t640_658 : Tree := .node t640_649 ⟨3,false,51,75⟩ t650_658
def t659_668 : Tree := (.node (.node (.node (.node .empty ⟨3,true,7,1⟩ .empty) ⟨3,true,8,11⟩ .empty) ⟨3,true,8,39⟩ (.node .empty ⟨3,true,8,45⟩ .empty)) ⟨3,true,8,54⟩ (.node (.node (.node .empty ⟨3,true,8,74⟩ .empty) ⟨3,true,11,6⟩ .empty) ⟨3,true,16,34⟩ (.node .empty ⟨3,true,16,54⟩ .empty)))
def t669_677 : Tree := (.node (.node (.node (.node .empty ⟨3,true,17,49⟩ .empty) ⟨3,true,17,54⟩ .empty) ⟨3,true,17,64⟩ (.node .empty ⟨3,true,17,74⟩ .empty)) ⟨3,true,18,33⟩ (.node (.node .empty ⟨3,true,18,39⟩ .empty) ⟨3,true,18,53⟩ (.node .empty ⟨3,true,18,54⟩ .empty)))
def t659_677 : Tree := .node t659_668 ⟨3,true,16,69⟩ t669_677
def t640_677 : Tree := .node t640_658 ⟨3,true,6,2⟩ t659_677
def t602_677 : Tree := .node t602_639 ⟨3,false,50,54⟩ t640_677
def t678_687 : Tree := (.node (.node (.node (.node .empty ⟨3,true,18,63⟩ .empty) ⟨3,true,18,73⟩ .empty) ⟨3,true,18,74⟩ (.node .empty ⟨3,true,19,0⟩ .empty)) ⟨3,true,19,24⟩ (.node (.node (.node .empty ⟨3,true,19,29⟩ .empty) ⟨3,true,20,10⟩ .empty) ⟨3,true,20,24⟩ (.node .empty ⟨3,true,21,2⟩ .empty)))
def t688_696 : Tree := (.node (.node (.node (.node .empty ⟨3,true,22,2⟩ .empty) ⟨3,true,23,6⟩ .empty) ⟨3,true,25,6⟩ (.node .empty ⟨3,true,25,14⟩ .empty)) ⟨3,true,28,14⟩ (.node (.node .empty ⟨3,true,28,28⟩ .empty) ⟨3,true,30,28⟩ (.node .empty ⟨3,true,30,33⟩ .empty)))
def t678_696 : Tree := .node t678_687 ⟨3,true,21,10⟩ t688_696
def t697_706 : Tree := (.node (.node (.node (.node .empty ⟨3,true,30,53⟩ .empty) ⟨3,true,30,58⟩ .empty) ⟨3,true,30,68⟩ (.node .empty ⟨3,true,30,78⟩ .empty)) ⟨3,true,31,38⟩ (.node (.node (.node .empty ⟨3,true,31,58⟩ .empty) ⟨3,true,31,73⟩ .empty) ⟨3,true,33,29⟩ (.node .empty ⟨3,true,33,49⟩ .empty)))
def t707_715 : Tree := (.node (.node (.node (.node .empty ⟨3,true,33,59⟩ .empty) ⟨3,true,33,69⟩ .empty) ⟨3,true,34,14⟩ (.node .empty ⟨3,true,34,28⟩ .empty)) ⟨3,true,34,29⟩ (.node (.node .empty ⟨3,true,34,33⟩ .empty) ⟨3,true,34,38⟩ (.node .empty ⟨3,true,34,49⟩ .empty)))
def t697_715 : Tree := .node t697_706 ⟨3,true,33,54⟩ t707_715
def t678_715 : Tree := .node t678_696 ⟨3,true,30,43⟩ t697_715
def t716_725 : Tree := (.node (.node (.node (.node .empty ⟨3,true,34,54⟩ .empty) ⟨3,true,34,58⟩ .empty) ⟨3,true,34,63⟩ (.node .empty ⟨3,true,34,64⟩ .empty)) ⟨3,true,34,73⟩ (.node (.node (.node .empty ⟨3,true,34,74⟩ .empty) ⟨3,true,36,24⟩ .empty) ⟨3,true,36,29⟩ (.node .empty ⟨3,true,36,39⟩ .empty)))
def t726_734 : Tree := (.node (.node (.node (.node .empty ⟨3,true,36,54⟩ .empty) ⟨3,true,36,64⟩ .empty) ⟨3,true,36,74⟩ (.node .empty ⟨3,true,37,10⟩ .empty)) ⟨3,true,37,29⟩ (.node (.node .empty ⟨3,true,37,34⟩ .empty) ⟨3,true,37,49⟩ (.node .empty ⟨3,true,37,54⟩ .empty)))
def t716_734 : Tree := .node t716_725 ⟨3,true,36,49⟩ t726_734
def t735_743 : Tree := (.node (.node (.node (.node .empty ⟨3,true,37,69⟩ .empty) ⟨3,true,38,10⟩ .empty) ⟨3,true,38,14⟩ (.node .empty ⟨3,true,38,24⟩ .empty)) ⟨3,true,38,29⟩ (.node (.node .empty ⟨3,true,38,33⟩ .empty) ⟨3,true,38,38⟩ (.node .empty ⟨3,true,38,39⟩ .empty)))
def t744_752 : Tree := (.node (.node (.node (.node .empty ⟨3,true,38,53⟩ .empty) ⟨3,true,38,54⟩ .empty) ⟨3,true,38,58⟩ (.node .empty ⟨3,true,38,63⟩ .empty)) ⟨3,true,38,64⟩ (.node (.node .empty ⟨3,true,38,73⟩ .empty) ⟨3,true,38,74⟩ (.node .empty ⟨3,true,40,6⟩ .empty)))
def t735_752 : Tree := .node t735_743 ⟨3,true,38,49⟩ t744_752
def t716_752 : Tree := .node t716_734 ⟨3,true,37,59⟩ t735_752
def t678_752 : Tree := .node t678_715 ⟨3,true,34,53⟩ t716_752
def t602_752 : Tree := .node t602_677 ⟨3,true,18,58⟩ t678_752
def t753_762 : Tree := (.node (.node (.node (.node .empty ⟨3,true,40,33⟩ .empty) ⟨3,true,40,43⟩ .empty) ⟨3,true,40,53⟩ (.node .empty ⟨3,true,40,58⟩ .empty)) ⟨3,true,40,68⟩ (.node (.node (.node .empty ⟨3,true,40,78⟩ .empty) ⟨3,true,41,53⟩ .empty) ⟨3,true,41,58⟩ (.node .empty ⟨3,true,41,68⟩ .empty)))
def t763_771 : Tree := (.node (.node (.node (.node .empty ⟨3,true,44,2⟩ .empty) ⟨3,true,44,24⟩ .empty) ⟨3,true,44,29⟩ (.node .empty ⟨3,true,44,39⟩ .empty)) ⟨3,true,44,49⟩ (.node (.node .empty ⟨3,true,44,54⟩ .empty) ⟨3,true,44,64⟩ (.node .empty ⟨3,true,44,74⟩ .empty)))
def t753_771 : Tree := .node t753_762 ⟨3,true,41,78⟩ t763_771
def t772_781 : Tree := (.node (.node (.node (.node .empty ⟨3,true,45,29⟩ .empty) ⟨3,true,45,34⟩ .empty) ⟨3,true,45,49⟩ (.node .empty ⟨3,true,45,54⟩ .empty)) ⟨3,true,45,59⟩ (.node (.node (.node .empty ⟨3,true,45,69⟩ .empty) ⟨3,true,46,0⟩ .empty) ⟨3,true,46,1⟩ (.node .empty ⟨3,true,46,2⟩ .empty)))
def t782_790 : Tree := (.node (.node (.node (.node .empty ⟨3,true,46,14⟩ .empty) ⟨3,true,46,24⟩ .empty) ⟨3,true,46,28⟩ (.node .empty ⟨3,true,46,29⟩ .empty)) ⟨3,true,46,33⟩ (.node (.node .empty ⟨3,true,46,38⟩ .empty) ⟨3,true,46,39⟩ (.node .empty ⟨3,true,46,49⟩ .empty)))
def t772_790 : Tree := .node t772_781 ⟨3,true,46,10⟩ t782_790
def t753_790 : Tree := .node t753_771 ⟨3,true,45,10⟩ t772_790
def t791_800 : Tree := (.node (.node (.node (.node .empty ⟨3,true,46,54⟩ .empty) ⟨3,true,46,58⟩ .empty) ⟨3,true,46,63⟩ (.node .empty ⟨3,true,46,64⟩ .empty)) ⟨3,true,46,73⟩ (.node (.node (.node .empty ⟨3,true,46,74⟩ .empty) ⟨3,true,47,24⟩ .empty) ⟨3,true,47,29⟩ (.node .empty ⟨3,true,48,10⟩ .empty)))
def t801_809 : Tree := (.node (.node (.node (.node .empty ⟨3,true,49,2⟩ .empty) ⟨3,true,49,10⟩ .empty) ⟨3,true,50,6⟩ (.node .empty ⟨3,true,50,28⟩ .empty)) ⟨3,true,50,33⟩ (.node (.node .empty ⟨3,true,50,43⟩ .empty) ⟨3,true,50,53⟩ (.node .empty ⟨3,true,50,58⟩ .empty)))
def t791_809 : Tree := .node t791_800 ⟨3,true,48,24⟩ t801_809
def t810_818 : Tree := (.node (.node (.node (.node .empty ⟨3,true,50,78⟩ .empty) ⟨4,false,5,1⟩ .empty) ⟨4,false,5,15⟩ (.node .empty ⟨4,false,16,2⟩ .empty)) ⟨4,false,16,43⟩ (.node (.node .empty ⟨4,false,16,58⟩ .empty) ⟨4,false,16,78⟩ (.node .empty ⟨4,false,20,0⟩ .empty)))
def t819_827 : Tree := (.node (.node (.node (.node .empty ⟨4,true,1,6⟩ .empty) ⟨4,true,1,16⟩ .empty) ⟨4,true,1,23⟩ (.node .empty ⟨4,true,2,1⟩ .empty)) ⟨4,true,2,15⟩ (.node (.node .empty ⟨4,true,6,2⟩ .empty) ⟨4,true,6,43⟩ (.node .empty ⟨4,true,6,58⟩ .empty)))
def t810_827 : Tree := .node t810_818 ⟨4,false,47,0⟩ t819_827
def t791_827 : Tree := .node t791_809 ⟨3,true,50,68⟩ t810_827
def t753_827 : Tree := .node t753_790 ⟨3,true,46,53⟩ t791_827
def t828_837 : Tree := (.node (.node (.node (.node .empty ⟨4,true,8,0⟩ .empty) ⟨4,true,9,1⟩ .empty) ⟨4,true,12,3⟩ (.node .empty ⟨4,true,14,14⟩ .empty)) ⟨4,true,14,48⟩ (.node (.node (.node .empty ⟨4,true,16,34⟩ .empty) ⟨4,true,16,49⟩ .empty) ⟨4,true,16,54⟩ (.node .empty ⟨4,true,16,69⟩ .empty)))
def t838_846 : Tree := (.node (.node (.node (.node .empty ⟨4,true,17,33⟩ .empty) ⟨4,true,17,49⟩ .empty) ⟨4,true,17,54⟩ (.node .empty ⟨4,true,17,64⟩ .empty)) ⟨4,true,17,74⟩ (.node (.node .empty ⟨4,true,19,30⟩ .empty) ⟨4,true,19,34⟩ (.node .empty ⟨4,true,19,49⟩ .empty)))
def t828_846 : Tree := .node t828_837 ⟨4,true,17,28⟩ t838_846
def t847_856 : Tree := (.node (.node (.node (.node .empty ⟨4,true,19,54⟩ .empty) ⟨4,true,19,55⟩ .empty) ⟨4,true,19,60⟩ (.node .empty ⟨4,true,19,69⟩ .empty)) ⟨4,true,19,70⟩ (.node (.node (.node .empty ⟨4,true,20,10⟩ .empty) ⟨4,true,20,24⟩ .empty) ⟨4,true,21,2⟩ (.node .empty ⟨4,true,21,10⟩ .empty)))
def t857_865 : Tree := (.node (.node (.node (.node .empty ⟨4,true,22,2⟩ .empty) ⟨4,true,26,3⟩ .empty) ⟨4,true,26,11⟩ (.node .empty ⟨4,true,29,11⟩ .empty)) ⟨4,true,29,25⟩ (.node (.node .empty ⟨4,true,32,35⟩ .empty) ⟨4,true,32,55⟩ (.node .empty ⟨4,true,32,70⟩ .empty)))
def t847_865 : Tree := .node t847_856 ⟨4,true,22,1⟩ t857_865
def t828_865 : Tree := .node t828_846 ⟨4,true,19,50⟩ t847_865
def t866_875 : Tree := (.node (.node (.node (.node .empty ⟨4,true,33,49⟩ .empty) ⟨4,true,33,54⟩ .empty) ⟨4,true,33,59⟩ (.node .empty ⟨4,true,33,69⟩ .empty)) ⟨4,true,35,11⟩ (.node (.node (.node .empty ⟨4,true,35,24⟩ .empty) ⟨4,true,35,25⟩ .empty) ⟨4,true,35,29⟩ (.node .empty ⟨4,true,35,30⟩ .empty)))
def t876_884 : Tree := (.node (.node (.node (.node .empty ⟨4,true,35,49⟩ .empty) ⟨4,true,35,50⟩ .empty) ⟨4,true,35,54⟩ (.node .empty ⟨4,true,35,55⟩ .empty)) ⟨4,true,35,59⟩ (.node (.node .empty ⟨4,true,35,60⟩ .empty) ⟨4,true,35,69⟩ (.node .empty ⟨4,true,35,70⟩ .empty)))
def t866_884 : Tree := .node t866_875 ⟨4,true,35,35⟩ t876_884
def t885_893 : Tree := (.node (.node (.node (.node .empty ⟨4,true,36,29⟩ .empty) ⟨4,true,36,39⟩ .empty) ⟨4,true,36,49⟩ (.node .empty ⟨4,true,36,54⟩ .empty)) ⟨4,true,36,64⟩ (.node (.node .empty ⟨4,true,36,74⟩ .empty) ⟨4,true,37,10⟩ (.node .empty ⟨4,true,37,24⟩ .empty)))
def t894_902 : Tree := (.node (.node (.node (.node .empty ⟨4,true,37,34⟩ .empty) ⟨4,true,37,49⟩ .empty) ⟨4,true,37,54⟩ (.node .empty ⟨4,true,37,59⟩ .empty)) ⟨4,true,37,69⟩ (.node (.node .empty ⟨4,true,39,25⟩ .empty) ⟨4,true,39,30⟩ (.node .empty ⟨4,true,39,40⟩ .empty)))
def t885_902 : Tree := .node t885_893 ⟨4,true,37,29⟩ t894_902
def t866_902 : Tree := .node t866_884 ⟨4,true,36,24⟩ t885_902
def t828_902 : Tree := .node t828_865 ⟨4,true,33,29⟩ t866_902
def t753_902 : Tree := .node t753_827 ⟨4,true,6,78⟩ t828_902
def t602_902 : Tree := .node t602_752 ⟨3,true,40,28⟩ t753_902
def t903_912 : Tree := (.node (.node (.node (.node .empty ⟨4,true,39,55⟩ .empty) ⟨4,true,39,65⟩ .empty) ⟨4,true,39,75⟩ (.node .empty ⟨4,true,42,50⟩ .empty)) ⟨4,true,42,55⟩ (.node (.node (.node .empty ⟨4,true,42,65⟩ .empty) ⟨4,true,42,75⟩ .empty) ⟨4,true,43,2⟩ (.node .empty ⟨4,true,43,10⟩ .empty)))
def t913_921 : Tree := (.node (.node (.node (.node .empty ⟨4,true,43,24⟩ .empty) ⟨4,true,43,29⟩ .empty) ⟨4,true,43,30⟩ (.node .empty ⟨4,true,43,34⟩ .empty)) ⟨4,true,43,35⟩ (.node (.node .empty ⟨4,true,43,49⟩ .empty) ⟨4,true,43,50⟩ (.node .empty ⟨4,true,43,54⟩ .empty)))
def t903_921 : Tree := .node t903_912 ⟨4,true,43,11⟩ t913_921
def t922_931 : Tree := (.node (.node (.node (.node .empty ⟨4,true,43,59⟩ .empty) ⟨4,true,43,60⟩ .empty) ⟨4,true,43,69⟩ (.node .empty ⟨4,true,43,70⟩ .empty)) ⟨4,true,44,2⟩ (.node (.node (.node .empty ⟨4,true,44,24⟩ .empty) ⟨4,true,44,28⟩ .empty) ⟨4,true,44,29⟩ (.node .empty ⟨4,true,44,33⟩ .empty)))
def t932_940 : Tree := (.node (.node (.node (.node .empty ⟨4,true,44,49⟩ .empty) ⟨4,true,44,54⟩ .empty) ⟨4,true,44,64⟩ (.node .empty ⟨4,true,44,74⟩ .empty)) ⟨4,true,45,1⟩ (.node (.node .empty ⟨4,true,45,10⟩ .empty) ⟨4,true,45,24⟩ (.node .empty ⟨4,true,45,29⟩ .empty)))
def t922_940 : Tree := .node t922_931 ⟨4,true,44,39⟩ t932_940
def t903_940 : Tree := .node t903_921 ⟨4,true,43,55⟩ t922_940
def t941_950 : Tree := (.node (.node (.node (.node .empty ⟨4,true,45,49⟩ .empty) ⟨4,true,45,54⟩ .empty) ⟨4,true,45,59⟩ (.node .empty ⟨4,true,45,69⟩ .empty)) ⟨4,true,47,0⟩ (.node (.node (.node .empty ⟨4,true,47,1⟩ .empty) ⟨4,true,47,2⟩ .empty) ⟨4,true,47,10⟩ (.node .empty ⟨4,true,47,11⟩ .empty)))
def t951_959 : Tree := (.node (.node (.node (.node .empty ⟨4,true,47,25⟩ .empty) ⟨4,true,47,29⟩ .empty) ⟨4,true,47,30⟩ (.node .empty ⟨4,true,47,34⟩ .empty)) ⟨4,true,47,35⟩ (.node (.node .empty ⟨4,true,47,49⟩ .empty) ⟨4,true,47,50⟩ (.node .empty ⟨4,true,47,54⟩ .empty)))
def t941_959 : Tree := .node t941_950 ⟨4,true,47,24⟩ t951_959
def t960_968 : Tree := (.node (.node (.node (.node .empty ⟨4,true,47,59⟩ .empty) ⟨4,true,47,60⟩ .empty) ⟨4,true,47,69⟩ (.node .empty ⟨4,true,47,70⟩ .empty)) ⟨4,true,48,10⟩ (.node (.node .empty ⟨4,true,48,24⟩ .empty) ⟨4,true,49,2⟩ (.node .empty ⟨4,true,49,10⟩ .empty)))
def t969_977 : Tree := (.node (.node (.node (.node .empty ⟨4,true,51,25⟩ .empty) ⟨4,true,51,30⟩ .empty) ⟨4,true,51,40⟩ (.node .empty ⟨4,true,51,50⟩ .empty)) ⟨4,true,51,55⟩ (.node (.node .empty ⟨4,true,51,65⟩ .empty) ⟨4,true,51,75⟩ (.node .empty ⟨5,false,0,17⟩ .empty)))
def t960_977 : Tree := .node t960_968 ⟨4,true,51,3⟩ t969_977
def t941_977 : Tree := .node t941_959 ⟨4,true,47,55⟩ t960_977
def t903_977 : Tree := .node t903_940 ⟨4,true,45,34⟩ t941_977
def t978_987 : Tree := (.node (.node (.node (.node .empty ⟨5,false,7,14⟩ .empty) ⟨5,false,7,48⟩ .empty) ⟨5,false,11,4⟩ (.node .empty ⟨5,false,18,1⟩ .empty)) ⟨5,false,18,31⟩ (.node (.node (.node .empty ⟨5,false,18,40⟩ .empty) ⟨5,false,18,51⟩ .empty) ⟨5,false,18,55⟩ (.node .empty ⟨5,false,18,56⟩ .empty)))
def t988_996 : Tree := (.node (.node (.node (.node .empty ⟨5,false,18,71⟩ .empty) ⟨5,false,18,75⟩ .empty) ⟨5,false,23,4⟩ (.node .empty ⟨5,false,25,4⟩ .empty)) ⟨5,false,25,12⟩ (.node (.node .empty ⟨5,false,28,12⟩ .empty) ⟨5,false,28,26⟩ (.node .empty ⟨5,false,30,26⟩ .empty)))
def t978_996 : Tree := .node t978_987 ⟨5,false,18,61⟩ t988_996
def t997_1006 : Tree := (.node (.node (.node (.node .empty ⟨5,false,30,41⟩ .empty) ⟨5,false,30,51⟩ .empty) ⟨5,false,30,56⟩ (.node .empty ⟨5,false,30,66⟩ .empty)) ⟨5,false,30,76⟩ (.node (.node (.node .empty ⟨5,false,31,36⟩ .empty) ⟨5,false,31,56⟩ .empty) ⟨5,false,31,71⟩ (.node .empty ⟨5,false,34,12⟩ .empty)))
def t1007_1015 : Tree := (.node (.node (.node (.node .empty ⟨5,false,34,36⟩ .empty) ⟨5,false,34,51⟩ .empty) ⟨5,false,34,56⟩ (.node .empty ⟨5,false,34,61⟩ .empty)) ⟨5,false,34,71⟩ (.node (.node .empty ⟨5,false,38,12⟩ .empty) ⟨5,false,38,31⟩ (.node .empty ⟨5,false,38,36⟩ .empty)))
def t997_1015 : Tree := .node t997_1006 ⟨5,false,34,31⟩ t1007_1015
def t978_1015 : Tree := .node t978_996 ⟨5,false,30,31⟩ t997_1015
def t1016_1025 : Tree := (.node (.node (.node (.node .empty ⟨5,false,38,56⟩ .empty) ⟨5,false,38,61⟩ .empty) ⟨5,false,38,71⟩ (.node .empty ⟨5,false,40,4⟩ .empty)) ⟨5,false,40,26⟩ (.node (.node (.node .empty ⟨5,false,40,31⟩ .empty) ⟨5,false,40,41⟩ .empty) ⟨5,false,40,51⟩ (.node .empty ⟨5,false,40,56⟩ .empty)))
def t1026_1034 : Tree := (.node (.node (.node (.node .empty ⟨5,false,40,76⟩ .empty) ⟨5,false,41,51⟩ .empty) ⟨5,false,41,56⟩ (.node .empty ⟨5,false,41,66⟩ .empty)) ⟨5,false,41,76⟩ (.node (.node .empty ⟨5,false,46,12⟩ .empty) ⟨5,false,46,31⟩ (.node .empty ⟨5,false,46,36⟩ .empty)))
def t1016_1034 : Tree := .node t1016_1025 ⟨5,false,40,66⟩ t1026_1034
def t1035_1043 : Tree := (.node (.node (.node (.node .empty ⟨5,false,46,56⟩ .empty) ⟨5,false,46,61⟩ .empty) ⟨5,false,46,71⟩ (.node .empty ⟨5,false,50,4⟩ .empty)) ⟨5,false,50,26⟩ (.node (.node .empty ⟨5,false,50,31⟩ .empty) ⟨5,false,50,41⟩ (.node .empty ⟨5,false,50,51⟩ .empty)))
def t1044_1052 : Tree := (.node (.node (.node (.node .empty ⟨5,false,50,66⟩ .empty) ⟨5,false,50,76⟩ .empty) ⟨5,true,0,8⟩ (.node .empty ⟨5,true,0,17⟩ .empty)) ⟨5,true,1,3⟩ (.node (.node .empty ⟨5,true,1,20⟩ .empty) ⟨5,true,2,16⟩ (.node .empty ⟨5,true,5,11⟩ .empty)))
def t1035_1052 : Tree := .node t1035_1043 ⟨5,false,50,56⟩ t1044_1052
def t1016_1052 : Tree := .node t1016_1034 ⟨5,false,46,51⟩ t1035_1052
def t978_1052 : Tree := .node t978_1015 ⟨5,false,38,51⟩ t1016_1052
def t903_1052 : Tree := .node t903_977 ⟨5,false,7,0⟩ t978_1052
def t1053_1062 : Tree := (.node (.node (.node (.node .empty ⟨5,true,6,3⟩ .empty) ⟨5,true,7,0⟩ .empty) ⟨5,true,8,40⟩ (.node .empty ⟨5,true,8,55⟩ .empty)) ⟨5,true,8,75⟩ (.node (.node (.node .empty ⟨5,true,11,4⟩ .empty) ⟨5,true,16,35⟩ .empty) ⟨5,true,16,55⟩ (.node .empty ⟨5,true,16,70⟩ .empty)))
def t1063_1071 : Tree := (.node (.node (.node (.node .empty ⟨5,true,17,55⟩ .empty) ⟨5,true,17,65⟩ .empty) ⟨5,true,17,75⟩ (.node .empty ⟨5,true,18,31⟩ .empty)) ⟨5,true,18,40⟩ (.node (.node .empty ⟨5,true,18,51⟩ .empty) ⟨5,true,18,55⟩ (.node .empty ⟨5,true,18,56⟩ .empty)))
def t1053_1071 : Tree := .node t1053_1062 ⟨5,true,17,50⟩ t1063_1071
def t1072_1081 : Tree := (.node (.node (.node (.node .empty ⟨5,true,18,71⟩ .empty) ⟨5,true,18,75⟩ .empty) ⟨5,true,19,25⟩ (.node .empty ⟨5,true,19,30⟩ .empty)) ⟨5,true,20,11⟩ (.node (.node (.node .empty ⟨5,true,20,25⟩ .empty) ⟨5,true,21,3⟩ .empty) ⟨5,true,21,11⟩ (.node .empty ⟨5,true,22,3⟩ .empty)))
def t1082_1090 : Tree := (.node (.node (.node (.node .empty ⟨5,true,25,4⟩ .empty) ⟨5,true,25,12⟩ .empty) ⟨5,true,28,12⟩ (.node .empty ⟨5,true,28,26⟩ .empty)) ⟨5,true,30,26⟩ (.node (.node .empty ⟨5,true,30,31⟩ .empty) ⟨5,true,30,41⟩ (.node .empty ⟨5,true,30,51⟩ .empty)))
def t1072_1090 : Tree := .node t1072_1081 ⟨5,true,23,4⟩ t1082_1090
def t1053_1090 : Tree := .node t1053_1071 ⟨5,true,18,61⟩ t1072_1090
def t1091_1100 : Tree := (.node (.node (.node (.node .empty ⟨5,true,30,66⟩ .empty) ⟨5,true,30,76⟩ .empty) ⟨5,true,31,36⟩ (.node .empty ⟨5,true,31,56⟩ .empty)) ⟨5,true,31,71⟩ (.node (.node (.node .empty ⟨5,true,33,30⟩ .empty) ⟨5,true,33,50⟩ .empty) ⟨5,true,33,55⟩ (.node .empty ⟨5,true,33,60⟩ .empty)))
def t1101_1109 : Tree := (.node (.node (.node (.node .empty ⟨5,true,34,12⟩ .empty) ⟨5,true,34,26⟩ .empty) ⟨5,true,34,30⟩ (.node .empty ⟨5,true,34,31⟩ .empty)) ⟨5,true,34,36⟩ (.node (.node .empty ⟨5,true,34,50⟩ .empty) ⟨5,true,34,51⟩ (.node .empty ⟨5,true,34,55⟩ .empty)))
def t1091_1109 : Tree := .node t1091_1100 ⟨5,true,33,70⟩ t1101_1109
def t1110_1118 : Tree := (.node (.node (.node (.node .empty ⟨5,true,34,61⟩ .empty) ⟨5,true,34,65⟩ .empty) ⟨5,true,34,71⟩ (.node .empty ⟨5,true,34,75⟩ .empty)) ⟨5,true,36,25⟩ (.node (.node .empty ⟨5,true,36,30⟩ .empty) ⟨5,true,36,40⟩ (.node .empty ⟨5,true,36,50⟩ .empty)))
def t1119_1127 : Tree := (.node (.node (.node (.node .empty ⟨5,true,36,65⟩ .empty) ⟨5,true,36,75⟩ .empty) ⟨5,true,37,11⟩ (.node .empty ⟨5,true,37,30⟩ .empty)) ⟨5,true,37,35⟩ (.node (.node .empty ⟨5,true,37,50⟩ .empty) ⟨5,true,37,55⟩ (.node .empty ⟨5,true,37,60⟩ .empty)))
def t1110_1127 : Tree := .node t1110_1118 ⟨5,true,36,55⟩ t1119_1127
def t1091_1127 : Tree := .node t1091_1109 ⟨5,true,34,56⟩ t1110_1127
def t1053_1127 : Tree := .node t1053_1090 ⟨5,true,30,56⟩ t1091_1127
def t1128_1137 : Tree := (.node (.node (.node (.node .empty ⟨5,true,38,11⟩ .empty) ⟨5,true,38,12⟩ .empty) ⟨5,true,38,25⟩ (.node .empty ⟨5,true,38,30⟩ .empty)) ⟨5,true,38,31⟩ (.node (.node (.node .empty ⟨5,true,38,36⟩ .empty) ⟨5,true,38,40⟩ .empty) ⟨5,true,38,50⟩ (.node .empty ⟨5,true,38,51⟩ .empty)))
def t1138_1146 : Tree := (.node (.node (.node (.node .empty ⟨5,true,38,56⟩ .empty) ⟨5,true,38,61⟩ .empty) ⟨5,true,38,65⟩ (.node .empty ⟨5,true,38,71⟩ .empty)) ⟨5,true,38,75⟩ (.node (.node .empty ⟨5,true,40,4⟩ .empty) ⟨5,true,40,26⟩ (.node .empty ⟨5,true,40,31⟩ .empty)))
def t1128_1146 : Tree := .node t1128_1137 ⟨5,true,38,55⟩ t1138_1146
def t1147_1156 : Tree := (.node (.node (.node (.node .empty ⟨5,true,40,51⟩ .empty) ⟨5,true,40,56⟩ .empty) ⟨5,true,40,66⟩ (.node .empty ⟨5,true,40,76⟩ .empty)) ⟨5,true,41,51⟩ (.node (.node (.node .empty ⟨5,true,41,56⟩ .empty) ⟨5,true,41,66⟩ .empty) ⟨5,true,41,76⟩ (.node .empty ⟨5,true,44,3⟩ .empty)))
def t1157_1165 : Tree := (.node (.node (.node (.node .empty ⟨5,true,44,30⟩ .empty) ⟨5,true,44,40⟩ .empty) ⟨5,true,44,50⟩ (.node .empty ⟨5,true,44,55⟩ .empty)) ⟨5,true,44,65⟩ (.node (.node .empty ⟨5,true,44,75⟩ .empty) ⟨5,true,45,11⟩ (.node .empty ⟨5,true,45,30⟩ .empty)))
def t1147_1165 : Tree := .node t1147_1156 ⟨5,true,44,25⟩ t1157_1165
def t1128_1165 : Tree := .node t1128_1146 ⟨5,true,40,41⟩ t1147_1165
def t1166_1175 : Tree := (.node (.node (.node (.node .empty ⟨5,true,45,50⟩ .empty) ⟨5,true,45,55⟩ .empty) ⟨5,true,45,60⟩ (.node .empty ⟨5,true,45,70⟩ .empty)) ⟨5,true,46,0⟩ (.node (.node (.node .empty ⟨5,true,46,3⟩ .empty) ⟨5,true,46,11⟩ .empty) ⟨5,true,46,12⟩ (.node .empty ⟨5,true,46,25⟩ .empty)))
def t1176_1184 : Tree := (.node (.node (.node (.node .empty ⟨5,true,46,30⟩ .empty) ⟨5,true,46,31⟩ .empty) ⟨5,true,46,36⟩ (.node .empty ⟨5,true,46,40⟩ .empty)) ⟨5,true,46,50⟩ (.node (.node .empty ⟨5,true,46,51⟩ .empty) ⟨5,true,46,55⟩ (.node .empty ⟨5,true,46,56⟩ .empty)))
def t1166_1184 : Tree := .node t1166_1175 ⟨5,true,46,26⟩ t1176_1184
def t1185_1193 : Tree := (.node (.node (.node (.node .empty ⟨5,true,46,65⟩ .empty) ⟨5,true,46,71⟩ .empty) ⟨5,true,46,75⟩ (.node .empty ⟨5,true,47,25⟩ .empty)) ⟨5,true,47,30⟩ (.node (.node .empty ⟨5,true,48,11⟩ .empty) ⟨5,true,48,25⟩ (.node .empty ⟨5,true,49,3⟩ .empty)))
def t1194_1202 : Tree := (.node (.node (.node (.node .empty ⟨5,true,50,4⟩ .empty) ⟨5,true,50,26⟩ .empty) ⟨5,true,50,31⟩ (.node .empty ⟨5,true,50,41⟩ .empty)) ⟨5,true,50,51⟩ (.node (.node .empty ⟨5,true,50,56⟩ .empty) ⟨5,true,50,66⟩ (.node .empty ⟨5,true,50,76⟩ .empty)))
def t1185_1202 : Tree := .node t1185_1193 ⟨5,true,49,11⟩ t1194_1202
def t1166_1202 : Tree := .node t1166_1184 ⟨5,true,46,61⟩ t1185_1202
def t1128_1202 : Tree := .node t1128_1165 ⟨5,true,45,35⟩ t1166_1202
def t1053_1202 : Tree := .node t1053_1127 ⟨5,true,37,70⟩ t1128_1202
def t903_1202 : Tree := .node t903_1052 ⟨5,true,5,45⟩ t1053_1202
def t602_1202 : Tree := .node t602_902 ⟨4,true,39,50⟩ t903_1202
def t0_1202 : Tree := .node t0_601 ⟨3,false,45,24⟩ t602_1202
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 14, 11, 5, 0, 0, 7, 6, 13, 9, 31, 8, 41, 16, 10, 0, 0, 0, 0, 12, 0, 0, 0, 0, 15, 0, 0, 0, 18, 17, 30, 33, 28, 19, 25, 20, 23, 21, 27, 22, 24, 9, 0, 12, 0, 0, 0, 26, 0, 0, 0, 0, 0, 29, 0, 0, 0, 39, 0, 32, 0, 0, 34, 36, 0, 35, 0, 0, 40, 37, 38, 44, 0, 43, 0, 0, 0, 51, 0, 42, 0, 0, 0, 0, 50, 45, 46, 44, 28, 47, 25, 48, 23, 49, 27, 22, 0, 51, 0, 0],#[0, 1, 3, 2, 11, 10, 4, 6, 5, 0, 0, 0, 8, 7, 0, 0, 9, 0, 0, 0, 25, 24, 12, 14, 13, 0, 0, 0, 16, 15, 20, 19, 17, 7, 18, 0, 0, 0, 0, 0, 21, 23, 22, 0, 0, 0, 8, 7, 30, 29, 26, 28, 27, 0, 0, 0, 35, 34, 50, 49, 31, 33, 32, 0, 0, 0, 35, 34, 40, 39, 36, 38, 37, 0, 0, 0, 0, 0, 60, 59, 41, 43, 42, 0, 0, 0, 45, 44, 0, 0, 46, 48, 47, 0, 0, 0, 16, 15, 55, 54, 51, 53, 52, 0, 0, 0, 0, 0, 55, 54, 56, 58, 57, 0, 0, 0, 45, 44, 65, 64, 61, 63, 62, 0, 0, 0, 0, 0, 70, 69, 66, 68, 67, 0, 0, 0, 0, 0, 75, 74, 71, 73, 72, 0, 0, 0, 0, 0, 70, 69, 76, 78, 77, 0, 0, 0, 45, 44],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,3)],[(true,5)],[(false,5)],[(true,7)],[(true,6),(true,22)],[(false,9)],[(false,3)],[(true,11),(true,23)],[(false,6)],[(true,2)],[(false,14)],[(true,8)],[(true,16)],[(false,16)],[(true,18)],[(true,19)],[(true,20)],[(true,21),(true,49)],[(false,20),(false,48)],[(false,22)],[(false,19),(false,47)],[(true,25)],[(false,21),(false,49)],[(false,18),(false,46)],[(true,28)],[(false,17)],[(false,7)],[(true,31)],[(true,17)],[(false,33)],[(true,34)],[(true,33)],[(true,36)],[(false,37)],[(true,30)],[(false,36)],[(false,8)],[(true,41)],[(true,38)],[(true,37),(true,45)],[(true,44)],[(false,45)],[(true,46)],[(true,47)],[(true,48)],[(false,44)],[(true,40),(true,50)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(false,4)],[(true,3)],[(true,6),(true,16),(true,23)],[(false,6),(false,23)],[(false,8)],[(true,2)],[(false,2)],[(false,11)],[(false,12)],[(true,11)],[(true,14),(true,48)],[(false,14),(false,48)],[(false,16)],[(false,17)],[(true,15)],[(false,15)],[(false,20)],[(false,21)],[(true,20)],[(true,10)],[(false,10)],[(false,25)],[(false,26)],[(true,25)],[(true,24)],[(false,24)],[(false,30)],[(false,31)],[(true,30)],[(true,28),(true,33)],[(false,28),(false,33)],[(false,35)],[(false,36)],[(true,35)],[(true,34)],[(false,34)],[(false,40)],[(false,41)],[(true,40)],[(true,43),(true,58),(true,78)],[(false,43),(false,58),(false,78)],[(false,45)],[(false,46)],[(true,45)],[(true,29)],[(false,29)],[(false,50)],[(false,51)],[(true,50)],[(true,49),(true,54)],[(false,49),(false,54)],[(false,55)],[(false,56)],[(true,55)],[(true,39)],[(false,39)],[(false,60)],[(false,61)],[(true,60)],[(true,59)],[(false,59)],[(false,65)],[(false,66)],[(true,65)],[(true,64),(true,74)],[(false,64),(false,74)],[(false,70)],[(false,71)],[(true,70)],[(true,69)],[(false,69)],[(false,75)],[(false,76)],[(true,75)]],
  t0_1202⟩
theorem check0_9 : t0_9.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check10_18 : t10_18.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node9 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,8,57⟩ = true := by decide
theorem check0_18 : t0_18.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node9 check0_9 check10_18
theorem check19_28 : t19_28.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check29_37 : t29_37.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node28 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,18,27⟩ = true := by decide
theorem check19_37 : t19_37.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node28 check19_28 check29_37
theorem node18 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,16,72⟩ = true := by decide
theorem check0_37 : t0_37.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node18 check0_18 check19_37
theorem check38_47 : t38_47.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check48_56 : t48_56.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node47 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,36,27⟩ = true := by decide
theorem check38_56 : t38_56.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node47 check38_47 check48_56
theorem check57_66 : t57_66.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check67_75 : t67_75.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node66 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,37,66⟩ = true := by decide
theorem check57_75 : t57_75.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node66 check57_66 check67_75
theorem node56 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,37,26⟩ = true := by decide
theorem check38_75 : t38_75.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node56 check38_56 check57_75
theorem node37 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,33,37⟩ = true := by decide
theorem check0_75 : t0_75.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node37 check0_37 check38_75
theorem check76_85 : t76_85.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check86_94 : t86_94.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node85 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,45,37⟩ = true := by decide
theorem check76_94 : t76_94.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node85 check76_85 check86_94
theorem check95_104 : t95_104.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check105_113 : t105_113.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node104 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,3,12⟩ = true := by decide
theorem check95_113 : t95_113.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node104 check95_104 check105_113
theorem node94 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,45,76⟩ = true := by decide
theorem check76_113 : t76_113.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node94 check76_94 check95_113
theorem check114_123 : t114_123.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check124_132 : t124_132.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node123 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,17,51⟩ = true := by decide
theorem check114_132 : t114_132.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node123 check114_123 check124_132
theorem check133_141 : t133_141.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check142_150 : t142_150.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node141 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,33,66⟩ = true := by decide
theorem check133_150 : t133_150.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node141 check133_141 check142_150
theorem node132 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,19,26⟩ = true := by decide
theorem check114_150 : t114_150.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node132 check114_132 check133_150
theorem node113 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,8,36⟩ = true := by decide
theorem check76_150 : t76_150.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node113 check76_113 check114_150
theorem node75 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,44,67⟩ = true := by decide
theorem check0_150 : t0_150.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node75 check0_75 check76_150
theorem check151_160 : t151_160.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check161_169 : t161_169.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node160 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,44,36⟩ = true := by decide
theorem check151_169 : t151_169.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node160 check151_160 check161_169
theorem check170_179 : t170_179.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check180_188 : t180_188.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node179 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,49,4⟩ = true := by decide
theorem check170_188 : t170_188.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node179 check170_179 check180_188
theorem node169 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,45,51⟩ = true := by decide
theorem check151_188 : t151_188.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node169 check151_169 check170_188
theorem check189_198 : t189_198.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check199_207 : t199_207.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node198 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,16,56⟩ = true := by decide
theorem check189_207 : t189_207.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node198 check189_198 check199_207
theorem check208_216 : t208_216.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check217_225 : t217_225.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node216 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,33,31⟩ = true := by decide
theorem check208_225 : t208_225.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node216 check208_216 check217_225
theorem node207 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,17,71⟩ = true := by decide
theorem check189_225 : t189_225.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node207 check189_207 check208_225
theorem node188 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,5,42⟩ = true := by decide
theorem check151_225 : t151_225.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node188 check151_188 check189_225
theorem check226_235 : t226_235.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check236_244 : t236_244.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node235 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,37,4⟩ = true := by decide
theorem check226_244 : t226_244.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node235 check226_235 check236_244
theorem check245_254 : t245_254.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check255_263 : t255_263.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node254 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,44,51⟩ = true := by decide
theorem check245_263 : t245_263.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node254 check245_254 check255_263
theorem node244 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,44,3⟩ = true := by decide
theorem check226_263 : t226_263.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node244 check226_244 check245_263
theorem check264_273 : t264_273.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check274_282 : t274_282.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node273 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,48,4⟩ = true := by decide
theorem check264_282 : t264_282.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node273 check264_273 check274_282
theorem check283_291 : t283_291.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check292_300 : t292_300.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node291 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,16,52⟩ = true := by decide
theorem check283_300 : t283_300.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node291 check283_291 check292_300
theorem node282 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,7,57⟩ = true := by decide
theorem check264_300 : t264_300.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node282 check264_282 check283_300
theorem node263 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,45,27⟩ = true := by decide
theorem check226_300 : t226_300.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node263 check226_263 check264_300
theorem node225 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,36,31⟩ = true := by decide
theorem check151_300 : t151_300.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node225 check151_225 check226_300
theorem node150 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,37,4⟩ = true := by decide
theorem check0_300 : t0_300.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node150 check0_150 check151_300
theorem check301_310 : t301_310.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check311_319 : t311_319.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node310 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,33,32⟩ = true := by decide
theorem check301_319 : t301_319.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node310 check301_310 check311_319
theorem check320_329 : t320_329.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check330_338 : t330_338.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node329 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,37,62⟩ = true := by decide
theorem check320_338 : t320_338.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node329 check320_329 check330_338
theorem node319 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,36,42⟩ = true := by decide
theorem check301_338 : t301_338.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node319 check301_319 check320_338
theorem check339_348 : t339_348.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check349_357 : t349_357.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node348 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,47,5⟩ = true := by decide
theorem check339_357 : t339_357.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node348 check339_348 check349_357
theorem check358_367 : t358_367.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check368_376 : t368_376.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node367 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,17,26⟩ = true := by decide
theorem check358_376 : t358_376.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node367 check358_367 check368_376
theorem node357 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,6,3⟩ = true := by decide
theorem check339_376 : t339_376.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node357 check339_357 check358_376
theorem node338 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,44,77⟩ = true := by decide
theorem check301_376 : t301_376.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node338 check301_338 check339_376
theorem check377_386 : t377_386.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check387_395 : t387_395.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node386 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,33,69⟩ = true := by decide
theorem check377_395 : t377_395.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node386 check377_386 check387_395
theorem check396_405 : t396_405.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check406_414 : t406_414.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node405 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,37,59⟩ = true := by decide
theorem check396_414 : t396_414.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node405 check396_405 check406_414
theorem node395 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,37,11⟩ = true := by decide
theorem check377_414 : t377_414.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node395 check377_395 check396_414
theorem check415_424 : t415_424.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check425_433 : t425_433.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node424 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,45,24⟩ = true := by decide
theorem check415_433 : t415_433.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node424 check415_424 check425_433
theorem check434_442 : t434_442.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check443_451 : t443_451.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node442 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,1,6⟩ = true := by decide
theorem check434_451 : t434_451.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node442 check434_442 check443_451
theorem node433 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,45,55⟩ = true := by decide
theorem check415_451 : t415_451.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node433 check415_433 check434_451
theorem node414 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,44,40⟩ = true := by decide
theorem check377_451 : t377_451.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node414 check377_414 check415_451
theorem node376 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,21,11⟩ = true := by decide
theorem check301_451 : t301_451.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node376 check301_376 check377_451
theorem check452_461 : t452_461.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check462_470 : t462_470.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node461 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,13,40⟩ = true := by decide
theorem check452_470 : t452_470.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node461 check452_461 check462_470
theorem check471_480 : t471_480.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check481_489 : t481_489.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node480 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,18,54⟩ = true := by decide
theorem check471_489 : t471_489.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node480 check471_480 check481_489
theorem node470 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,16,69⟩ = true := by decide
theorem check452_489 : t452_489.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node470 check452_470 check471_489
theorem check490_499 : t490_499.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check500_508 : t500_508.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node499 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,23,10⟩ = true := by decide
theorem check490_508 : t490_508.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node499 check490_499 check500_508
theorem check509_517 : t509_517.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check518_526 : t518_526.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node517 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,32,70⟩ = true := by decide
theorem check509_526 : t509_526.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node517 check509_517 check518_526
theorem node508 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,30,25⟩ = true := by decide
theorem check490_526 : t490_526.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node508 check490_508 check509_526
theorem node489 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,19,60⟩ = true := by decide
theorem check452_526 : t452_526.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node489 check452_489 check490_526
theorem check527_536 : t527_536.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check537_545 : t537_545.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node536 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,35,70⟩ = true := by decide
theorem check527_545 : t527_545.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node536 check527_536 check537_545
theorem check546_555 : t546_555.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check556_564 : t556_564.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node555 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,38,28⟩ = true := by decide
theorem check546_564 : t546_564.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node555 check546_555 check556_564
theorem node545 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,37,24⟩ = true := by decide
theorem check527_564 : t527_564.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node545 check527_545 check546_564
theorem check565_574 : t565_574.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check575_583 : t575_583.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node574 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,40,49⟩ = true := by decide
theorem check565_583 : t565_583.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node574 check565_574 check575_583
theorem check584_592 : t584_592.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check593_601 : t593_601.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node592 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,44,29⟩ = true := by decide
theorem check584_601 : t584_601.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node592 check584_592 check593_601
theorem node583 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,43,30⟩ = true := by decide
theorem check565_601 : t565_601.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node583 check565_583 check584_601
theorem node564 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,39,30⟩ = true := by decide
theorem check527_601 : t527_601.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node564 check527_564 check565_601
theorem node526 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,34,49⟩ = true := by decide
theorem check452_601 : t452_601.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node526 check452_526 check527_601
theorem node451 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,4,20⟩ = true := by decide
theorem check301_601 : t301_601.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node451 check301_451 check452_601
theorem node300 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,17,52⟩ = true := by decide
theorem check0_601 : t0_601.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node300 check0_300 check301_601
theorem check602_611 : t602_611.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check612_620 : t612_620.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node611 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,46,24⟩ = true := by decide
theorem check602_620 : t602_620.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node611 check602_611 check612_620
theorem check621_630 : t621_630.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check631_639 : t631_639.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node630 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,49,10⟩ = true := by decide
theorem check621_639 : t621_639.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node630 check621_630 check631_639
theorem node620 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,47,11⟩ = true := by decide
theorem check602_639 : t602_639.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node620 check602_620 check621_639
theorem check640_649 : t640_649.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check650_658 : t650_658.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node649 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,51,75⟩ = true := by decide
theorem check640_658 : t640_658.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node649 check640_649 check650_658
theorem check659_668 : t659_668.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check669_677 : t669_677.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node668 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,16,69⟩ = true := by decide
theorem check659_677 : t659_677.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node668 check659_668 check669_677
theorem node658 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,6,2⟩ = true := by decide
theorem check640_677 : t640_677.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node658 check640_658 check659_677
theorem node639 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,50,54⟩ = true := by decide
theorem check602_677 : t602_677.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node639 check602_639 check640_677
theorem check678_687 : t678_687.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check688_696 : t688_696.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node687 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,21,10⟩ = true := by decide
theorem check678_696 : t678_696.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node687 check678_687 check688_696
theorem check697_706 : t697_706.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check707_715 : t707_715.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node706 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,33,54⟩ = true := by decide
theorem check697_715 : t697_715.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node706 check697_706 check707_715
theorem node696 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,30,43⟩ = true := by decide
theorem check678_715 : t678_715.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node696 check678_696 check697_715
theorem check716_725 : t716_725.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check726_734 : t726_734.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node725 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,36,49⟩ = true := by decide
theorem check716_734 : t716_734.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node725 check716_725 check726_734
theorem check735_743 : t735_743.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check744_752 : t744_752.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node743 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,38,49⟩ = true := by decide
theorem check735_752 : t735_752.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node743 check735_743 check744_752
theorem node734 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,37,59⟩ = true := by decide
theorem check716_752 : t716_752.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node734 check716_734 check735_752
theorem node715 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,34,53⟩ = true := by decide
theorem check678_752 : t678_752.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node715 check678_715 check716_752
theorem node677 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,18,58⟩ = true := by decide
theorem check602_752 : t602_752.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node677 check602_677 check678_752
theorem check753_762 : t753_762.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check763_771 : t763_771.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node762 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,41,78⟩ = true := by decide
theorem check753_771 : t753_771.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node762 check753_762 check763_771
theorem check772_781 : t772_781.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check782_790 : t782_790.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node781 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,46,10⟩ = true := by decide
theorem check772_790 : t772_790.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node781 check772_781 check782_790
theorem node771 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,45,10⟩ = true := by decide
theorem check753_790 : t753_790.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node771 check753_771 check772_790
theorem check791_800 : t791_800.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check801_809 : t801_809.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node800 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,48,24⟩ = true := by decide
theorem check791_809 : t791_809.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node800 check791_800 check801_809
theorem check810_818 : t810_818.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check819_827 : t819_827.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node818 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,47,0⟩ = true := by decide
theorem check810_827 : t810_827.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node818 check810_818 check819_827
theorem node809 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,50,68⟩ = true := by decide
theorem check791_827 : t791_827.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node809 check791_809 check810_827
theorem node790 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,46,53⟩ = true := by decide
theorem check753_827 : t753_827.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node790 check753_790 check791_827
theorem check828_837 : t828_837.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check838_846 : t838_846.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node837 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,17,28⟩ = true := by decide
theorem check828_846 : t828_846.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node837 check828_837 check838_846
theorem check847_856 : t847_856.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check857_865 : t857_865.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node856 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,22,1⟩ = true := by decide
theorem check847_865 : t847_865.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node856 check847_856 check857_865
theorem node846 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,19,50⟩ = true := by decide
theorem check828_865 : t828_865.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node846 check828_846 check847_865
theorem check866_875 : t866_875.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check876_884 : t876_884.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node875 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,35,35⟩ = true := by decide
theorem check866_884 : t866_884.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node875 check866_875 check876_884
theorem check885_893 : t885_893.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check894_902 : t894_902.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node893 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,37,29⟩ = true := by decide
theorem check885_902 : t885_902.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node893 check885_893 check894_902
theorem node884 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,36,24⟩ = true := by decide
theorem check866_902 : t866_902.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node884 check866_884 check885_902
theorem node865 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,33,29⟩ = true := by decide
theorem check828_902 : t828_902.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node865 check828_865 check866_902
theorem node827 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,6,78⟩ = true := by decide
theorem check753_902 : t753_902.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node827 check753_827 check828_902
theorem node752 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,40,28⟩ = true := by decide
theorem check602_902 : t602_902.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node752 check602_752 check753_902
theorem check903_912 : t903_912.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check913_921 : t913_921.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node912 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,43,11⟩ = true := by decide
theorem check903_921 : t903_921.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node912 check903_912 check913_921
theorem check922_931 : t922_931.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check932_940 : t932_940.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node931 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,44,39⟩ = true := by decide
theorem check922_940 : t922_940.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node931 check922_931 check932_940
theorem node921 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,43,55⟩ = true := by decide
theorem check903_940 : t903_940.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node921 check903_921 check922_940
theorem check941_950 : t941_950.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check951_959 : t951_959.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node950 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,47,24⟩ = true := by decide
theorem check941_959 : t941_959.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node950 check941_950 check951_959
theorem check960_968 : t960_968.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check969_977 : t969_977.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node968 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,51,3⟩ = true := by decide
theorem check960_977 : t960_977.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node968 check960_968 check969_977
theorem node959 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,47,55⟩ = true := by decide
theorem check941_977 : t941_977.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node959 check941_959 check960_977
theorem node940 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,45,34⟩ = true := by decide
theorem check903_977 : t903_977.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node940 check903_940 check941_977
theorem check978_987 : t978_987.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check988_996 : t988_996.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node987 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,18,61⟩ = true := by decide
theorem check978_996 : t978_996.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node987 check978_987 check988_996
theorem check997_1006 : t997_1006.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1007_1015 : t1007_1015.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1006 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,34,31⟩ = true := by decide
theorem check997_1015 : t997_1015.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1006 check997_1006 check1007_1015
theorem node996 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,30,31⟩ = true := by decide
theorem check978_1015 : t978_1015.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node996 check978_996 check997_1015
theorem check1016_1025 : t1016_1025.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1026_1034 : t1026_1034.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1025 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,40,66⟩ = true := by decide
theorem check1016_1034 : t1016_1034.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1025 check1016_1025 check1026_1034
theorem check1035_1043 : t1035_1043.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1044_1052 : t1044_1052.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1043 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,50,56⟩ = true := by decide
theorem check1035_1052 : t1035_1052.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1043 check1035_1043 check1044_1052
theorem node1034 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,46,51⟩ = true := by decide
theorem check1016_1052 : t1016_1052.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1034 check1016_1034 check1035_1052
theorem node1015 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,38,51⟩ = true := by decide
theorem check978_1052 : t978_1052.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1015 check978_1015 check1016_1052
theorem node977 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,7,0⟩ = true := by decide
theorem check903_1052 : t903_1052.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node977 check903_977 check978_1052
theorem check1053_1062 : t1053_1062.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1063_1071 : t1063_1071.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1062 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,17,50⟩ = true := by decide
theorem check1053_1071 : t1053_1071.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1062 check1053_1062 check1063_1071
theorem check1072_1081 : t1072_1081.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1082_1090 : t1082_1090.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1081 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,23,4⟩ = true := by decide
theorem check1072_1090 : t1072_1090.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1081 check1072_1081 check1082_1090
theorem node1071 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,18,61⟩ = true := by decide
theorem check1053_1090 : t1053_1090.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1071 check1053_1071 check1072_1090
theorem check1091_1100 : t1091_1100.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1101_1109 : t1101_1109.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1100 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,33,70⟩ = true := by decide
theorem check1091_1109 : t1091_1109.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1100 check1091_1100 check1101_1109
theorem check1110_1118 : t1110_1118.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1119_1127 : t1119_1127.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1118 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,36,55⟩ = true := by decide
theorem check1110_1127 : t1110_1127.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1118 check1110_1118 check1119_1127
theorem node1109 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,34,56⟩ = true := by decide
theorem check1091_1127 : t1091_1127.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1109 check1091_1109 check1110_1127
theorem node1090 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,30,56⟩ = true := by decide
theorem check1053_1127 : t1053_1127.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1090 check1053_1090 check1091_1127
theorem check1128_1137 : t1128_1137.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1138_1146 : t1138_1146.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1137 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,38,55⟩ = true := by decide
theorem check1128_1146 : t1128_1146.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1137 check1128_1137 check1138_1146
theorem check1147_1156 : t1147_1156.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1157_1165 : t1157_1165.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1156 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,44,25⟩ = true := by decide
theorem check1147_1165 : t1147_1165.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1156 check1147_1156 check1157_1165
theorem node1146 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,40,41⟩ = true := by decide
theorem check1128_1165 : t1128_1165.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1146 check1128_1146 check1147_1165
theorem check1166_1175 : t1166_1175.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1176_1184 : t1176_1184.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1175 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,46,26⟩ = true := by decide
theorem check1166_1184 : t1166_1184.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1175 check1166_1175 check1176_1184
theorem check1185_1193 : t1185_1193.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1194_1202 : t1194_1202.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1193 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,49,11⟩ = true := by decide
theorem check1185_1202 : t1185_1202.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1193 check1185_1193 check1194_1202
theorem node1184 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,46,61⟩ = true := by decide
theorem check1166_1202 : t1166_1202.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1184 check1166_1184 check1185_1202
theorem node1165 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,45,35⟩ = true := by decide
theorem check1128_1202 : t1128_1202.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1165 check1128_1165 check1166_1202
theorem node1127 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,37,70⟩ = true := by decide
theorem check1053_1202 : t1053_1202.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1127 check1053_1127 check1128_1202
theorem node1052 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,5,45⟩ = true := by decide
theorem check903_1202 : t903_1202.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1052 check903_1052 check1053_1202
theorem node902 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,39,50⟩ = true := by decide
theorem check602_1202 : t602_1202.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node902 check602_902 check903_1202
theorem node601 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,45,24⟩ = true := by decide
theorem check0_1202 : t0_1202.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node601 check0_601 check602_1202
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_1202
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M009
