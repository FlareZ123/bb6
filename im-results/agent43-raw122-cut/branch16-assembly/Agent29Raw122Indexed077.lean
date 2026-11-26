import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M077
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
def t0_9 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,3,3⟩ .empty) ⟨0,false,3,5⟩ (.node .empty ⟨0,false,3,7⟩ .empty)) ⟨0,false,3,9⟩ (.node (.node (.node .empty ⟨0,false,3,10⟩ .empty) ⟨0,false,3,13⟩ .empty) ⟨0,false,3,14⟩ (.node .empty ⟨0,false,3,16⟩ .empty)))
def t10_19 : Tree := (.node (.node (.node (.node .empty ⟨0,false,3,22⟩ .empty) ⟨0,false,3,23⟩ .empty) ⟨0,false,3,25⟩ (.node .empty ⟨0,false,3,30⟩ .empty)) ⟨0,false,4,3⟩ (.node (.node (.node .empty ⟨0,false,4,4⟩ .empty) ⟨0,false,4,5⟩ .empty) ⟨0,false,4,15⟩ (.node .empty ⟨0,false,4,16⟩ .empty)))
def t0_19 : Tree := .node t0_9 ⟨0,false,3,21⟩ t10_19
def t20_29 : Tree := (.node (.node (.node (.node .empty ⟨0,false,4,23⟩ .empty) ⟨0,false,8,0⟩ .empty) ⟨0,false,8,1⟩ (.node .empty ⟨0,false,8,3⟩ .empty)) ⟨0,false,8,4⟩ (.node (.node (.node .empty ⟨0,false,8,5⟩ .empty) ⟨0,false,8,6⟩ .empty) ⟨0,false,8,7⟩ (.node .empty ⟨0,false,8,9⟩ .empty)))
def t30_38 : Tree := (.node (.node (.node (.node .empty ⟨0,false,8,11⟩ .empty) ⟨0,false,8,13⟩ .empty) ⟨0,false,8,14⟩ (.node .empty ⟨0,false,8,15⟩ .empty)) ⟨0,false,8,16⟩ (.node (.node .empty ⟨0,false,8,18⟩ .empty) ⟨0,false,8,20⟩ (.node .empty ⟨0,false,8,21⟩ .empty)))
def t20_38 : Tree := .node t20_29 ⟨0,false,8,10⟩ t30_38
def t0_38 : Tree := .node t0_19 ⟨0,false,4,21⟩ t20_38
def t39_48 : Tree := (.node (.node (.node (.node .empty ⟨0,false,8,23⟩ .empty) ⟨0,false,8,25⟩ .empty) ⟨0,false,8,26⟩ (.node .empty ⟨0,false,8,27⟩ .empty)) ⟨0,false,8,30⟩ (.node (.node (.node .empty ⟨0,false,8,32⟩ .empty) ⟨0,false,8,34⟩ .empty) ⟨0,false,15,0⟩ (.node .empty ⟨0,false,15,1⟩ .empty)))
def t49_58 : Tree := (.node (.node (.node (.node .empty ⟨0,false,15,5⟩ .empty) ⟨0,false,15,9⟩ .empty) ⟨0,false,15,10⟩ (.node .empty ⟨0,false,15,13⟩ .empty)) ⟨0,false,15,14⟩ (.node (.node (.node .empty ⟨0,false,15,16⟩ .empty) ⟨0,false,15,18⟩ .empty) ⟨0,false,15,20⟩ (.node .empty ⟨0,false,15,21⟩ .empty)))
def t39_58 : Tree := .node t39_48 ⟨0,false,15,3⟩ t49_58
def t59_68 : Tree := (.node (.node (.node (.node .empty ⟨0,false,15,25⟩ .empty) ⟨0,false,15,32⟩ .empty) ⟨0,false,15,34⟩ (.node .empty ⟨0,false,17,0⟩ .empty)) ⟨0,false,17,1⟩ (.node (.node (.node .empty ⟨0,false,17,3⟩ .empty) ⟨0,false,17,4⟩ .empty) ⟨0,false,17,5⟩ (.node .empty ⟨0,false,17,6⟩ .empty)))
def t69_77 : Tree := (.node (.node (.node (.node .empty ⟨0,false,17,9⟩ .empty) ⟨0,false,17,10⟩ .empty) ⟨0,false,17,11⟩ (.node .empty ⟨0,false,17,13⟩ .empty)) ⟨0,false,17,14⟩ (.node (.node .empty ⟨0,false,17,15⟩ .empty) ⟨0,false,17,16⟩ (.node .empty ⟨0,false,17,18⟩ .empty)))
def t59_77 : Tree := .node t59_68 ⟨0,false,17,7⟩ t69_77
def t39_77 : Tree := .node t39_58 ⟨0,false,15,23⟩ t59_77
def t0_77 : Tree := .node t0_38 ⟨0,false,8,22⟩ t39_77
def t78_87 : Tree := (.node (.node (.node (.node .empty ⟨0,false,17,21⟩ .empty) ⟨0,false,17,22⟩ .empty) ⟨0,false,17,23⟩ (.node .empty ⟨0,false,17,25⟩ .empty)) ⟨0,false,17,26⟩ (.node (.node (.node .empty ⟨0,false,17,27⟩ .empty) ⟨0,false,17,30⟩ .empty) ⟨0,false,17,32⟩ (.node .empty ⟨0,false,17,34⟩ .empty)))
def t88_97 : Tree := (.node (.node (.node (.node .empty ⟨0,false,19,1⟩ .empty) ⟨0,false,19,3⟩ .empty) ⟨0,false,19,4⟩ (.node .empty ⟨0,false,19,5⟩ .empty)) ⟨0,false,19,6⟩ (.node (.node (.node .empty ⟨0,false,19,7⟩ .empty) ⟨0,false,19,9⟩ .empty) ⟨0,false,19,10⟩ (.node .empty ⟨0,false,19,11⟩ .empty)))
def t78_97 : Tree := .node t78_87 ⟨0,false,19,0⟩ t88_97
def t98_107 : Tree := (.node (.node (.node (.node .empty ⟨0,false,19,14⟩ .empty) ⟨0,false,19,15⟩ .empty) ⟨0,false,19,16⟩ (.node .empty ⟨0,false,19,18⟩ .empty)) ⟨0,false,19,20⟩ (.node (.node (.node .empty ⟨0,false,19,21⟩ .empty) ⟨0,false,19,22⟩ .empty) ⟨0,false,19,23⟩ (.node .empty ⟨0,false,19,25⟩ .empty)))
def t108_116 : Tree := (.node (.node (.node (.node .empty ⟨0,false,19,27⟩ .empty) ⟨0,false,19,30⟩ .empty) ⟨0,false,19,32⟩ (.node .empty ⟨0,false,19,34⟩ .empty)) ⟨1,false,0,6⟩ (.node (.node .empty ⟨1,false,0,17⟩ .empty) ⟨1,false,1,0⟩ (.node .empty ⟨1,false,1,9⟩ .empty)))
def t98_116 : Tree := .node t98_107 ⟨0,false,19,26⟩ t108_116
def t78_116 : Tree := .node t78_97 ⟨0,false,19,13⟩ t98_116
def t117_126 : Tree := (.node (.node (.node (.node .empty ⟨1,false,1,17⟩ .empty) ⟨1,false,1,28⟩ .empty) ⟨1,false,1,31⟩ (.node .empty ⟨1,false,5,1⟩ .empty)) ⟨1,false,5,4⟩ (.node (.node (.node .empty ⟨1,false,5,15⟩ .empty) ⟨1,false,5,17⟩ .empty) ⟨1,false,5,20⟩ (.node .empty ⟨1,false,5,28⟩ .empty)))
def t127_136 : Tree := (.node (.node (.node (.node .empty ⟨1,false,5,34⟩ .empty) ⟨1,false,6,1⟩ .empty) ⟨1,false,6,3⟩ (.node .empty ⟨1,false,6,4⟩ .empty)) ⟨1,false,6,6⟩ (.node (.node (.node .empty ⟨1,false,6,9⟩ .empty) ⟨1,false,6,10⟩ .empty) ⟨1,false,6,13⟩ (.node .empty ⟨1,false,6,14⟩ .empty)))
def t117_136 : Tree := .node t117_126 ⟨1,false,5,31⟩ t127_136
def t137_146 : Tree := (.node (.node (.node (.node .empty ⟨1,false,6,17⟩ .empty) ⟨1,false,6,20⟩ .empty) ⟨1,false,6,21⟩ (.node .empty ⟨1,false,6,26⟩ .empty)) ⟨1,false,6,28⟩ (.node (.node (.node .empty ⟨1,false,6,31⟩ .empty) ⟨1,false,6,34⟩ .empty) ⟨1,false,9,0⟩ (.node .empty ⟨1,false,9,1⟩ .empty)))
def t147_155 : Tree := (.node (.node (.node (.node .empty ⟨1,false,9,4⟩ .empty) ⟨1,false,9,5⟩ .empty) ⟨1,false,9,6⟩ (.node .empty ⟨1,false,9,8⟩ .empty)) ⟨1,false,9,9⟩ (.node (.node .empty ⟨1,false,9,10⟩ .empty) ⟨1,false,9,12⟩ (.node .empty ⟨1,false,9,13⟩ .empty)))
def t137_155 : Tree := .node t137_146 ⟨1,false,9,3⟩ t147_155
def t117_155 : Tree := .node t117_136 ⟨1,false,6,15⟩ t137_155
def t78_155 : Tree := .node t78_116 ⟨1,false,1,15⟩ t117_155
def t0_155 : Tree := .node t0_77 ⟨0,false,17,20⟩ t78_155
def t156_165 : Tree := (.node (.node (.node (.node .empty ⟨1,false,9,15⟩ .empty) ⟨1,false,9,16⟩ .empty) ⟨1,false,9,17⟩ (.node .empty ⟨1,false,9,19⟩ .empty)) ⟨1,false,9,20⟩ (.node (.node (.node .empty ⟨1,false,9,21⟩ .empty) ⟨1,false,9,25⟩ .empty) ⟨1,false,9,26⟩ (.node .empty ⟨1,false,9,28⟩ .empty)))
def t166_175 : Tree := (.node (.node (.node (.node .empty ⟨1,false,9,33⟩ .empty) ⟨1,false,9,34⟩ .empty) ⟨1,false,10,0⟩ (.node .empty ⟨1,false,10,3⟩ .empty)) ⟨1,false,10,5⟩ (.node (.node (.node .empty ⟨1,false,10,8⟩ .empty) ⟨1,false,10,10⟩ .empty) ⟨1,false,10,12⟩ (.node .empty ⟨1,false,10,14⟩ .empty)))
def t156_175 : Tree := .node t156_165 ⟨1,false,9,31⟩ t166_175
def t176_185 : Tree := (.node (.node (.node (.node .empty ⟨1,false,10,19⟩ .empty) ⟨1,false,10,21⟩ .empty) ⟨1,false,10,25⟩ (.node .empty ⟨1,false,10,33⟩ .empty)) ⟨1,false,16,0⟩ (.node (.node (.node .empty ⟨1,false,16,1⟩ .empty) ⟨1,false,16,4⟩ .empty) ⟨1,false,16,6⟩ (.node .empty ⟨1,false,16,8⟩ .empty)))
def t186_194 : Tree := (.node (.node (.node (.node .empty ⟨1,false,16,12⟩ .empty) ⟨1,false,16,13⟩ .empty) ⟨1,false,16,15⟩ (.node .empty ⟨1,false,16,17⟩ .empty)) ⟨1,false,16,19⟩ (.node (.node .empty ⟨1,false,16,20⟩ .empty) ⟨1,false,16,26⟩ (.node .empty ⟨1,false,16,28⟩ .empty)))
def t176_194 : Tree := .node t176_185 ⟨1,false,16,9⟩ t186_194
def t156_194 : Tree := .node t156_175 ⟨1,false,10,16⟩ t176_194
def t195_204 : Tree := (.node (.node (.node (.node .empty ⟨1,false,16,33⟩ .empty) ⟨1,false,16,34⟩ .empty) ⟨1,false,20,0⟩ (.node .empty ⟨1,false,20,1⟩ .empty)) ⟨1,false,20,3⟩ (.node (.node (.node .empty ⟨1,false,20,4⟩ .empty) ⟨1,false,20,5⟩ .empty) ⟨1,false,20,6⟩ (.node .empty ⟨1,false,20,8⟩ .empty)))
def t205_214 : Tree := (.node (.node (.node (.node .empty ⟨1,false,20,10⟩ .empty) ⟨1,false,20,12⟩ .empty) ⟨1,false,20,13⟩ (.node .empty ⟨1,false,20,14⟩ .empty)) ⟨1,false,20,15⟩ (.node (.node (.node .empty ⟨1,false,20,16⟩ .empty) ⟨1,false,20,17⟩ .empty) ⟨1,false,20,19⟩ (.node .empty ⟨1,false,20,20⟩ .empty)))
def t195_214 : Tree := .node t195_204 ⟨1,false,20,9⟩ t205_214
def t215_224 : Tree := (.node (.node (.node (.node .empty ⟨1,false,20,25⟩ .empty) ⟨1,false,20,26⟩ .empty) ⟨1,false,20,28⟩ (.node .empty ⟨1,false,20,31⟩ .empty)) ⟨1,false,20,33⟩ (.node (.node (.node .empty ⟨1,false,20,34⟩ .empty) ⟨1,false,23,0⟩ .empty) ⟨1,false,23,3⟩ (.node .empty ⟨1,false,23,5⟩ .empty)))
def t225_233 : Tree := (.node (.node (.node (.node .empty ⟨1,false,23,10⟩ .empty) ⟨1,false,23,12⟩ .empty) ⟨1,false,23,14⟩ (.node .empty ⟨1,false,23,16⟩ .empty)) ⟨1,false,23,19⟩ (.node (.node .empty ⟨1,false,23,21⟩ .empty) ⟨1,false,23,25⟩ (.node .empty ⟨1,false,23,33⟩ .empty)))
def t215_233 : Tree := .node t215_224 ⟨1,false,23,8⟩ t225_233
def t195_233 : Tree := .node t195_214 ⟨1,false,20,21⟩ t215_233
def t156_233 : Tree := .node t156_194 ⟨1,false,16,31⟩ t195_233
def t234_243 : Tree := (.node (.node (.node (.node .empty ⟨1,true,0,15⟩ .empty) ⟨1,true,0,17⟩ .empty) ⟨1,true,0,28⟩ (.node .empty ⟨1,true,1,4⟩ .empty)) ⟨1,true,1,15⟩ (.node (.node (.node .empty ⟨1,true,1,17⟩ .empty) ⟨1,true,1,20⟩ .empty) ⟨1,true,1,28⟩ (.node .empty ⟨1,true,1,31⟩ .empty)))
def t244_253 : Tree := (.node (.node (.node (.node .empty ⟨1,true,5,3⟩ .empty) ⟨1,true,5,4⟩ .empty) ⟨1,true,5,6⟩ (.node .empty ⟨1,true,5,10⟩ .empty)) ⟨1,true,5,14⟩ (.node (.node (.node .empty ⟨1,true,5,15⟩ .empty) ⟨1,true,5,17⟩ .empty) ⟨1,true,5,20⟩ (.node .empty ⟨1,true,5,21⟩ .empty)))
def t234_253 : Tree := .node t234_243 ⟨1,true,5,1⟩ t244_253
def t254_263 : Tree := (.node (.node (.node (.node .empty ⟨1,true,5,28⟩ .empty) ⟨1,true,5,31⟩ .empty) ⟨1,true,5,34⟩ (.node .empty ⟨1,true,6,1⟩ .empty)) ⟨1,true,6,4⟩ (.node (.node (.node .empty ⟨1,true,6,6⟩ .empty) ⟨1,true,6,8⟩ .empty) ⟨1,true,6,9⟩ (.node .empty ⟨1,true,6,12⟩ .empty)))
def t264_272 : Tree := (.node (.node (.node (.node .empty ⟨1,true,6,15⟩ .empty) ⟨1,true,6,17⟩ .empty) ⟨1,true,6,20⟩ (.node .empty ⟨1,true,6,26⟩ .empty)) ⟨1,true,6,28⟩ (.node (.node .empty ⟨1,true,6,31⟩ .empty) ⟨1,true,6,34⟩ (.node .empty ⟨1,true,9,0⟩ .empty)))
def t254_272 : Tree := .node t254_263 ⟨1,true,6,13⟩ t264_272
def t234_272 : Tree := .node t234_253 ⟨1,true,5,26⟩ t254_272
def t273_282 : Tree := (.node (.node (.node (.node .empty ⟨1,true,9,3⟩ .empty) ⟨1,true,9,4⟩ .empty) ⟨1,true,9,5⟩ (.node .empty ⟨1,true,9,6⟩ .empty)) ⟨1,true,9,8⟩ (.node (.node (.node .empty ⟨1,true,9,9⟩ .empty) ⟨1,true,9,10⟩ .empty) ⟨1,true,9,12⟩ (.node .empty ⟨1,true,9,13⟩ .empty)))
def t283_291 : Tree := (.node (.node (.node (.node .empty ⟨1,true,9,15⟩ .empty) ⟨1,true,9,16⟩ .empty) ⟨1,true,9,17⟩ (.node .empty ⟨1,true,9,19⟩ .empty)) ⟨1,true,9,20⟩ (.node (.node .empty ⟨1,true,9,21⟩ .empty) ⟨1,true,9,25⟩ (.node .empty ⟨1,true,9,26⟩ .empty)))
def t273_291 : Tree := .node t273_282 ⟨1,true,9,14⟩ t283_291
def t292_301 : Tree := (.node (.node (.node (.node .empty ⟨1,true,9,31⟩ .empty) ⟨1,true,9,33⟩ .empty) ⟨1,true,9,34⟩ (.node .empty ⟨1,true,10,0⟩ .empty)) ⟨1,true,10,3⟩ (.node (.node (.node .empty ⟨1,true,10,5⟩ .empty) ⟨1,true,10,8⟩ .empty) ⟨1,true,10,10⟩ (.node .empty ⟨1,true,10,12⟩ .empty)))
def t302_310 : Tree := (.node (.node (.node (.node .empty ⟨1,true,10,16⟩ .empty) ⟨1,true,10,19⟩ .empty) ⟨1,true,10,21⟩ (.node .empty ⟨1,true,10,25⟩ .empty)) ⟨1,true,10,33⟩ (.node (.node .empty ⟨1,true,11,0⟩ .empty) ⟨1,true,11,3⟩ (.node .empty ⟨1,true,11,5⟩ .empty)))
def t292_310 : Tree := .node t292_301 ⟨1,true,10,14⟩ t302_310
def t273_310 : Tree := .node t273_291 ⟨1,true,9,28⟩ t292_310
def t234_310 : Tree := .node t234_272 ⟨1,true,9,1⟩ t273_310
def t156_310 : Tree := .node t156_233 ⟨1,true,0,9⟩ t234_310
def t0_310 : Tree := .node t0_155 ⟨1,false,9,14⟩ t156_310
def t311_320 : Tree := (.node (.node (.node (.node .empty ⟨1,true,11,10⟩ .empty) ⟨1,true,11,12⟩ .empty) ⟨1,true,11,14⟩ (.node .empty ⟨1,true,11,16⟩ .empty)) ⟨1,true,11,19⟩ (.node (.node (.node .empty ⟨1,true,11,21⟩ .empty) ⟨1,true,11,25⟩ .empty) ⟨1,true,11,33⟩ (.node .empty ⟨1,true,13,0⟩ .empty)))
def t321_330 : Tree := (.node (.node (.node (.node .empty ⟨1,true,13,5⟩ .empty) ⟨1,true,13,8⟩ .empty) ⟨1,true,13,10⟩ (.node .empty ⟨1,true,13,12⟩ .empty)) ⟨1,true,13,14⟩ (.node (.node (.node .empty ⟨1,true,13,16⟩ .empty) ⟨1,true,13,19⟩ .empty) ⟨1,true,13,21⟩ (.node .empty ⟨1,true,13,25⟩ .empty)))
def t311_330 : Tree := .node t311_320 ⟨1,true,13,3⟩ t321_330
def t331_340 : Tree := (.node (.node (.node (.node .empty ⟨1,true,16,0⟩ .empty) ⟨1,true,16,1⟩ .empty) ⟨1,true,16,4⟩ (.node .empty ⟨1,true,16,6⟩ .empty)) ⟨1,true,16,8⟩ (.node (.node (.node .empty ⟨1,true,16,9⟩ .empty) ⟨1,true,16,12⟩ .empty) ⟨1,true,16,13⟩ (.node .empty ⟨1,true,16,15⟩ .empty)))
def t341_349 : Tree := (.node (.node (.node (.node .empty ⟨1,true,16,19⟩ .empty) ⟨1,true,16,20⟩ .empty) ⟨1,true,16,26⟩ (.node .empty ⟨1,true,16,28⟩ .empty)) ⟨1,true,16,31⟩ (.node (.node .empty ⟨1,true,16,33⟩ .empty) ⟨1,true,16,34⟩ (.node .empty ⟨1,true,20,0⟩ .empty)))
def t331_349 : Tree := .node t331_340 ⟨1,true,16,17⟩ t341_349
def t311_349 : Tree := .node t311_330 ⟨1,true,13,33⟩ t331_349
def t350_359 : Tree := (.node (.node (.node (.node .empty ⟨1,true,20,3⟩ .empty) ⟨1,true,20,4⟩ .empty) ⟨1,true,20,5⟩ (.node .empty ⟨1,true,20,6⟩ .empty)) ⟨1,true,20,8⟩ (.node (.node (.node .empty ⟨1,true,20,9⟩ .empty) ⟨1,true,20,10⟩ .empty) ⟨1,true,20,12⟩ (.node .empty ⟨1,true,20,13⟩ .empty)))
def t360_369 : Tree := (.node (.node (.node (.node .empty ⟨1,true,20,15⟩ .empty) ⟨1,true,20,16⟩ .empty) ⟨1,true,20,17⟩ (.node .empty ⟨1,true,20,19⟩ .empty)) ⟨1,true,20,20⟩ (.node (.node (.node .empty ⟨1,true,20,21⟩ .empty) ⟨1,true,20,25⟩ .empty) ⟨1,true,20,26⟩ (.node .empty ⟨1,true,20,28⟩ .empty)))
def t350_369 : Tree := .node t350_359 ⟨1,true,20,14⟩ t360_369
def t370_379 : Tree := (.node (.node (.node (.node .empty ⟨1,true,20,33⟩ .empty) ⟨1,true,20,34⟩ .empty) ⟨1,true,21,3⟩ (.node .empty ⟨1,true,21,5⟩ .empty)) ⟨1,true,21,10⟩ (.node (.node (.node .empty ⟨1,true,21,14⟩ .empty) ⟨1,true,21,16⟩ .empty) ⟨1,true,21,21⟩ (.node .empty ⟨1,true,21,25⟩ .empty)))
def t380_388 : Tree := (.node (.node (.node (.node .empty ⟨1,true,23,3⟩ .empty) ⟨1,true,23,5⟩ .empty) ⟨1,true,23,8⟩ (.node .empty ⟨1,true,23,10⟩ .empty)) ⟨1,true,23,12⟩ (.node (.node .empty ⟨1,true,23,14⟩ .empty) ⟨1,true,23,16⟩ (.node .empty ⟨1,true,23,19⟩ .empty)))
def t370_388 : Tree := .node t370_379 ⟨1,true,23,0⟩ t380_388
def t350_388 : Tree := .node t350_369 ⟨1,true,20,31⟩ t370_388
def t311_388 : Tree := .node t311_349 ⟨1,true,20,1⟩ t350_388
def t389_398 : Tree := (.node (.node (.node (.node .empty ⟨1,true,23,25⟩ .empty) ⟨1,true,23,33⟩ .empty) ⟨2,false,2,0⟩ (.node .empty ⟨2,false,7,1⟩ .empty)) ⟨2,false,7,9⟩ (.node (.node (.node .empty ⟨2,false,7,13⟩ .empty) ⟨2,false,7,20⟩ .empty) ⟨2,false,7,34⟩ (.node .empty ⟨2,false,10,0⟩ .empty)))
def t399_408 : Tree := (.node (.node (.node (.node .empty ⟨2,false,10,4⟩ .empty) ⟨2,false,10,6⟩ .empty) ⟨2,false,10,7⟩ (.node .empty ⟨2,false,10,9⟩ .empty)) ⟨2,false,10,11⟩ (.node (.node (.node .empty ⟨2,false,10,13⟩ .empty) ⟨2,false,10,15⟩ .empty) ⟨2,false,10,18⟩ (.node .empty ⟨2,false,10,20⟩ .empty)))
def t389_408 : Tree := .node t389_398 ⟨2,false,10,1⟩ t399_408
def t409_418 : Tree := (.node (.node (.node (.node .empty ⟨2,false,10,26⟩ .empty) ⟨2,false,10,27⟩ .empty) ⟨2,false,10,30⟩ (.node .empty ⟨2,false,10,32⟩ .empty)) ⟨2,false,10,34⟩ (.node (.node (.node .empty ⟨2,false,11,0⟩ .empty) ⟨2,false,11,1⟩ .empty) ⟨2,false,11,4⟩ (.node .empty ⟨2,false,11,6⟩ .empty)))
def t419_427 : Tree := (.node (.node (.node (.node .empty ⟨2,false,11,9⟩ .empty) ⟨2,false,11,11⟩ .empty) ⟨2,false,11,13⟩ (.node .empty ⟨2,false,11,15⟩ .empty)) ⟨2,false,11,18⟩ (.node (.node .empty ⟨2,false,11,20⟩ .empty) ⟨2,false,11,22⟩ (.node .empty ⟨2,false,11,26⟩ .empty)))
def t409_427 : Tree := .node t409_418 ⟨2,false,11,7⟩ t419_427
def t389_427 : Tree := .node t389_408 ⟨2,false,10,22⟩ t409_427
def t428_437 : Tree := (.node (.node (.node (.node .empty ⟨2,false,11,30⟩ .empty) ⟨2,false,11,32⟩ .empty) ⟨2,false,11,34⟩ (.node .empty ⟨2,false,18,0⟩ .empty)) ⟨2,false,18,7⟩ (.node (.node (.node .empty ⟨2,false,18,11⟩ .empty) ⟨2,false,18,18⟩ .empty) ⟨2,false,18,22⟩ (.node .empty ⟨2,false,18,27⟩ .empty)))
def t438_447 : Tree := (.node (.node (.node (.node .empty ⟨2,false,18,32⟩ .empty) ⟨2,false,24,0⟩ .empty) ⟨2,false,24,1⟩ (.node .empty ⟨2,false,24,4⟩ .empty)) ⟨2,false,24,6⟩ (.node (.node (.node .empty ⟨2,false,24,7⟩ .empty) ⟨2,false,24,9⟩ .empty) ⟨2,false,24,11⟩ (.node .empty ⟨2,false,24,13⟩ .empty)))
def t428_447 : Tree := .node t428_437 ⟨2,false,18,30⟩ t438_447
def t448_457 : Tree := (.node (.node (.node (.node .empty ⟨2,false,24,18⟩ .empty) ⟨2,false,24,20⟩ .empty) ⟨2,false,24,22⟩ (.node .empty ⟨2,false,24,26⟩ .empty)) ⟨2,false,24,27⟩ (.node (.node (.node .empty ⟨2,false,24,30⟩ .empty) ⟨2,false,24,32⟩ .empty) ⟨2,false,24,34⟩ (.node .empty ⟨2,true,1,5⟩ .empty)))
def t458_466 : Tree := (.node (.node (.node (.node .empty ⟨2,true,1,11⟩ .empty) ⟨2,true,1,16⟩ .empty) ⟨2,true,1,22⟩ (.node .empty ⟨2,true,1,29⟩ .empty)) ⟨2,true,2,7⟩ (.node (.node .empty ⟨2,true,2,8⟩ .empty) ⟨2,true,2,10⟩ (.node .empty ⟨2,true,2,11⟩ .empty)))
def t448_466 : Tree := .node t448_457 ⟨2,true,1,7⟩ t458_466
def t428_466 : Tree := .node t428_447 ⟨2,false,24,15⟩ t448_466
def t389_466 : Tree := .node t389_427 ⟨2,false,11,27⟩ t428_466
def t311_466 : Tree := .node t311_388 ⟨1,true,23,21⟩ t389_466
def t467_476 : Tree := (.node (.node (.node (.node .empty ⟨2,true,2,22⟩ .empty) ⟨2,true,2,27⟩ .empty) ⟨2,true,2,29⟩ (.node .empty ⟨2,true,2,30⟩ .empty)) ⟨2,true,7,0⟩ (.node (.node (.node .empty ⟨2,true,7,3⟩ .empty) ⟨2,true,7,5⟩ .empty) ⟨2,true,7,7⟩ (.node .empty ⟨2,true,7,8⟩ .empty)))
def t477_486 : Tree := (.node (.node (.node (.node .empty ⟨2,true,7,11⟩ .empty) ⟨2,true,7,12⟩ .empty) ⟨2,true,7,14⟩ (.node .empty ⟨2,true,7,16⟩ .empty)) ⟨2,true,7,19⟩ (.node (.node (.node .empty ⟨2,true,7,21⟩ .empty) ⟨2,true,7,22⟩ .empty) ⟨2,true,7,25⟩ (.node .empty ⟨2,true,7,27⟩ .empty)))
def t467_486 : Tree := .node t467_476 ⟨2,true,7,10⟩ t477_486
def t487_496 : Tree := (.node (.node (.node (.node .empty ⟨2,true,7,30⟩ .empty) ⟨2,true,7,33⟩ .empty) ⟨2,true,10,0⟩ (.node .empty ⟨2,true,10,3⟩ .empty)) ⟨2,true,10,5⟩ (.node (.node (.node .empty ⟨2,true,10,7⟩ .empty) ⟨2,true,10,8⟩ .empty) ⟨2,true,10,10⟩ (.node .empty ⟨2,true,10,11⟩ .empty)))
def t497_505 : Tree := (.node (.node (.node (.node .empty ⟨2,true,10,14⟩ .empty) ⟨2,true,10,16⟩ .empty) ⟨2,true,10,19⟩ (.node .empty ⟨2,true,10,21⟩ .empty)) ⟨2,true,10,22⟩ (.node (.node .empty ⟨2,true,10,25⟩ .empty) ⟨2,true,10,27⟩ (.node .empty ⟨2,true,10,29⟩ .empty)))
def t487_505 : Tree := .node t487_496 ⟨2,true,10,12⟩ t497_505
def t467_505 : Tree := .node t467_486 ⟨2,true,7,29⟩ t487_505
def t506_515 : Tree := (.node (.node (.node (.node .empty ⟨2,true,10,33⟩ .empty) ⟨2,true,14,0⟩ .empty) ⟨2,true,14,3⟩ (.node .empty ⟨2,true,14,7⟩ .empty)) ⟨2,true,14,10⟩ (.node (.node (.node .empty ⟨2,true,14,11⟩ .empty) ⟨2,true,14,14⟩ .empty) ⟨2,true,14,19⟩ (.node .empty ⟨2,true,14,21⟩ .empty)))
def t516_525 : Tree := (.node (.node (.node (.node .empty ⟨2,true,14,27⟩ .empty) ⟨2,true,14,29⟩ .empty) ⟨2,true,14,30⟩ (.node .empty ⟨2,true,14,33⟩ .empty)) ⟨2,true,18,0⟩ (.node (.node (.node .empty ⟨2,true,18,3⟩ .empty) ⟨2,true,18,5⟩ .empty) ⟨2,true,18,7⟩ (.node .empty ⟨2,true,18,8⟩ .empty)))
def t506_525 : Tree := .node t506_515 ⟨2,true,14,22⟩ t516_525
def t526_535 : Tree := (.node (.node (.node (.node .empty ⟨2,true,18,11⟩ .empty) ⟨2,true,18,12⟩ .empty) ⟨2,true,18,14⟩ (.node .empty ⟨2,true,18,16⟩ .empty)) ⟨2,true,18,19⟩ (.node (.node (.node .empty ⟨2,true,18,21⟩ .empty) ⟨2,true,18,22⟩ .empty) ⟨2,true,18,25⟩ (.node .empty ⟨2,true,18,27⟩ .empty)))
def t536_544 : Tree := (.node (.node (.node (.node .empty ⟨2,true,18,30⟩ .empty) ⟨2,true,18,33⟩ .empty) ⟨3,false,2,1⟩ (.node .empty ⟨3,false,3,0⟩ .empty)) ⟨3,false,10,1⟩ (.node (.node .empty ⟨3,false,10,4⟩ .empty) ⟨3,false,10,6⟩ (.node .empty ⟨3,false,10,9⟩ .empty)))
def t526_544 : Tree := .node t526_535 ⟨2,true,18,29⟩ t536_544
def t506_544 : Tree := .node t506_525 ⟨2,true,18,10⟩ t526_544
def t467_544 : Tree := .node t467_505 ⟨2,true,10,30⟩ t506_544
def t545_554 : Tree := (.node (.node (.node (.node .empty ⟨3,false,10,15⟩ .empty) ⟨3,false,10,20⟩ .empty) ⟨3,false,10,26⟩ (.node .empty ⟨3,false,10,34⟩ .empty)) ⟨3,false,11,1⟩ (.node (.node (.node .empty ⟨3,false,11,4⟩ .empty) ⟨3,false,11,6⟩ .empty) ⟨3,false,11,9⟩ (.node .empty ⟨3,false,11,13⟩ .empty)))
def t555_564 : Tree := (.node (.node (.node (.node .empty ⟨3,false,11,20⟩ .empty) ⟨3,false,11,26⟩ .empty) ⟨3,false,11,34⟩ (.node .empty ⟨3,false,12,0⟩ .empty)) ⟨3,false,12,3⟩ (.node (.node (.node .empty ⟨3,false,12,5⟩ .empty) ⟨3,false,12,8⟩ .empty) ⟨3,false,12,10⟩ (.node .empty ⟨3,false,12,12⟩ .empty)))
def t545_564 : Tree := .node t545_554 ⟨3,false,11,15⟩ t555_564
def t565_574 : Tree := (.node (.node (.node (.node .empty ⟨3,false,12,16⟩ .empty) ⟨3,false,12,19⟩ .empty) ⟨3,false,12,21⟩ (.node .empty ⟨3,false,12,25⟩ .empty)) ⟨3,false,12,33⟩ (.node (.node (.node .empty ⟨3,false,17,0⟩ .empty) ⟨3,false,17,3⟩ .empty) ⟨3,false,17,5⟩ (.node .empty ⟨3,false,17,8⟩ .empty)))
def t575_583 : Tree := (.node (.node (.node (.node .empty ⟨3,false,17,12⟩ .empty) ⟨3,false,17,14⟩ .empty) ⟨3,false,17,16⟩ (.node .empty ⟨3,false,17,19⟩ .empty)) ⟨3,false,17,21⟩ (.node (.node .empty ⟨3,false,17,25⟩ .empty) ⟨3,false,17,33⟩ (.node .empty ⟨3,false,18,1⟩ .empty)))
def t565_583 : Tree := .node t565_574 ⟨3,false,17,10⟩ t575_583
def t545_583 : Tree := .node t545_564 ⟨3,false,12,14⟩ t565_583
def t584_593 : Tree := (.node (.node (.node (.node .empty ⟨3,false,18,6⟩ .empty) ⟨3,false,18,9⟩ .empty) ⟨3,false,18,13⟩ (.node .empty ⟨3,false,18,15⟩ .empty)) ⟨3,false,18,20⟩ (.node (.node (.node .empty ⟨3,false,18,26⟩ .empty) ⟨3,false,18,34⟩ .empty) ⟨3,false,19,0⟩ (.node .empty ⟨3,false,19,3⟩ .empty)))
def t594_602 : Tree := (.node (.node (.node (.node .empty ⟨3,false,19,8⟩ .empty) ⟨3,false,19,10⟩ .empty) ⟨3,false,19,12⟩ (.node .empty ⟨3,false,19,14⟩ .empty)) ⟨3,false,19,16⟩ (.node (.node .empty ⟨3,false,19,19⟩ .empty) ⟨3,false,19,21⟩ (.node .empty ⟨3,false,19,25⟩ .empty)))
def t584_602 : Tree := .node t584_593 ⟨3,false,19,5⟩ t594_602
def t603_612 : Tree := (.node (.node (.node (.node .empty ⟨3,false,24,1⟩ .empty) ⟨3,false,24,4⟩ .empty) ⟨3,false,24,6⟩ (.node .empty ⟨3,false,24,9⟩ .empty)) ⟨3,false,24,13⟩ (.node (.node (.node .empty ⟨3,false,24,15⟩ .empty) ⟨3,false,24,20⟩ .empty) ⟨3,false,24,26⟩ (.node .empty ⟨3,false,24,34⟩ .empty)))
def t613_621 : Tree := (.node (.node (.node (.node .empty ⟨3,true,8,0⟩ .empty) ⟨3,true,8,8⟩ .empty) ⟨3,true,8,12⟩ (.node .empty ⟨3,true,8,19⟩ .empty)) ⟨3,true,8,33⟩ (.node (.node .empty ⟨3,true,9,2⟩ .empty) ⟨3,true,9,24⟩ (.node .empty ⟨3,true,10,2⟩ .empty)))
def t603_621 : Tree := .node t603_612 ⟨3,true,1,2⟩ t613_621
def t584_621 : Tree := .node t584_602 ⟨3,false,19,33⟩ t603_621
def t545_621 : Tree := .node t545_583 ⟨3,false,18,4⟩ t584_621
def t467_621 : Tree := .node t467_544 ⟨3,false,10,13⟩ t545_621
def t311_621 : Tree := .node t311_466 ⟨2,true,2,14⟩ t467_621
def t0_621 : Tree := .node t0_310 ⟨1,true,11,8⟩ t311_621
def t622_631 : Tree := (.node (.node (.node (.node .empty ⟨3,true,12,0⟩ .empty) ⟨3,true,12,3⟩ .empty) ⟨3,true,12,5⟩ (.node .empty ⟨3,true,12,8⟩ .empty)) ⟨3,true,12,10⟩ (.node (.node (.node .empty ⟨3,true,12,12⟩ .empty) ⟨3,true,12,14⟩ .empty) ⟨3,true,12,16⟩ (.node .empty ⟨3,true,12,19⟩ .empty)))
def t632_641 : Tree := (.node (.node (.node (.node .empty ⟨3,true,12,25⟩ .empty) ⟨3,true,12,33⟩ .empty) ⟨3,true,16,2⟩ (.node .empty ⟨3,true,16,24⟩ .empty)) ⟨3,true,17,0⟩ (.node (.node (.node .empty ⟨3,true,17,3⟩ .empty) ⟨3,true,17,5⟩ .empty) ⟨3,true,17,8⟩ (.node .empty ⟨3,true,17,10⟩ .empty)))
def t622_641 : Tree := .node t622_631 ⟨3,true,12,21⟩ t632_641
def t642_651 : Tree := (.node (.node (.node (.node .empty ⟨3,true,17,14⟩ .empty) ⟨3,true,17,16⟩ .empty) ⟨3,true,17,19⟩ (.node .empty ⟨3,true,17,21⟩ .empty)) ⟨3,true,17,25⟩ (.node (.node (.node .empty ⟨3,true,17,33⟩ .empty) ⟨3,true,18,2⟩ .empty) ⟨3,true,18,24⟩ (.node .empty ⟨3,true,20,2⟩ .empty)))
def t652_660 : Tree := (.node (.node (.node (.node .empty ⟨3,true,23,2⟩ .empty) ⟨3,true,23,24⟩ .empty) ⟨4,false,0,10⟩ (.node .empty ⟨4,false,0,16⟩ .empty)) ⟨4,false,0,23⟩ (.node (.node .empty ⟨4,false,7,1⟩ .empty) ⟨4,false,7,4⟩ (.node .empty ⟨4,false,7,6⟩ .empty)))
def t642_660 : Tree := .node t642_651 ⟨3,true,20,24⟩ t652_660
def t622_660 : Tree := .node t622_641 ⟨3,true,17,12⟩ t642_660
def t661_670 : Tree := (.node (.node (.node (.node .empty ⟨4,false,7,13⟩ .empty) ⟨4,false,7,15⟩ .empty) ⟨4,false,7,20⟩ (.node .empty ⟨4,false,7,26⟩ .empty)) ⟨4,false,7,34⟩ (.node (.node (.node .empty ⟨4,false,9,0⟩ .empty) ⟨4,false,9,7⟩ .empty) ⟨4,false,9,11⟩ (.node .empty ⟨4,false,9,18⟩ .empty)))
def t671_680 : Tree := (.node (.node (.node (.node .empty ⟨4,false,9,27⟩ .empty) ⟨4,false,9,30⟩ .empty) ⟨4,false,9,32⟩ (.node .empty ⟨4,false,10,1⟩ .empty)) ⟨4,false,10,4⟩ (.node (.node (.node .empty ⟨4,false,10,6⟩ .empty) ⟨4,false,10,9⟩ .empty) ⟨4,false,10,13⟩ (.node .empty ⟨4,false,10,15⟩ .empty)))
def t661_680 : Tree := .node t661_670 ⟨4,false,9,22⟩ t671_680
def t681_690 : Tree := (.node (.node (.node (.node .empty ⟨4,false,10,26⟩ .empty) ⟨4,false,10,34⟩ .empty) ⟨4,false,11,1⟩ (.node .empty ⟨4,false,11,4⟩ .empty)) ⟨4,false,11,6⟩ (.node (.node (.node .empty ⟨4,false,11,9⟩ .empty) ⟨4,false,11,13⟩ .empty) ⟨4,false,11,15⟩ (.node .empty ⟨4,false,11,20⟩ .empty)))
def t691_699 : Tree := (.node (.node (.node (.node .empty ⟨4,false,11,34⟩ .empty) ⟨4,false,14,4⟩ .empty) ⟨4,false,14,6⟩ (.node .empty ⟨4,false,14,15⟩ .empty)) ⟨4,false,14,26⟩ (.node (.node .empty ⟨4,false,18,1⟩ .empty) ⟨4,false,18,4⟩ (.node .empty ⟨4,false,18,6⟩ .empty)))
def t681_699 : Tree := .node t681_690 ⟨4,false,11,26⟩ t691_699
def t661_699 : Tree := .node t661_680 ⟨4,false,10,20⟩ t681_699
def t622_699 : Tree := .node t622_660 ⟨4,false,7,9⟩ t661_699
def t700_709 : Tree := (.node (.node (.node (.node .empty ⟨4,false,18,13⟩ .empty) ⟨4,false,18,15⟩ .empty) ⟨4,false,18,20⟩ (.node .empty ⟨4,false,18,26⟩ .empty)) ⟨4,false,18,34⟩ (.node (.node (.node .empty ⟨4,false,20,0⟩ .empty) ⟨4,false,20,1⟩ .empty) ⟨4,false,20,4⟩ (.node .empty ⟨4,false,20,6⟩ .empty)))
def t710_719 : Tree := (.node (.node (.node (.node .empty ⟨4,false,20,9⟩ .empty) ⟨4,false,20,11⟩ .empty) ⟨4,false,20,13⟩ (.node .empty ⟨4,false,20,15⟩ .empty)) ⟨4,false,20,18⟩ (.node (.node (.node .empty ⟨4,false,20,20⟩ .empty) ⟨4,false,20,22⟩ .empty) ⟨4,false,20,26⟩ (.node .empty ⟨4,false,20,27⟩ .empty)))
def t700_719 : Tree := .node t700_709 ⟨4,false,20,7⟩ t710_719
def t720_729 : Tree := (.node (.node (.node (.node .empty ⟨4,false,20,32⟩ .empty) ⟨4,false,20,34⟩ .empty) ⟨4,false,22,0⟩ (.node .empty ⟨4,false,22,1⟩ .empty)) ⟨4,false,22,4⟩ (.node (.node (.node .empty ⟨4,false,22,6⟩ .empty) ⟨4,false,22,7⟩ .empty) ⟨4,false,22,9⟩ (.node .empty ⟨4,false,22,11⟩ .empty)))
def t730_738 : Tree := (.node (.node (.node (.node .empty ⟨4,false,22,15⟩ .empty) ⟨4,false,22,18⟩ .empty) ⟨4,false,22,20⟩ (.node .empty ⟨4,false,22,22⟩ .empty)) ⟨4,false,22,26⟩ (.node (.node .empty ⟨4,false,22,27⟩ .empty) ⟨4,false,22,30⟩ (.node .empty ⟨4,false,22,32⟩ .empty)))
def t720_738 : Tree := .node t720_729 ⟨4,false,22,13⟩ t730_738
def t700_738 : Tree := .node t700_719 ⟨4,false,20,30⟩ t720_738
def t739_748 : Tree := (.node (.node (.node (.node .empty ⟨4,false,24,1⟩ .empty) ⟨4,false,24,4⟩ .empty) ⟨4,false,24,6⟩ (.node .empty ⟨4,false,24,9⟩ .empty)) ⟨4,false,24,13⟩ (.node (.node (.node .empty ⟨4,false,24,15⟩ .empty) ⟨4,false,24,20⟩ .empty) ⟨4,false,24,26⟩ (.node .empty ⟨4,false,24,34⟩ .empty)))
def t749_758 : Tree := (.node (.node (.node (.node .empty ⟨4,true,0,5⟩ .empty) ⟨4,true,0,16⟩ .empty) ⟨4,true,0,21⟩ (.node .empty ⟨4,true,0,23⟩ .empty)) ⟨4,true,2,1⟩ (.node (.node (.node .empty ⟨4,true,3,1⟩ .empty) ⟨4,true,3,3⟩ .empty) ⟨4,true,3,5⟩ (.node .empty ⟨4,true,3,9⟩ .empty)))
def t739_758 : Tree := .node t739_748 ⟨4,true,0,4⟩ t749_758
def t759_768 : Tree := (.node (.node (.node (.node .empty ⟨4,true,3,13⟩ .empty) ⟨4,true,3,14⟩ .empty) ⟨4,true,3,16⟩ (.node .empty ⟨4,true,3,18⟩ .empty)) ⟨4,true,3,20⟩ (.node (.node (.node .empty ⟨4,true,3,21⟩ .empty) ⟨4,true,3,23⟩ .empty) ⟨4,true,3,25⟩ (.node .empty ⟨4,true,3,34⟩ .empty)))
def t769_777 : Tree := (.node (.node (.node (.node .empty ⟨4,true,4,5⟩ .empty) ⟨4,true,4,7⟩ .empty) ⟨4,true,4,9⟩ (.node .empty ⟨4,true,4,13⟩ .empty)) ⟨4,true,4,16⟩ (.node (.node .empty ⟨4,true,4,21⟩ .empty) ⟨4,true,4,22⟩ (.node .empty ⟨4,true,4,23⟩ .empty)))
def t759_777 : Tree := .node t759_768 ⟨4,true,4,3⟩ t769_777
def t739_777 : Tree := .node t739_758 ⟨4,true,3,10⟩ t759_777
def t700_777 : Tree := .node t700_738 ⟨4,false,22,34⟩ t739_777
def t622_777 : Tree := .node t622_699 ⟨4,false,18,9⟩ t700_777
def t778_787 : Tree := (.node (.node (.node (.node .empty ⟨4,true,4,30⟩ .empty) ⟨4,true,7,0⟩ .empty) ⟨4,true,7,7⟩ (.node .empty ⟨4,true,7,11⟩ .empty)) ⟨4,true,7,18⟩ (.node (.node (.node .empty ⟨4,true,7,22⟩ .empty) ⟨4,true,7,27⟩ .empty) ⟨4,true,7,30⟩ (.node .empty ⟨4,true,7,32⟩ .empty)))
def t788_797 : Tree := (.node (.node (.node (.node .empty ⟨4,true,8,1⟩ .empty) ⟨4,true,8,3⟩ .empty) ⟨4,true,8,4⟩ (.node .empty ⟨4,true,8,5⟩ .empty)) ⟨4,true,8,6⟩ (.node (.node (.node .empty ⟨4,true,8,7⟩ .empty) ⟨4,true,8,9⟩ .empty) ⟨4,true,8,10⟩ (.node .empty ⟨4,true,8,11⟩ .empty)))
def t778_797 : Tree := .node t778_787 ⟨4,true,8,0⟩ t788_797
def t798_807 : Tree := (.node (.node (.node (.node .empty ⟨4,true,8,14⟩ .empty) ⟨4,true,8,15⟩ .empty) ⟨4,true,8,16⟩ (.node .empty ⟨4,true,8,18⟩ .empty)) ⟨4,true,8,20⟩ (.node (.node (.node .empty ⟨4,true,8,21⟩ .empty) ⟨4,true,8,22⟩ .empty) ⟨4,true,8,23⟩ (.node .empty ⟨4,true,8,25⟩ .empty)))
def t808_816 : Tree := (.node (.node (.node (.node .empty ⟨4,true,8,27⟩ .empty) ⟨4,true,8,30⟩ .empty) ⟨4,true,8,32⟩ (.node .empty ⟨4,true,8,34⟩ .empty)) ⟨4,true,9,0⟩ (.node (.node .empty ⟨4,true,9,1⟩ .empty) ⟨4,true,9,4⟩ (.node .empty ⟨4,true,9,6⟩ .empty)))
def t798_816 : Tree := .node t798_807 ⟨4,true,8,26⟩ t808_816
def t778_816 : Tree := .node t778_797 ⟨4,true,8,13⟩ t798_816
def t817_826 : Tree := (.node (.node (.node (.node .empty ⟨4,true,9,9⟩ .empty) ⟨4,true,9,11⟩ .empty) ⟨4,true,9,13⟩ (.node .empty ⟨4,true,9,15⟩ .empty)) ⟨4,true,9,18⟩ (.node (.node (.node .empty ⟨4,true,9,20⟩ .empty) ⟨4,true,9,22⟩ .empty) ⟨4,true,9,26⟩ (.node .empty ⟨4,true,9,27⟩ .empty)))
def t827_836 : Tree := (.node (.node (.node (.node .empty ⟨4,true,9,32⟩ .empty) ⟨4,true,9,34⟩ .empty) ⟨4,true,10,0⟩ (.node .empty ⟨4,true,10,1⟩ .empty)) ⟨4,true,10,4⟩ (.node (.node (.node .empty ⟨4,true,10,6⟩ .empty) ⟨4,true,10,7⟩ .empty) ⟨4,true,10,9⟩ (.node .empty ⟨4,true,10,11⟩ .empty)))
def t817_836 : Tree := .node t817_826 ⟨4,true,9,30⟩ t827_836
def t837_846 : Tree := (.node (.node (.node (.node .empty ⟨4,true,10,15⟩ .empty) ⟨4,true,10,18⟩ .empty) ⟨4,true,10,20⟩ (.node .empty ⟨4,true,10,22⟩ .empty)) ⟨4,true,10,26⟩ (.node (.node (.node .empty ⟨4,true,10,27⟩ .empty) ⟨4,true,10,30⟩ .empty) ⟨4,true,10,32⟩ (.node .empty ⟨4,true,10,34⟩ .empty)))
def t847_855 : Tree := (.node (.node (.node (.node .empty ⟨4,true,11,1⟩ .empty) ⟨4,true,11,4⟩ .empty) ⟨4,true,11,6⟩ (.node .empty ⟨4,true,11,7⟩ .empty)) ⟨4,true,11,9⟩ (.node (.node .empty ⟨4,true,11,11⟩ .empty) ⟨4,true,11,13⟩ (.node .empty ⟨4,true,11,15⟩ .empty)))
def t837_855 : Tree := .node t837_846 ⟨4,true,11,0⟩ t847_855
def t817_855 : Tree := .node t817_836 ⟨4,true,10,13⟩ t837_855
def t778_855 : Tree := .node t778_816 ⟨4,true,9,7⟩ t817_855
def t856_865 : Tree := (.node (.node (.node (.node .empty ⟨4,true,11,20⟩ .empty) ⟨4,true,11,22⟩ .empty) ⟨4,true,11,26⟩ (.node .empty ⟨4,true,11,27⟩ .empty)) ⟨4,true,11,30⟩ (.node (.node (.node .empty ⟨4,true,11,32⟩ .empty) ⟨4,true,11,34⟩ .empty) ⟨4,true,14,7⟩ (.node .empty ⟨4,true,14,11⟩ .empty)))
def t866_875 : Tree := (.node (.node (.node (.node .empty ⟨4,true,14,27⟩ .empty) ⟨4,true,14,30⟩ .empty) ⟨4,true,15,0⟩ (.node .empty ⟨4,true,15,1⟩ .empty)) ⟨4,true,15,3⟩ (.node (.node (.node .empty ⟨4,true,15,4⟩ .empty) ⟨4,true,15,5⟩ .empty) ⟨4,true,15,6⟩ (.node .empty ⟨4,true,15,9⟩ .empty)))
def t856_875 : Tree := .node t856_865 ⟨4,true,14,22⟩ t866_875
def t876_885 : Tree := (.node (.node (.node (.node .empty ⟨4,true,15,13⟩ .empty) ⟨4,true,15,14⟩ .empty) ⟨4,true,15,15⟩ (.node .empty ⟨4,true,15,16⟩ .empty)) ⟨4,true,15,18⟩ (.node (.node (.node .empty ⟨4,true,15,20⟩ .empty) ⟨4,true,15,21⟩ .empty) ⟨4,true,15,23⟩ (.node .empty ⟨4,true,15,25⟩ .empty)))
def t886_894 : Tree := (.node (.node (.node (.node .empty ⟨4,true,15,32⟩ .empty) ⟨4,true,15,34⟩ .empty) ⟨4,true,16,1⟩ (.node .empty ⟨4,true,16,4⟩ .empty)) ⟨4,true,16,6⟩ (.node (.node .empty ⟨4,true,16,9⟩ .empty) ⟨4,true,16,13⟩ (.node .empty ⟨4,true,16,15⟩ .empty)))
def t876_894 : Tree := .node t876_885 ⟨4,true,15,26⟩ t886_894
def t856_894 : Tree := .node t856_875 ⟨4,true,15,10⟩ t876_894
def t895_904 : Tree := (.node (.node (.node (.node .empty ⟨4,true,16,26⟩ .empty) ⟨4,true,16,34⟩ .empty) ⟨4,true,17,0⟩ (.node .empty ⟨4,true,17,1⟩ .empty)) ⟨4,true,17,3⟩ (.node (.node (.node .empty ⟨4,true,17,4⟩ .empty) ⟨4,true,17,5⟩ .empty) ⟨4,true,17,6⟩ (.node .empty ⟨4,true,17,7⟩ .empty)))
def t905_913 : Tree := (.node (.node (.node (.node .empty ⟨4,true,17,10⟩ .empty) ⟨4,true,17,11⟩ .empty) ⟨4,true,17,13⟩ (.node .empty ⟨4,true,17,14⟩ .empty)) ⟨4,true,17,15⟩ (.node (.node .empty ⟨4,true,17,16⟩ .empty) ⟨4,true,17,18⟩ (.node .empty ⟨4,true,17,20⟩ .empty)))
def t895_913 : Tree := .node t895_904 ⟨4,true,17,9⟩ t905_913
def t914_923 : Tree := (.node (.node (.node (.node .empty ⟨4,true,17,22⟩ .empty) ⟨4,true,17,23⟩ .empty) ⟨4,true,17,25⟩ (.node .empty ⟨4,true,17,26⟩ .empty)) ⟨4,true,17,27⟩ (.node (.node (.node .empty ⟨4,true,17,30⟩ .empty) ⟨4,true,17,32⟩ .empty) ⟨4,true,17,34⟩ (.node .empty ⟨4,true,18,0⟩ .empty)))
def t924_932 : Tree := (.node (.node (.node (.node .empty ⟨4,true,18,4⟩ .empty) ⟨4,true,18,6⟩ .empty) ⟨4,true,18,7⟩ (.node .empty ⟨4,true,18,9⟩ .empty)) ⟨4,true,18,11⟩ (.node (.node .empty ⟨4,true,18,13⟩ .empty) ⟨4,true,18,15⟩ (.node .empty ⟨4,true,18,18⟩ .empty)))
def t914_932 : Tree := .node t914_923 ⟨4,true,18,1⟩ t924_932
def t895_932 : Tree := .node t895_913 ⟨4,true,17,21⟩ t914_932
def t856_932 : Tree := .node t856_894 ⟨4,true,16,20⟩ t895_932
def t778_932 : Tree := .node t778_855 ⟨4,true,11,18⟩ t856_932
def t622_932 : Tree := .node t622_777 ⟨4,true,4,25⟩ t778_932
def t933_942 : Tree := (.node (.node (.node (.node .empty ⟨4,true,18,22⟩ .empty) ⟨4,true,18,26⟩ .empty) ⟨4,true,18,27⟩ (.node .empty ⟨4,true,18,30⟩ .empty)) ⟨4,true,18,32⟩ (.node (.node (.node .empty ⟨4,true,18,34⟩ .empty) ⟨4,true,19,0⟩ .empty) ⟨4,true,19,1⟩ (.node .empty ⟨4,true,19,3⟩ .empty)))
def t943_952 : Tree := (.node (.node (.node (.node .empty ⟨4,true,19,5⟩ .empty) ⟨4,true,19,6⟩ .empty) ⟨4,true,19,7⟩ (.node .empty ⟨4,true,19,9⟩ .empty)) ⟨4,true,19,10⟩ (.node (.node (.node .empty ⟨4,true,19,11⟩ .empty) ⟨4,true,19,13⟩ .empty) ⟨4,true,19,14⟩ (.node .empty ⟨4,true,19,15⟩ .empty)))
def t933_952 : Tree := .node t933_942 ⟨4,true,19,4⟩ t943_952
def t953_962 : Tree := (.node (.node (.node (.node .empty ⟨4,true,19,18⟩ .empty) ⟨4,true,19,20⟩ .empty) ⟨4,true,19,21⟩ (.node .empty ⟨4,true,19,22⟩ .empty)) ⟨4,true,19,23⟩ (.node (.node (.node .empty ⟨4,true,19,25⟩ .empty) ⟨4,true,19,26⟩ .empty) ⟨4,true,19,27⟩ (.node .empty ⟨4,true,19,30⟩ .empty)))
def t963_971 : Tree := (.node (.node (.node (.node .empty ⟨4,true,19,34⟩ .empty) ⟨4,true,20,0⟩ .empty) ⟨4,true,20,1⟩ (.node .empty ⟨4,true,20,4⟩ .empty)) ⟨4,true,20,6⟩ (.node (.node .empty ⟨4,true,20,7⟩ .empty) ⟨4,true,20,9⟩ (.node .empty ⟨4,true,20,11⟩ .empty)))
def t953_971 : Tree := .node t953_962 ⟨4,true,19,32⟩ t963_971
def t933_971 : Tree := .node t933_952 ⟨4,true,19,16⟩ t953_971
def t972_981 : Tree := (.node (.node (.node (.node .empty ⟨4,true,20,15⟩ .empty) ⟨4,true,20,18⟩ .empty) ⟨4,true,20,20⟩ (.node .empty ⟨4,true,20,22⟩ .empty)) ⟨4,true,20,26⟩ (.node (.node (.node .empty ⟨4,true,20,27⟩ .empty) ⟨4,true,20,30⟩ .empty) ⟨4,true,20,32⟩ (.node .empty ⟨4,true,20,34⟩ .empty)))
def t982_991 : Tree := (.node (.node (.node (.node .empty ⟨4,true,22,1⟩ .empty) ⟨4,true,22,4⟩ .empty) ⟨4,true,22,6⟩ (.node .empty ⟨4,true,22,7⟩ .empty)) ⟨4,true,22,9⟩ (.node (.node (.node .empty ⟨4,true,22,11⟩ .empty) ⟨4,true,22,13⟩ .empty) ⟨4,true,22,15⟩ (.node .empty ⟨4,true,22,18⟩ .empty)))
def t972_991 : Tree := .node t972_981 ⟨4,true,22,0⟩ t982_991
def t992_1001 : Tree := (.node (.node (.node (.node .empty ⟨4,true,22,22⟩ .empty) ⟨4,true,22,26⟩ .empty) ⟨4,true,22,27⟩ (.node .empty ⟨4,true,22,30⟩ .empty)) ⟨4,true,22,32⟩ (.node (.node (.node .empty ⟨4,true,22,34⟩ .empty) ⟨4,true,24,0⟩ .empty) ⟨4,true,24,1⟩ (.node .empty ⟨4,true,24,4⟩ .empty)))
def t1002_1010 : Tree := (.node (.node (.node (.node .empty ⟨4,true,24,7⟩ .empty) ⟨4,true,24,9⟩ .empty) ⟨4,true,24,11⟩ (.node .empty ⟨4,true,24,13⟩ .empty)) ⟨4,true,24,15⟩ (.node (.node .empty ⟨4,true,24,18⟩ .empty) ⟨4,true,24,20⟩ (.node .empty ⟨4,true,24,22⟩ .empty)))
def t992_1010 : Tree := .node t992_1001 ⟨4,true,24,6⟩ t1002_1010
def t972_1010 : Tree := .node t972_991 ⟨4,true,22,20⟩ t992_1010
def t933_1010 : Tree := .node t933_971 ⟨4,true,20,13⟩ t972_1010
def t1011_1020 : Tree := (.node (.node (.node (.node .empty ⟨4,true,24,27⟩ .empty) ⟨4,true,24,30⟩ .empty) ⟨4,true,24,32⟩ (.node .empty ⟨4,true,24,34⟩ .empty)) ⟨5,false,0,5⟩ (.node (.node (.node .empty ⟨5,false,0,11⟩ .empty) ⟨5,false,0,22⟩ .empty) ⟨5,false,0,29⟩ (.node .empty ⟨5,false,1,7⟩ .empty)))
def t1021_1030 : Tree := (.node (.node (.node (.node .empty ⟨5,false,1,10⟩ .empty) ⟨5,false,1,11⟩ .empty) ⟨5,false,1,14⟩ (.node .empty ⟨5,false,1,22⟩ .empty)) ⟨5,false,1,27⟩ (.node (.node (.node .empty ⟨5,false,1,29⟩ .empty) ⟨5,false,2,3⟩ .empty) ⟨5,false,2,7⟩ (.node .empty ⟨5,false,2,10⟩ .empty)))
def t1011_1030 : Tree := .node t1011_1020 ⟨5,false,1,8⟩ t1021_1030
def t1031_1040 : Tree := (.node (.node (.node (.node .empty ⟨5,false,2,14⟩ .empty) ⟨5,false,2,19⟩ .empty) ⟨5,false,2,21⟩ (.node .empty ⟨5,false,2,22⟩ .empty)) ⟨5,false,2,27⟩ (.node (.node (.node .empty ⟨5,false,2,29⟩ .empty) ⟨5,false,2,30⟩ .empty) ⟨5,false,7,0⟩ (.node .empty ⟨5,false,7,3⟩ .empty)))
def t1041_1049 : Tree := (.node (.node (.node (.node .empty ⟨5,false,7,7⟩ .empty) ⟨5,false,7,8⟩ .empty) ⟨5,false,7,10⟩ (.node .empty ⟨5,false,7,11⟩ .empty)) ⟨5,false,7,12⟩ (.node (.node .empty ⟨5,false,7,14⟩ .empty) ⟨5,false,7,16⟩ (.node .empty ⟨5,false,7,19⟩ .empty)))
def t1031_1049 : Tree := .node t1031_1040 ⟨5,false,7,5⟩ t1041_1049
def t1011_1049 : Tree := .node t1011_1030 ⟨5,false,2,11⟩ t1031_1049
def t1050_1059 : Tree := (.node (.node (.node (.node .empty ⟨5,false,7,22⟩ .empty) ⟨5,false,7,25⟩ .empty) ⟨5,false,7,27⟩ (.node .empty ⟨5,false,7,29⟩ .empty)) ⟨5,false,7,30⟩ (.node (.node (.node .empty ⟨5,false,7,33⟩ .empty) ⟨5,false,10,0⟩ .empty) ⟨5,false,10,3⟩ (.node .empty ⟨5,false,10,5⟩ .empty)))
def t1060_1069 : Tree := (.node (.node (.node (.node .empty ⟨5,false,10,8⟩ .empty) ⟨5,false,10,10⟩ .empty) ⟨5,false,10,11⟩ (.node .empty ⟨5,false,10,12⟩ .empty)) ⟨5,false,10,14⟩ (.node (.node (.node .empty ⟨5,false,10,16⟩ .empty) ⟨5,false,10,19⟩ .empty) ⟨5,false,10,21⟩ (.node .empty ⟨5,false,10,22⟩ .empty)))
def t1050_1069 : Tree := .node t1050_1059 ⟨5,false,10,7⟩ t1060_1069
def t1070_1079 : Tree := (.node (.node (.node (.node .empty ⟨5,false,10,27⟩ .empty) ⟨5,false,10,29⟩ .empty) ⟨5,false,10,30⟩ (.node .empty ⟨5,false,10,33⟩ .empty)) ⟨5,false,14,0⟩ (.node (.node (.node .empty ⟨5,false,14,3⟩ .empty) ⟨5,false,14,5⟩ .empty) ⟨5,false,14,7⟩ (.node .empty ⟨5,false,14,10⟩ .empty)))
def t1080_1088 : Tree := (.node (.node (.node (.node .empty ⟨5,false,14,14⟩ .empty) ⟨5,false,14,16⟩ .empty) ⟨5,false,14,19⟩ (.node .empty ⟨5,false,14,21⟩ .empty)) ⟨5,false,14,22⟩ (.node (.node .empty ⟨5,false,14,25⟩ .empty) ⟨5,false,14,27⟩ (.node .empty ⟨5,false,14,29⟩ .empty)))
def t1070_1088 : Tree := .node t1070_1079 ⟨5,false,14,11⟩ t1080_1088
def t1050_1088 : Tree := .node t1050_1069 ⟨5,false,10,25⟩ t1070_1088
def t1011_1088 : Tree := .node t1011_1049 ⟨5,false,7,21⟩ t1050_1088
def t933_1088 : Tree := .node t933_1010 ⟨4,true,24,26⟩ t1011_1088
def t1089_1098 : Tree := (.node (.node (.node (.node .empty ⟨5,false,14,33⟩ .empty) ⟨5,false,18,0⟩ .empty) ⟨5,false,18,3⟩ (.node .empty ⟨5,false,18,5⟩ .empty)) ⟨5,false,18,7⟩ (.node (.node (.node .empty ⟨5,false,18,8⟩ .empty) ⟨5,false,18,10⟩ .empty) ⟨5,false,18,11⟩ (.node .empty ⟨5,false,18,12⟩ .empty)))
def t1099_1108 : Tree := (.node (.node (.node (.node .empty ⟨5,false,18,16⟩ .empty) ⟨5,false,18,19⟩ .empty) ⟨5,false,18,21⟩ (.node .empty ⟨5,false,18,22⟩ .empty)) ⟨5,false,18,25⟩ (.node (.node (.node .empty ⟨5,false,18,27⟩ .empty) ⟨5,false,18,29⟩ .empty) ⟨5,false,18,30⟩ (.node .empty ⟨5,false,18,33⟩ .empty)))
def t1089_1108 : Tree := .node t1089_1098 ⟨5,false,18,14⟩ t1099_1108
def t1109_1118 : Tree := (.node (.node (.node (.node .empty ⟨5,true,5,8⟩ .empty) ⟨5,true,5,12⟩ .empty) ⟨5,true,6,0⟩ (.node .empty ⟨5,true,6,8⟩ .empty)) ⟨5,true,6,12⟩ (.node (.node (.node .empty ⟨5,true,6,19⟩ .empty) ⟨5,true,6,33⟩ .empty) ⟨5,true,8,0⟩ (.node .empty ⟨5,true,8,3⟩ .empty)))
def t1119_1127 : Tree := (.node (.node (.node (.node .empty ⟨5,true,8,8⟩ .empty) ⟨5,true,8,10⟩ .empty) ⟨5,true,8,12⟩ (.node .empty ⟨5,true,8,14⟩ .empty)) ⟨5,true,8,16⟩ (.node (.node .empty ⟨5,true,8,19⟩ .empty) ⟨5,true,8,21⟩ (.node .empty ⟨5,true,8,25⟩ .empty)))
def t1109_1127 : Tree := .node t1109_1118 ⟨5,true,8,5⟩ t1119_1127
def t1089_1127 : Tree := .node t1089_1108 ⟨5,true,1,3⟩ t1109_1127
def t1128_1137 : Tree := (.node (.node (.node (.node .empty ⟨5,true,9,0⟩ .empty) ⟨5,true,9,3⟩ .empty) ⟨5,true,9,5⟩ (.node .empty ⟨5,true,9,8⟩ .empty)) ⟨5,true,9,10⟩ (.node (.node (.node .empty ⟨5,true,9,12⟩ .empty) ⟨5,true,9,14⟩ .empty) ⟨5,true,9,16⟩ (.node .empty ⟨5,true,9,19⟩ .empty)))
def t1138_1147 : Tree := (.node (.node (.node (.node .empty ⟨5,true,9,25⟩ .empty) ⟨5,true,9,33⟩ .empty) ⟨5,true,10,0⟩ (.node .empty ⟨5,true,10,3⟩ .empty)) ⟨5,true,10,5⟩ (.node (.node (.node .empty ⟨5,true,10,8⟩ .empty) ⟨5,true,10,10⟩ .empty) ⟨5,true,10,12⟩ (.node .empty ⟨5,true,10,14⟩ .empty)))
def t1128_1147 : Tree := .node t1128_1137 ⟨5,true,9,21⟩ t1138_1147
def t1148_1157 : Tree := (.node (.node (.node (.node .empty ⟨5,true,10,19⟩ .empty) ⟨5,true,10,21⟩ .empty) ⟨5,true,10,25⟩ (.node .empty ⟨5,true,10,33⟩ .empty)) ⟨5,true,12,0⟩ (.node (.node (.node .empty ⟨5,true,12,3⟩ .empty) ⟨5,true,12,5⟩ .empty) ⟨5,true,12,8⟩ (.node .empty ⟨5,true,12,10⟩ .empty)))
def t1158_1166 : Tree := (.node (.node (.node (.node .empty ⟨5,true,12,14⟩ .empty) ⟨5,true,12,16⟩ .empty) ⟨5,true,12,19⟩ (.node .empty ⟨5,true,12,21⟩ .empty)) ⟨5,true,12,25⟩ (.node (.node .empty ⟨5,true,12,33⟩ .empty) ⟨5,true,15,3⟩ (.node .empty ⟨5,true,15,5⟩ .empty)))
def t1148_1166 : Tree := .node t1148_1157 ⟨5,true,12,12⟩ t1158_1166
def t1128_1166 : Tree := .node t1128_1147 ⟨5,true,10,16⟩ t1148_1166
def t1089_1166 : Tree := .node t1089_1127 ⟨5,true,8,33⟩ t1128_1166
def t1167_1176 : Tree := (.node (.node (.node (.node .empty ⟨5,true,15,14⟩ .empty) ⟨5,true,15,16⟩ .empty) ⟨5,true,15,21⟩ (.node .empty ⟨5,true,15,25⟩ .empty)) ⟨5,true,16,0⟩ (.node (.node (.node .empty ⟨5,true,16,3⟩ .empty) ⟨5,true,16,5⟩ .empty) ⟨5,true,16,8⟩ (.node .empty ⟨5,true,16,10⟩ .empty)))
def t1177_1186 : Tree := (.node (.node (.node (.node .empty ⟨5,true,16,14⟩ .empty) ⟨5,true,16,16⟩ .empty) ⟨5,true,16,19⟩ (.node .empty ⟨5,true,16,21⟩ .empty)) ⟨5,true,16,25⟩ (.node (.node (.node .empty ⟨5,true,16,33⟩ .empty) ⟨5,true,17,0⟩ .empty) ⟨5,true,17,3⟩ (.node .empty ⟨5,true,17,5⟩ .empty)))
def t1167_1186 : Tree := .node t1167_1176 ⟨5,true,16,12⟩ t1177_1186
def t1187_1196 : Tree := (.node (.node (.node (.node .empty ⟨5,true,17,10⟩ .empty) ⟨5,true,17,12⟩ .empty) ⟨5,true,17,14⟩ (.node .empty ⟨5,true,17,16⟩ .empty)) ⟨5,true,17,19⟩ (.node (.node (.node .empty ⟨5,true,17,21⟩ .empty) ⟨5,true,17,25⟩ .empty) ⟨5,true,17,33⟩ (.node .empty ⟨5,true,18,0⟩ .empty)))
def t1197_1205 : Tree := (.node (.node (.node (.node .empty ⟨5,true,18,5⟩ .empty) ⟨5,true,18,8⟩ .empty) ⟨5,true,18,10⟩ (.node .empty ⟨5,true,18,12⟩ .empty)) ⟨5,true,18,14⟩ (.node (.node .empty ⟨5,true,18,16⟩ .empty) ⟨5,true,18,19⟩ (.node .empty ⟨5,true,18,21⟩ .empty)))
def t1187_1205 : Tree := .node t1187_1196 ⟨5,true,18,3⟩ t1197_1205
def t1167_1205 : Tree := .node t1167_1186 ⟨5,true,17,8⟩ t1187_1205
def t1206_1215 : Tree := (.node (.node (.node (.node .empty ⟨5,true,18,33⟩ .empty) ⟨5,true,19,0⟩ .empty) ⟨5,true,19,3⟩ (.node .empty ⟨5,true,19,5⟩ .empty)) ⟨5,true,19,8⟩ (.node (.node (.node .empty ⟨5,true,19,10⟩ .empty) ⟨5,true,19,12⟩ .empty) ⟨5,true,19,14⟩ (.node .empty ⟨5,true,19,16⟩ .empty)))
def t1216_1224 : Tree := (.node (.node (.node (.node .empty ⟨5,true,19,21⟩ .empty) ⟨5,true,19,25⟩ .empty) ⟨5,true,19,33⟩ (.node .empty ⟨5,true,20,0⟩ .empty)) ⟨5,true,20,3⟩ (.node (.node .empty ⟨5,true,20,5⟩ .empty) ⟨5,true,20,8⟩ (.node .empty ⟨5,true,20,10⟩ .empty)))
def t1206_1224 : Tree := .node t1206_1215 ⟨5,true,19,19⟩ t1216_1224
def t1225_1234 : Tree := (.node (.node (.node (.node .empty ⟨5,true,20,14⟩ .empty) ⟨5,true,20,16⟩ .empty) ⟨5,true,20,19⟩ (.node .empty ⟨5,true,20,21⟩ .empty)) ⟨5,true,20,25⟩ (.node (.node (.node .empty ⟨5,true,20,33⟩ .empty) ⟨5,true,23,0⟩ .empty) ⟨5,true,23,3⟩ (.node .empty ⟨5,true,23,5⟩ .empty)))
def t1235_1243 : Tree := (.node (.node (.node (.node .empty ⟨5,true,23,10⟩ .empty) ⟨5,true,23,12⟩ .empty) ⟨5,true,23,14⟩ (.node .empty ⟨5,true,23,16⟩ .empty)) ⟨5,true,23,19⟩ (.node (.node .empty ⟨5,true,23,21⟩ .empty) ⟨5,true,23,25⟩ (.node .empty ⟨5,true,23,33⟩ .empty)))
def t1225_1243 : Tree := .node t1225_1234 ⟨5,true,23,8⟩ t1235_1243
def t1206_1243 : Tree := .node t1206_1224 ⟨5,true,20,12⟩ t1225_1243
def t1167_1243 : Tree := .node t1167_1205 ⟨5,true,18,25⟩ t1206_1243
def t1089_1243 : Tree := .node t1089_1166 ⟨5,true,15,10⟩ t1167_1243
def t933_1243 : Tree := .node t933_1088 ⟨5,false,14,30⟩ t1089_1243
def t622_1243 : Tree := .node t622_932 ⟨4,true,18,20⟩ t933_1243
def t0_1243 : Tree := .node t0_621 ⟨3,true,10,24⟩ t622_1243
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 0, 0, 6, 0, 5, 0, 14, 0, 7, 8, 13, 0, 9, 0, 10, 17, 11, 12, 13, 0, 22, 0, 0, 15, 21, 0, 16, 0, 18, 0, 20, 19, 11, 0, 20, 0, 10, 0, 0, 0, 23, 0, 24, 12, 13],#[0, 1, 3, 2, 0, 0, 7, 4, 5, 24, 11, 6, 25, 24, 8, 17, 18, 9, 10, 24, 30, 15, 12, 17, 18, 13, 14, 24, 30, 15, 16, 24, 11, 6, 23, 0, 19, 0, 32, 20, 21, 24, 22, 4, 8, 17, 29, 0, 0, 0, 27, 26, 25, 24, 12, 28, 23, 0, 0, 17, 8, 31, 23, 0, 33, 0, 32, 34, 3, 24],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,4)],[(true,3)],[(true,6)],[(false,7)],[(true,8)],[(true,9),(true,20)],[(true,10),(true,18)],[(false,11),(false,24)],[(true,7),(true,11),(true,24)],[(true,5)],[(false,14)],[(true,15)],[(false,10)],[(true,16)],[(false,18)],[(true,17),(true,19)],[(true,14)],[(true,12)],[(true,22)],[(true,23)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1),(false,34)],[(true,3),(true,21)],[(false,4)],[(true,5),(true,16)],[(false,3)],[(false,7),(false,22),(false,30)],[(true,8)],[(false,9)],[(false,5),(false,16)],[(false,11),(false,27)],[(true,12)],[(false,13)],[(true,10),(true,14)],[(false,15)],[(true,7),(true,11),(true,22),(true,29)],[(false,8),(false,12)],[(false,18)],[(true,19)],[(false,20)],[(false,21)],[(false,17),(false,28),(false,31)],[(true,4),(true,6),(true,9),(true,13),(true,15),(true,20),(true,26),(true,34)],[(false,6),(false,26)],[(true,25)],[(false,25)],[(true,27)],[(false,23)],[(false,10),(false,14)],[(true,30)],[(false,19),(false,33)],[(false,32)],[(true,33)]],
  t0_1243⟩
theorem check0_9 : t0_9.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check10_19 : t10_19.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node9 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,3,21⟩ = true := by decide
theorem check0_19 : t0_19.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node9 check0_9 check10_19
theorem check20_29 : t20_29.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check30_38 : t30_38.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node29 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,8,10⟩ = true := by decide
theorem check20_38 : t20_38.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node29 check20_29 check30_38
theorem node19 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,4,21⟩ = true := by decide
theorem check0_38 : t0_38.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node19 check0_19 check20_38
theorem check39_48 : t39_48.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check49_58 : t49_58.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node48 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,15,3⟩ = true := by decide
theorem check39_58 : t39_58.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node48 check39_48 check49_58
theorem check59_68 : t59_68.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check69_77 : t69_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node68 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,17,7⟩ = true := by decide
theorem check59_77 : t59_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node68 check59_68 check69_77
theorem node58 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,15,23⟩ = true := by decide
theorem check39_77 : t39_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node58 check39_58 check59_77
theorem node38 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,8,22⟩ = true := by decide
theorem check0_77 : t0_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node38 check0_38 check39_77
theorem check78_87 : t78_87.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check88_97 : t88_97.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node87 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,19,0⟩ = true := by decide
theorem check78_97 : t78_97.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node87 check78_87 check88_97
theorem check98_107 : t98_107.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check108_116 : t108_116.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node107 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,19,26⟩ = true := by decide
theorem check98_116 : t98_116.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node107 check98_107 check108_116
theorem node97 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,19,13⟩ = true := by decide
theorem check78_116 : t78_116.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node97 check78_97 check98_116
theorem check117_126 : t117_126.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check127_136 : t127_136.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node126 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,5,31⟩ = true := by decide
theorem check117_136 : t117_136.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node126 check117_126 check127_136
theorem check137_146 : t137_146.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check147_155 : t147_155.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node146 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,9,3⟩ = true := by decide
theorem check137_155 : t137_155.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node146 check137_146 check147_155
theorem node136 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,6,15⟩ = true := by decide
theorem check117_155 : t117_155.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node136 check117_136 check137_155
theorem node116 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,1,15⟩ = true := by decide
theorem check78_155 : t78_155.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node116 check78_116 check117_155
theorem node77 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,17,20⟩ = true := by decide
theorem check0_155 : t0_155.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node77 check0_77 check78_155
theorem check156_165 : t156_165.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check166_175 : t166_175.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node165 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,9,31⟩ = true := by decide
theorem check156_175 : t156_175.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node165 check156_165 check166_175
theorem check176_185 : t176_185.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check186_194 : t186_194.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node185 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,16,9⟩ = true := by decide
theorem check176_194 : t176_194.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node185 check176_185 check186_194
theorem node175 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,10,16⟩ = true := by decide
theorem check156_194 : t156_194.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node175 check156_175 check176_194
theorem check195_204 : t195_204.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check205_214 : t205_214.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node204 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,20,9⟩ = true := by decide
theorem check195_214 : t195_214.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node204 check195_204 check205_214
theorem check215_224 : t215_224.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check225_233 : t225_233.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node224 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,23,8⟩ = true := by decide
theorem check215_233 : t215_233.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node224 check215_224 check225_233
theorem node214 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,20,21⟩ = true := by decide
theorem check195_233 : t195_233.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node214 check195_214 check215_233
theorem node194 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,16,31⟩ = true := by decide
theorem check156_233 : t156_233.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node194 check156_194 check195_233
theorem check234_243 : t234_243.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check244_253 : t244_253.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node243 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,5,1⟩ = true := by decide
theorem check234_253 : t234_253.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node243 check234_243 check244_253
theorem check254_263 : t254_263.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check264_272 : t264_272.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node263 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,6,13⟩ = true := by decide
theorem check254_272 : t254_272.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node263 check254_263 check264_272
theorem node253 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,5,26⟩ = true := by decide
theorem check234_272 : t234_272.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node253 check234_253 check254_272
theorem check273_282 : t273_282.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check283_291 : t283_291.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node282 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,9,14⟩ = true := by decide
theorem check273_291 : t273_291.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node282 check273_282 check283_291
theorem check292_301 : t292_301.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check302_310 : t302_310.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node301 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,10,14⟩ = true := by decide
theorem check292_310 : t292_310.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node301 check292_301 check302_310
theorem node291 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,9,28⟩ = true := by decide
theorem check273_310 : t273_310.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node291 check273_291 check292_310
theorem node272 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,9,1⟩ = true := by decide
theorem check234_310 : t234_310.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node272 check234_272 check273_310
theorem node233 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,0,9⟩ = true := by decide
theorem check156_310 : t156_310.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node233 check156_233 check234_310
theorem node155 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,9,14⟩ = true := by decide
theorem check0_310 : t0_310.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node155 check0_155 check156_310
theorem check311_320 : t311_320.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check321_330 : t321_330.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node320 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,13,3⟩ = true := by decide
theorem check311_330 : t311_330.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node320 check311_320 check321_330
theorem check331_340 : t331_340.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check341_349 : t341_349.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node340 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,16,17⟩ = true := by decide
theorem check331_349 : t331_349.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node340 check331_340 check341_349
theorem node330 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,13,33⟩ = true := by decide
theorem check311_349 : t311_349.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node330 check311_330 check331_349
theorem check350_359 : t350_359.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check360_369 : t360_369.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node359 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,20,14⟩ = true := by decide
theorem check350_369 : t350_369.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node359 check350_359 check360_369
theorem check370_379 : t370_379.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check380_388 : t380_388.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node379 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,23,0⟩ = true := by decide
theorem check370_388 : t370_388.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node379 check370_379 check380_388
theorem node369 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,20,31⟩ = true := by decide
theorem check350_388 : t350_388.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node369 check350_369 check370_388
theorem node349 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,20,1⟩ = true := by decide
theorem check311_388 : t311_388.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node349 check311_349 check350_388
theorem check389_398 : t389_398.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check399_408 : t399_408.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node398 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,10,1⟩ = true := by decide
theorem check389_408 : t389_408.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node398 check389_398 check399_408
theorem check409_418 : t409_418.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check419_427 : t419_427.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node418 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,11,7⟩ = true := by decide
theorem check409_427 : t409_427.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node418 check409_418 check419_427
theorem node408 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,10,22⟩ = true := by decide
theorem check389_427 : t389_427.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node408 check389_408 check409_427
theorem check428_437 : t428_437.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check438_447 : t438_447.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node437 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,18,30⟩ = true := by decide
theorem check428_447 : t428_447.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node437 check428_437 check438_447
theorem check448_457 : t448_457.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check458_466 : t458_466.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node457 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,1,7⟩ = true := by decide
theorem check448_466 : t448_466.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node457 check448_457 check458_466
theorem node447 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,24,15⟩ = true := by decide
theorem check428_466 : t428_466.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node447 check428_447 check448_466
theorem node427 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,11,27⟩ = true := by decide
theorem check389_466 : t389_466.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node427 check389_427 check428_466
theorem node388 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,23,21⟩ = true := by decide
theorem check311_466 : t311_466.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node388 check311_388 check389_466
theorem check467_476 : t467_476.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check477_486 : t477_486.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node476 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,7,10⟩ = true := by decide
theorem check467_486 : t467_486.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node476 check467_476 check477_486
theorem check487_496 : t487_496.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check497_505 : t497_505.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node496 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,10,12⟩ = true := by decide
theorem check487_505 : t487_505.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node496 check487_496 check497_505
theorem node486 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,7,29⟩ = true := by decide
theorem check467_505 : t467_505.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node486 check467_486 check487_505
theorem check506_515 : t506_515.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check516_525 : t516_525.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node515 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,14,22⟩ = true := by decide
theorem check506_525 : t506_525.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node515 check506_515 check516_525
theorem check526_535 : t526_535.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check536_544 : t536_544.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node535 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,18,29⟩ = true := by decide
theorem check526_544 : t526_544.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node535 check526_535 check536_544
theorem node525 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,18,10⟩ = true := by decide
theorem check506_544 : t506_544.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node525 check506_525 check526_544
theorem node505 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,10,30⟩ = true := by decide
theorem check467_544 : t467_544.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node505 check467_505 check506_544
theorem check545_554 : t545_554.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check555_564 : t555_564.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node554 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,11,15⟩ = true := by decide
theorem check545_564 : t545_564.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node554 check545_554 check555_564
theorem check565_574 : t565_574.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check575_583 : t575_583.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node574 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,17,10⟩ = true := by decide
theorem check565_583 : t565_583.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node574 check565_574 check575_583
theorem node564 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,12,14⟩ = true := by decide
theorem check545_583 : t545_583.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node564 check545_564 check565_583
theorem check584_593 : t584_593.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check594_602 : t594_602.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node593 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,19,5⟩ = true := by decide
theorem check584_602 : t584_602.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node593 check584_593 check594_602
theorem check603_612 : t603_612.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check613_621 : t613_621.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node612 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,1,2⟩ = true := by decide
theorem check603_621 : t603_621.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node612 check603_612 check613_621
theorem node602 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,19,33⟩ = true := by decide
theorem check584_621 : t584_621.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node602 check584_602 check603_621
theorem node583 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,18,4⟩ = true := by decide
theorem check545_621 : t545_621.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node583 check545_583 check584_621
theorem node544 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,10,13⟩ = true := by decide
theorem check467_621 : t467_621.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node544 check467_544 check545_621
theorem node466 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,2,14⟩ = true := by decide
theorem check311_621 : t311_621.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node466 check311_466 check467_621
theorem node310 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,11,8⟩ = true := by decide
theorem check0_621 : t0_621.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node310 check0_310 check311_621
theorem check622_631 : t622_631.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check632_641 : t632_641.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node631 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,12,21⟩ = true := by decide
theorem check622_641 : t622_641.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node631 check622_631 check632_641
theorem check642_651 : t642_651.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check652_660 : t652_660.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node651 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,20,24⟩ = true := by decide
theorem check642_660 : t642_660.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node651 check642_651 check652_660
theorem node641 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,17,12⟩ = true := by decide
theorem check622_660 : t622_660.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node641 check622_641 check642_660
theorem check661_670 : t661_670.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check671_680 : t671_680.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node670 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,9,22⟩ = true := by decide
theorem check661_680 : t661_680.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node670 check661_670 check671_680
theorem check681_690 : t681_690.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check691_699 : t691_699.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node690 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,11,26⟩ = true := by decide
theorem check681_699 : t681_699.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node690 check681_690 check691_699
theorem node680 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,10,20⟩ = true := by decide
theorem check661_699 : t661_699.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node680 check661_680 check681_699
theorem node660 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,7,9⟩ = true := by decide
theorem check622_699 : t622_699.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node660 check622_660 check661_699
theorem check700_709 : t700_709.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check710_719 : t710_719.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node709 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,20,7⟩ = true := by decide
theorem check700_719 : t700_719.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node709 check700_709 check710_719
theorem check720_729 : t720_729.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check730_738 : t730_738.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node729 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,22,13⟩ = true := by decide
theorem check720_738 : t720_738.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node729 check720_729 check730_738
theorem node719 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,20,30⟩ = true := by decide
theorem check700_738 : t700_738.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node719 check700_719 check720_738
theorem check739_748 : t739_748.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check749_758 : t749_758.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node748 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,0,4⟩ = true := by decide
theorem check739_758 : t739_758.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node748 check739_748 check749_758
theorem check759_768 : t759_768.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check769_777 : t769_777.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node768 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,4,3⟩ = true := by decide
theorem check759_777 : t759_777.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node768 check759_768 check769_777
theorem node758 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,3,10⟩ = true := by decide
theorem check739_777 : t739_777.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node758 check739_758 check759_777
theorem node738 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,22,34⟩ = true := by decide
theorem check700_777 : t700_777.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node738 check700_738 check739_777
theorem node699 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,18,9⟩ = true := by decide
theorem check622_777 : t622_777.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node699 check622_699 check700_777
theorem check778_787 : t778_787.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check788_797 : t788_797.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node787 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,8,0⟩ = true := by decide
theorem check778_797 : t778_797.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node787 check778_787 check788_797
theorem check798_807 : t798_807.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check808_816 : t808_816.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node807 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,8,26⟩ = true := by decide
theorem check798_816 : t798_816.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node807 check798_807 check808_816
theorem node797 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,8,13⟩ = true := by decide
theorem check778_816 : t778_816.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node797 check778_797 check798_816
theorem check817_826 : t817_826.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check827_836 : t827_836.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node826 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,9,30⟩ = true := by decide
theorem check817_836 : t817_836.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node826 check817_826 check827_836
theorem check837_846 : t837_846.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check847_855 : t847_855.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node846 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,11,0⟩ = true := by decide
theorem check837_855 : t837_855.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node846 check837_846 check847_855
theorem node836 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,10,13⟩ = true := by decide
theorem check817_855 : t817_855.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node836 check817_836 check837_855
theorem node816 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,9,7⟩ = true := by decide
theorem check778_855 : t778_855.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node816 check778_816 check817_855
theorem check856_865 : t856_865.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check866_875 : t866_875.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node865 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,14,22⟩ = true := by decide
theorem check856_875 : t856_875.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node865 check856_865 check866_875
theorem check876_885 : t876_885.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check886_894 : t886_894.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node885 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,15,26⟩ = true := by decide
theorem check876_894 : t876_894.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node885 check876_885 check886_894
theorem node875 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,15,10⟩ = true := by decide
theorem check856_894 : t856_894.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node875 check856_875 check876_894
theorem check895_904 : t895_904.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check905_913 : t905_913.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node904 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,17,9⟩ = true := by decide
theorem check895_913 : t895_913.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node904 check895_904 check905_913
theorem check914_923 : t914_923.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check924_932 : t924_932.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node923 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,18,1⟩ = true := by decide
theorem check914_932 : t914_932.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node923 check914_923 check924_932
theorem node913 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,17,21⟩ = true := by decide
theorem check895_932 : t895_932.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node913 check895_913 check914_932
theorem node894 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,16,20⟩ = true := by decide
theorem check856_932 : t856_932.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node894 check856_894 check895_932
theorem node855 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,11,18⟩ = true := by decide
theorem check778_932 : t778_932.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node855 check778_855 check856_932
theorem node777 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,4,25⟩ = true := by decide
theorem check622_932 : t622_932.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node777 check622_777 check778_932
theorem check933_942 : t933_942.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check943_952 : t943_952.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node942 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,19,4⟩ = true := by decide
theorem check933_952 : t933_952.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node942 check933_942 check943_952
theorem check953_962 : t953_962.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check963_971 : t963_971.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node962 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,19,32⟩ = true := by decide
theorem check953_971 : t953_971.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node962 check953_962 check963_971
theorem node952 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,19,16⟩ = true := by decide
theorem check933_971 : t933_971.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node952 check933_952 check953_971
theorem check972_981 : t972_981.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check982_991 : t982_991.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node981 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,22,0⟩ = true := by decide
theorem check972_991 : t972_991.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node981 check972_981 check982_991
theorem check992_1001 : t992_1001.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1002_1010 : t1002_1010.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1001 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,24,6⟩ = true := by decide
theorem check992_1010 : t992_1010.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1001 check992_1001 check1002_1010
theorem node991 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,22,20⟩ = true := by decide
theorem check972_1010 : t972_1010.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node991 check972_991 check992_1010
theorem node971 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,20,13⟩ = true := by decide
theorem check933_1010 : t933_1010.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node971 check933_971 check972_1010
theorem check1011_1020 : t1011_1020.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1021_1030 : t1021_1030.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1020 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,1,8⟩ = true := by decide
theorem check1011_1030 : t1011_1030.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1020 check1011_1020 check1021_1030
theorem check1031_1040 : t1031_1040.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1041_1049 : t1041_1049.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1040 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,7,5⟩ = true := by decide
theorem check1031_1049 : t1031_1049.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1040 check1031_1040 check1041_1049
theorem node1030 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,2,11⟩ = true := by decide
theorem check1011_1049 : t1011_1049.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1030 check1011_1030 check1031_1049
theorem check1050_1059 : t1050_1059.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1060_1069 : t1060_1069.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1059 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,10,7⟩ = true := by decide
theorem check1050_1069 : t1050_1069.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1059 check1050_1059 check1060_1069
theorem check1070_1079 : t1070_1079.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1080_1088 : t1080_1088.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1079 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,14,11⟩ = true := by decide
theorem check1070_1088 : t1070_1088.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1079 check1070_1079 check1080_1088
theorem node1069 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,10,25⟩ = true := by decide
theorem check1050_1088 : t1050_1088.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1069 check1050_1069 check1070_1088
theorem node1049 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,7,21⟩ = true := by decide
theorem check1011_1088 : t1011_1088.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1049 check1011_1049 check1050_1088
theorem node1010 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,24,26⟩ = true := by decide
theorem check933_1088 : t933_1088.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1010 check933_1010 check1011_1088
theorem check1089_1098 : t1089_1098.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1099_1108 : t1099_1108.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1098 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,18,14⟩ = true := by decide
theorem check1089_1108 : t1089_1108.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1098 check1089_1098 check1099_1108
theorem check1109_1118 : t1109_1118.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1119_1127 : t1119_1127.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1118 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,8,5⟩ = true := by decide
theorem check1109_1127 : t1109_1127.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1118 check1109_1118 check1119_1127
theorem node1108 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,1,3⟩ = true := by decide
theorem check1089_1127 : t1089_1127.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1108 check1089_1108 check1109_1127
theorem check1128_1137 : t1128_1137.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1138_1147 : t1138_1147.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1137 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,9,21⟩ = true := by decide
theorem check1128_1147 : t1128_1147.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1137 check1128_1137 check1138_1147
theorem check1148_1157 : t1148_1157.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1158_1166 : t1158_1166.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1157 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,12,12⟩ = true := by decide
theorem check1148_1166 : t1148_1166.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1157 check1148_1157 check1158_1166
theorem node1147 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,10,16⟩ = true := by decide
theorem check1128_1166 : t1128_1166.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1147 check1128_1147 check1148_1166
theorem node1127 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,8,33⟩ = true := by decide
theorem check1089_1166 : t1089_1166.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1127 check1089_1127 check1128_1166
theorem check1167_1176 : t1167_1176.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1177_1186 : t1177_1186.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1176 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,16,12⟩ = true := by decide
theorem check1167_1186 : t1167_1186.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1176 check1167_1176 check1177_1186
theorem check1187_1196 : t1187_1196.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1197_1205 : t1197_1205.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1196 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,18,3⟩ = true := by decide
theorem check1187_1205 : t1187_1205.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1196 check1187_1196 check1197_1205
theorem node1186 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,17,8⟩ = true := by decide
theorem check1167_1205 : t1167_1205.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1186 check1167_1186 check1187_1205
theorem check1206_1215 : t1206_1215.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1216_1224 : t1216_1224.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1215 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,19,19⟩ = true := by decide
theorem check1206_1224 : t1206_1224.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1215 check1206_1215 check1216_1224
theorem check1225_1234 : t1225_1234.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check1235_1243 : t1235_1243.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node1234 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,23,8⟩ = true := by decide
theorem check1225_1243 : t1225_1243.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1234 check1225_1234 check1235_1243
theorem node1224 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,20,12⟩ = true := by decide
theorem check1206_1243 : t1206_1243.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1224 check1206_1224 check1225_1243
theorem node1205 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,18,25⟩ = true := by decide
theorem check1167_1243 : t1167_1243.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1205 check1167_1205 check1206_1243
theorem node1166 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,15,10⟩ = true := by decide
theorem check1089_1243 : t1089_1243.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1166 check1089_1166 check1167_1243
theorem node1088 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,14,30⟩ = true := by decide
theorem check933_1243 : t933_1243.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node1088 check933_1088 check1089_1243
theorem node932 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,18,20⟩ = true := by decide
theorem check622_1243 : t622_1243.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node932 check622_932 check933_1243
theorem node621 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,10,24⟩ = true := by decide
theorem check0_1243 : t0_1243.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node621 check0_621 check622_1243
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_1243
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M077
