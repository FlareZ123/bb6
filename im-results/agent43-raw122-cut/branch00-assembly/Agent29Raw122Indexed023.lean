import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M023
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_16 : Tree := (.node (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,5⟩ .empty) ⟨0,false,0,10⟩ (.node .empty ⟨0,false,0,18⟩ .empty)) ⟨0,false,0,23⟩ (.node (.node .empty ⟨0,false,0,43⟩ .empty) ⟨0,false,0,48⟩ (.node .empty ⟨0,false,0,59⟩ .empty))) ⟨0,false,2,25⟩ (.node (.node (.node .empty ⟨0,false,2,48⟩ .empty) ⟨0,false,2,50⟩ (.node .empty ⟨0,false,2,61⟩ .empty)) ⟨0,false,2,97⟩ (.node (.node .empty ⟨0,false,7,5⟩ .empty) ⟨0,false,16,35⟩ (.node .empty ⟨0,false,16,48⟩ .empty))))
def t17_33 : Tree := (.node (.node (.node (.node (.node .empty ⟨0,false,16,61⟩ .empty) ⟨0,false,16,63⟩ .empty) ⟨0,false,16,81⟩ (.node .empty ⟨0,false,16,97⟩ .empty)) ⟨0,false,20,31⟩ (.node (.node .empty ⟨0,false,22,11⟩ .empty) ⟨0,false,30,35⟩ (.node .empty ⟨0,false,30,48⟩ .empty))) ⟨0,false,30,50⟩ (.node (.node (.node .empty ⟨0,false,30,61⟩ .empty) ⟨0,false,30,63⟩ (.node .empty ⟨0,false,30,81⟩ .empty)) ⟨0,false,30,97⟩ (.node (.node .empty ⟨0,false,34,73⟩ .empty) ⟨0,false,36,34⟩ (.node .empty ⟨0,false,36,64⟩ .empty))))
def t0_33 : Tree := .node t0_16 ⟨0,false,16,50⟩ t17_33
def t34_50 : Tree := (.node (.node (.node (.node (.node .empty ⟨0,false,36,92⟩ .empty) ⟨0,true,0,4⟩ .empty) ⟨0,true,0,17⟩ (.node .empty ⟨0,true,0,42⟩ .empty)) ⟨0,true,0,46⟩ (.node (.node .empty ⟨0,true,0,58⟩ .empty) ⟨0,true,1,16⟩ (.node .empty ⟨0,true,1,41⟩ .empty))) ⟨0,true,1,43⟩ (.node (.node (.node .empty ⟨0,true,1,57⟩ .empty) ⟨0,true,1,59⟩ (.node .empty ⟨0,true,1,100⟩ .empty)) ⟨0,true,2,29⟩ (.node (.node .empty ⟨0,true,2,40⟩ .empty) ⟨0,true,2,42⟩ (.node .empty ⟨0,true,2,46⟩ .empty))))
def t51_66 : Tree := (.node (.node (.node (.node .empty ⟨0,true,2,58⟩ .empty) ⟨0,true,2,94⟩ (.node .empty ⟨0,true,8,4⟩ .empty)) ⟨0,true,14,37⟩ (.node (.node .empty ⟨0,true,14,39⟩ .empty) ⟨0,true,14,41⟩ (.node .empty ⟨0,true,14,43⟩ .empty))) ⟨0,true,14,55⟩ (.node (.node (.node .empty ⟨0,true,14,57⟩ .empty) ⟨0,true,14,59⟩ (.node .empty ⟨0,true,14,100⟩ .empty)) ⟨0,true,14,111⟩ (.node (.node .empty ⟨0,true,16,36⟩ .empty) ⟨0,true,16,40⟩ (.node .empty ⟨0,true,16,42⟩ .empty))))
def t34_66 : Tree := .node t34_50 ⟨0,true,2,56⟩ t51_66
def t0_66 : Tree := .node t0_33 ⟨0,false,36,80⟩ t34_66
def t67_83 : Tree := (.node (.node (.node (.node (.node .empty ⟨0,true,16,54⟩ .empty) ⟨0,true,16,56⟩ .empty) ⟨0,true,16,58⟩ (.node .empty ⟨0,true,16,94⟩ .empty)) ⟨0,true,16,110⟩ (.node (.node .empty ⟨0,true,21,30⟩ .empty) ⟨0,true,22,10⟩ (.node .empty ⟨0,true,28,33⟩ .empty))) ⟨0,true,28,37⟩ (.node (.node (.node .empty ⟨0,true,28,39⟩ .empty) ⟨0,true,28,41⟩ (.node .empty ⟨0,true,28,43⟩ .empty)) ⟨0,true,28,55⟩ (.node (.node .empty ⟨0,true,28,57⟩ .empty) ⟨0,true,28,59⟩ (.node .empty ⟨0,true,28,85⟩ .empty))))
def t84_99 : Tree := (.node (.node (.node (.node .empty ⟨0,true,28,109⟩ .empty) ⟨0,true,28,111⟩ (.node .empty ⟨0,true,30,36⟩ .empty)) ⟨0,true,30,40⟩ (.node (.node .empty ⟨0,true,30,42⟩ .empty) ⟨0,true,30,46⟩ (.node .empty ⟨0,true,30,54⟩ .empty))) ⟨0,true,30,56⟩ (.node (.node (.node .empty ⟨0,true,30,58⟩ .empty) ⟨0,true,30,94⟩ (.node .empty ⟨0,true,30,110⟩ .empty)) ⟨0,true,35,70⟩ (.node (.node .empty ⟨0,true,35,71⟩ .empty) ⟨0,true,35,72⟩ (.node .empty ⟨0,true,35,89⟩ .empty))))
def t67_99 : Tree := .node t67_83 ⟨0,true,28,100⟩ t84_99
def t100_116 : Tree := (.node (.node (.node (.node (.node .empty ⟨0,true,36,45⟩ .empty) ⟨0,true,36,50⟩ .empty) ⟨0,true,36,68⟩ (.node .empty ⟨0,true,36,69⟩ .empty)) ⟨0,true,36,88⟩ (.node (.node .empty ⟨0,true,36,97⟩ .empty) ⟨0,true,36,102⟩ (.node .empty ⟨0,true,42,33⟩ .empty))) ⟨0,true,42,37⟩ (.node (.node (.node .empty ⟨0,true,42,39⟩ .empty) ⟨0,true,42,41⟩ (.node .empty ⟨0,true,42,43⟩ .empty)) ⟨0,true,42,55⟩ (.node (.node .empty ⟨0,true,42,57⟩ .empty) ⟨0,true,42,59⟩ (.node .empty ⟨0,true,42,85⟩ .empty))))
def t117_132 : Tree := (.node (.node (.node (.node .empty ⟨0,true,42,109⟩ .empty) ⟨0,true,42,111⟩ (.node .empty ⟨1,false,0,7⟩ .empty)) ⟨1,false,0,20⟩ (.node (.node .empty ⟨1,false,0,45⟩ .empty) ⟨1,false,1,0⟩ (.node .empty ⟨1,false,1,9⟩ .empty))) ⟨1,false,1,22⟩ (.node (.node (.node .empty ⟨1,false,1,47⟩ .empty) ⟨1,false,2,12⟩ (.node .empty ⟨1,false,5,3⟩ .empty)) ⟨1,false,9,0⟩ (.node (.node .empty ⟨1,false,14,24⟩ .empty) ⟨1,false,14,47⟩ (.node .empty ⟨1,false,14,49⟩ .empty))))
def t100_132 : Tree := .node t100_116 ⟨0,true,42,100⟩ t117_132
def t67_132 : Tree := .node t67_99 ⟨0,true,35,103⟩ t100_132
def t0_132 : Tree := .node t0_66 ⟨0,true,16,46⟩ t67_132
def t133_149 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,false,14,95⟩ .empty) ⟨1,false,16,35⟩ .empty) ⟨1,false,18,28⟩ (.node .empty ⟨1,false,24,7⟩ .empty)) ⟨1,false,28,34⟩ (.node (.node .empty ⟨1,false,28,47⟩ .empty) ⟨1,false,28,49⟩ (.node .empty ⟨1,false,28,60⟩ .empty))) ⟨1,false,28,62⟩ (.node (.node (.node .empty ⟨1,false,28,80⟩ .empty) ⟨1,false,28,95⟩ (.node .empty ⟨1,false,30,81⟩ .empty)) ⟨1,false,30,93⟩ (.node (.node .empty ⟨1,false,32,53⟩ .empty) ⟨1,false,38,10⟩ (.node .empty ⟨1,false,38,33⟩ .empty))))
def t150_165 : Tree := (.node (.node (.node (.node .empty ⟨1,false,38,50⟩ .empty) ⟨1,false,38,68⟩ (.node .empty ⟨1,false,38,69⟩ .empty)) ⟨1,false,38,77⟩ (.node (.node .empty ⟨1,false,38,78⟩ .empty) ⟨1,false,38,79⟩ (.node .empty ⟨1,false,38,85⟩ .empty))) ⟨1,false,38,91⟩ (.node (.node (.node .empty ⟨1,false,38,97⟩ .empty) ⟨1,false,38,105⟩ (.node .empty ⟨1,false,42,34⟩ .empty)) ⟨1,false,42,47⟩ (.node (.node .empty ⟨1,false,42,49⟩ .empty) ⟨1,false,42,60⟩ (.node .empty ⟨1,false,42,62⟩ .empty))))
def t133_165 : Tree := .node t133_149 ⟨1,false,38,39⟩ t150_165
def t166_182 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,false,42,95⟩ .empty) ⟨1,true,0,6⟩ .empty) ⟨1,true,0,19⟩ (.node .empty ⟨1,true,0,44⟩ .empty)) ⟨1,true,1,4⟩ (.node (.node .empty ⟨1,true,1,17⟩ .empty) ⟨1,true,1,42⟩ (.node .empty ⟨1,true,1,46⟩ .empty))) ⟨1,true,1,58⟩ (.node (.node (.node .empty ⟨1,true,3,11⟩ .empty) ⟨1,true,5,7⟩ (.node .empty ⟨1,true,7,6⟩ .empty)) ⟨1,true,13,4⟩ (.node (.node .empty ⟨1,true,17,34⟩ .empty) ⟨1,true,18,33⟩ (.node .empty ⟨1,true,20,32⟩ .empty))))
def t183_198 : Tree := (.node (.node (.node (.node .empty ⟨1,true,31,80⟩ .empty) ⟨1,true,31,92⟩ (.node .empty ⟨1,true,32,77⟩ .empty)) ⟨1,true,32,78⟩ (.node (.node .empty ⟨1,true,32,79⟩ .empty) ⟨1,true,32,91⟩ (.node .empty ⟨1,true,32,105⟩ .empty))) ⟨1,true,34,74⟩ (.node (.node (.node .empty ⟨1,true,34,75⟩ .empty) ⟨1,true,34,76⟩ (.node .empty ⟨1,true,34,90⟩ .empty)) ⟨1,true,34,104⟩ (.node (.node .empty ⟨1,true,41,70⟩ .empty) ⟨1,true,41,71⟩ (.node .empty ⟨1,true,41,72⟩ .empty))))
def t166_198 : Tree := .node t166_182 ⟨1,true,27,30⟩ t183_198
def t133_198 : Tree := .node t133_165 ⟨1,false,42,80⟩ t166_198
def t199_215 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,true,41,103⟩ .empty) ⟨2,false,1,6⟩ .empty) ⟨2,false,1,19⟩ (.node .empty ⟨2,false,1,44⟩ .empty)) ⟨2,false,2,0⟩ (.node (.node .empty ⟨2,false,2,5⟩ .empty) ⟨2,false,2,18⟩ (.node .empty ⟨2,false,2,43⟩ .empty))) ⟨2,false,2,59⟩ (.node (.node (.node .empty ⟨2,false,2,100⟩ .empty) ⟨2,false,7,1⟩ (.node .empty ⟨2,false,11,0⟩ .empty)) ⟨2,false,14,11⟩ (.node (.node .empty ⟨2,false,16,16⟩ .empty) ⟨2,false,16,37⟩ (.node .empty ⟨2,false,16,41⟩ .empty))))
def t216_231 : Tree := (.node (.node (.node (.node .empty ⟨2,false,16,57⟩ .empty) ⟨2,false,16,59⟩ (.node .empty ⟨2,false,16,83⟩ .empty)) ⟨2,false,16,100⟩ (.node (.node .empty ⟨2,false,16,111⟩ .empty) ⟨2,false,20,26⟩ (.node .empty ⟨2,false,25,6⟩ .empty))) ⟨2,false,28,34⟩ (.node (.node (.node .empty ⟨2,false,30,33⟩ .empty) ⟨2,false,30,37⟩ (.node .empty ⟨2,false,30,39⟩ .empty)) ⟨2,false,30,41⟩ (.node (.node .empty ⟨2,false,30,43⟩ .empty) ⟨2,false,30,55⟩ (.node .empty ⟨2,false,30,57⟩ .empty))))
def t199_231 : Tree := .node t199_215 ⟨2,false,16,43⟩ t216_231
def t232_248 : Tree := (.node (.node (.node (.node (.node .empty ⟨2,false,30,77⟩ .empty) ⟨2,false,30,78⟩ .empty) ⟨2,false,30,79⟩ (.node .empty ⟨2,false,30,83⟩ .empty)) ⟨2,false,30,85⟩ (.node (.node .empty ⟨2,false,30,100⟩ .empty) ⟨2,false,30,109⟩ (.node .empty ⟨2,false,30,111⟩ .empty))) ⟨2,false,34,51⟩ (.node (.node (.node .empty ⟨2,false,39,9⟩ .empty) ⟨2,false,39,32⟩ (.node .empty ⟨2,false,39,38⟩ .empty)) ⟨2,false,39,49⟩ (.node (.node .empty ⟨2,false,39,66⟩ .empty) ⟨2,false,39,67⟩ (.node .empty ⟨2,false,39,74⟩ .empty))))
def t249_264 : Tree := (.node (.node (.node (.node .empty ⟨2,false,39,76⟩ .empty) ⟨2,false,39,84⟩ (.node .empty ⟨2,false,39,90⟩ .empty)) ⟨2,false,39,95⟩ (.node (.node .empty ⟨2,false,39,99⟩ .empty) ⟨2,false,39,104⟩ (.node .empty ⟨2,false,42,80⟩ .empty))) ⟨2,false,42,92⟩ (.node (.node (.node .empty ⟨3,false,1,5⟩ .empty) ⟨3,false,1,18⟩ (.node .empty ⟨3,false,1,43⟩ .empty)) ⟨3,false,1,59⟩ (.node (.node .empty ⟨3,false,2,1⟩ .empty) ⟨3,false,3,0⟩ (.node .empty ⟨3,false,4,4⟩ .empty))))
def t232_264 : Tree := .node t232_248 ⟨2,false,39,75⟩ t249_264
def t199_264 : Tree := .node t199_231 ⟨2,false,30,59⟩ t232_264
def t133_264 : Tree := .node t133_198 ⟨1,true,41,89⟩ t199_264
def t0_264 : Tree := .node t0_132 ⟨1,false,14,60⟩ t133_264
def t265_281 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,false,4,42⟩ .empty) ⟨3,false,4,46⟩ .empty) ⟨3,false,4,58⟩ (.node .empty ⟨3,false,11,1⟩ .empty)) ⟨3,false,12,0⟩ (.node (.node .empty ⟨3,false,14,13⟩ .empty) ⟨3,false,15,7⟩ (.node .empty ⟨3,false,16,26⟩ .empty))) ⟨3,false,17,15⟩ (.node (.node (.node .empty ⟨3,false,25,5⟩ .empty) ⟨3,false,26,4⟩ (.node .empty ⟨3,false,28,36⟩ .empty)) ⟨3,false,28,40⟩ (.node (.node .empty ⟨3,false,29,33⟩ .empty) ⟨3,false,29,39⟩ (.node .empty ⟨3,false,29,85⟩ .empty))))
def t282_298 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,false,31,32⟩ .empty) ⟨3,false,31,38⟩ .empty) ⟨3,false,31,74⟩ (.node .empty ⟨3,false,31,75⟩ .empty)) ⟨3,false,31,76⟩ (.node (.node .empty ⟨3,false,31,84⟩ .empty) ⟨3,false,31,99⟩ (.node .empty ⟨3,false,31,108⟩ .empty))) ⟨3,false,39,8⟩ (.node (.node (.node .empty ⟨3,false,39,31⟩ .empty) ⟨3,false,39,37⟩ (.node .empty ⟨3,false,39,41⟩ .empty)) ⟨3,false,39,42⟩ (.node (.node .empty ⟨3,false,39,65⟩ .empty) ⟨3,false,39,73⟩ (.node .empty ⟨3,false,39,83⟩ .empty))))
def t265_298 : Tree := .node t265_281 ⟨3,false,30,51⟩ t282_298
def t299_315 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,false,39,98⟩ .empty) ⟨3,false,40,5⟩ .empty) ⟨3,false,40,8⟩ (.node .empty ⟨3,false,40,30⟩ .empty)) ⟨3,false,40,31⟩ (.node (.node .empty ⟨3,false,40,36⟩ .empty) ⟨3,false,40,37⟩ (.node .empty ⟨3,false,40,40⟩ .empty))) ⟨3,false,40,41⟩ (.node (.node (.node .empty ⟨3,false,40,70⟩ .empty) ⟨3,false,40,71⟩ (.node .empty ⟨3,false,40,72⟩ .empty)) ⟨3,false,40,82⟩ (.node (.node .empty ⟨3,false,40,83⟩ .empty) ⟨3,false,40,89⟩ (.node .empty ⟨3,false,40,96⟩ .empty))))
def t316_331 : Tree := (.node (.node (.node (.node .empty ⟨3,false,40,103⟩ .empty) ⟨3,false,40,111⟩ (.node .empty ⟨3,false,42,36⟩ .empty)) ⟨3,false,42,40⟩ (.node (.node .empty ⟨3,false,42,82⟩ .empty) ⟨3,false,42,96⟩ (.node .empty ⟨3,false,42,106⟩ .empty))) ⟨3,false,43,77⟩ (.node (.node (.node .empty ⟨3,false,43,78⟩ .empty) ⟨3,false,43,79⟩ (.node .empty ⟨3,false,43,91⟩ .empty)) ⟨3,false,43,105⟩ (.node (.node .empty ⟨3,true,0,8⟩ .empty) ⟨3,true,0,21⟩ (.node .empty ⟨3,true,0,46⟩ .empty))))
def t299_331 : Tree := .node t299_315 ⟨3,false,40,98⟩ t316_331
def t265_331 : Tree := .node t265_298 ⟨3,false,39,94⟩ t299_331
def t332_348 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,true,2,14⟩ .empty) ⟨3,true,3,4⟩ .empty) ⟨3,true,3,17⟩ (.node .empty ⟨3,true,3,42⟩ .empty)) ⟨3,true,3,46⟩ (.node (.node .empty ⟨3,true,3,58⟩ .empty) ⟨3,true,3,94⟩ (.node .empty ⟨3,true,8,0⟩ .empty))) ⟨3,true,9,2⟩ (.node (.node (.node .empty ⟨3,true,14,27⟩ .empty) ⟨3,true,16,37⟩ (.node .empty ⟨3,true,16,41⟩ .empty)) ⟨3,true,17,29⟩ (.node (.node .empty ⟨3,true,17,36⟩ .empty) ⟨3,true,17,40⟩ (.node .empty ⟨3,true,17,42⟩ .empty))))
def t349_364 : Tree := (.node (.node (.node (.node .empty ⟨3,true,17,56⟩ .empty) ⟨3,true,17,58⟩ (.node .empty ⟨3,true,17,82⟩ .empty)) ⟨3,true,17,94⟩ (.node (.node .empty ⟨3,true,17,110⟩ .empty) ⟨3,true,21,15⟩ (.node .empty ⟨3,true,24,8⟩ .empty))) ⟨3,true,28,52⟩ (.node (.node (.node .empty ⟨3,true,30,37⟩ .empty) ⟨3,true,30,41⟩ (.node .empty ⟨3,true,30,83⟩ .empty)) ⟨3,true,30,98⟩ (.node (.node .empty ⟨3,true,30,107⟩ .empty) ⟨3,true,31,36⟩ (.node .empty ⟨3,true,31,40⟩ .empty))))
def t332_364 : Tree := .node t332_348 ⟨3,true,17,46⟩ t349_364
def t365_381 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,true,31,46⟩ .empty) ⟨3,true,31,54⟩ .empty) ⟨3,true,31,56⟩ (.node .empty ⟨3,true,31,58⟩ .empty)) ⟨3,true,31,82⟩ (.node (.node .empty ⟨3,true,31,94⟩ .empty) ⟨3,true,31,110⟩ (.node .empty ⟨3,true,35,32⟩ .empty))) ⟨3,true,35,38⟩ (.node (.node (.node .empty ⟨3,true,35,74⟩ .empty) ⟨3,true,35,75⟩ (.node .empty ⟨3,true,35,76⟩ .empty)) ⟨3,true,35,84⟩ (.node (.node .empty ⟨3,true,35,99⟩ .empty) ⟨3,true,35,108⟩ (.node .empty ⟨3,true,38,42⟩ .empty))))
def t382_397 : Tree := (.node (.node (.node (.node .empty ⟨3,true,38,65⟩ .empty) ⟨3,true,38,86⟩ (.node .empty ⟨3,true,38,94⟩ .empty)) ⟨3,true,38,100⟩ (.node (.node .empty ⟨3,true,42,52⟩ .empty) ⟨4,false,5,3⟩ (.node .empty ⟨4,false,9,0⟩ .empty))) ⟨4,false,18,28⟩ (.node (.node (.node .empty ⟨4,false,22,13⟩ .empty) ⟨4,false,32,53⟩ (.node .empty ⟨4,false,36,30⟩ .empty)) ⟨4,false,36,36⟩ (.node (.node .empty ⟨4,false,36,40⟩ .empty) ⟨4,false,36,70⟩ (.node .empty ⟨4,false,36,71⟩ .empty))))
def t365_397 : Tree := .node t365_381 ⟨3,true,38,43⟩ t382_397
def t332_397 : Tree := .node t332_364 ⟨3,true,31,42⟩ t365_397
def t265_397 : Tree := .node t265_331 ⟨3,true,1,2⟩ t332_397
def t398_414 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,false,36,82⟩ .empty) ⟨4,false,36,96⟩ .empty) ⟨4,false,36,106⟩ (.node .empty ⟨4,true,1,5⟩ .empty)) ⟨4,true,1,18⟩ (.node (.node .empty ⟨4,true,1,43⟩ .empty) ⟨4,true,1,59⟩ (.node .empty ⟨4,true,2,1⟩ .empty))) ⟨4,true,5,16⟩ (.node (.node (.node .empty ⟨4,true,5,37⟩ .empty) ⟨4,true,5,41⟩ (.node .empty ⟨4,true,5,43⟩ .empty)) ⟨4,true,5,57⟩ (.node (.node .empty ⟨4,true,5,59⟩ .empty) ⟨4,true,5,83⟩ (.node .empty ⟨4,true,5,100⟩ .empty))))
def t415_430 : Tree := (.node (.node (.node (.node .empty ⟨4,true,11,1⟩ .empty) ⟨4,true,14,13⟩ (.node .empty ⟨4,true,16,26⟩ .empty)) ⟨4,true,18,33⟩ (.node (.node .empty ⟨4,true,18,37⟩ .empty) ⟨4,true,18,39⟩ (.node .empty ⟨4,true,18,41⟩ .empty))) ⟨4,true,18,43⟩ (.node (.node (.node .empty ⟨4,true,18,55⟩ .empty) ⟨4,true,18,57⟩ (.node .empty ⟨4,true,18,59⟩ .empty)) ⟨4,true,18,77⟩ (.node (.node .empty ⟨4,true,18,78⟩ .empty) ⟨4,true,18,79⟩ (.node .empty ⟨4,true,18,83⟩ .empty))))
def t398_430 : Tree := .node t398_414 ⟨4,true,5,111⟩ t415_430
def t431_447 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,true,18,100⟩ .empty) ⟨4,true,18,109⟩ .empty) ⟨4,true,18,111⟩ (.node .empty ⟨4,true,25,5⟩ .empty)) ⟨4,true,28,36⟩ (.node (.node .empty ⟨4,true,28,40⟩ .empty) ⟨4,true,30,51⟩ (.node .empty ⟨4,true,32,33⟩ .empty))) ⟨4,true,32,37⟩ (.node (.node (.node .empty ⟨4,true,32,39⟩ .empty) ⟨4,true,32,41⟩ (.node .empty ⟨4,true,32,43⟩ .empty)) ⟨4,true,32,55⟩ (.node (.node .empty ⟨4,true,32,57⟩ .empty) ⟨4,true,32,59⟩ (.node .empty ⟨4,true,32,77⟩ .empty))))
def t448_463 : Tree := (.node (.node (.node (.node .empty ⟨4,true,32,79⟩ .empty) ⟨4,true,32,83⟩ (.node .empty ⟨4,true,32,85⟩ .empty)) ⟨4,true,32,100⟩ (.node (.node .empty ⟨4,true,32,109⟩ .empty) ⟨4,true,32,111⟩ (.node .empty ⟨4,true,39,8⟩ .empty))) ⟨4,true,39,31⟩ (.node (.node (.node .empty ⟨4,true,39,37⟩ .empty) ⟨4,true,39,41⟩ (.node .empty ⟨4,true,39,42⟩ .empty)) ⟨4,true,39,65⟩ (.node (.node .empty ⟨4,true,39,73⟩ .empty) ⟨4,true,39,83⟩ (.node .empty ⟨4,true,39,94⟩ .empty))))
def t431_463 : Tree := .node t431_447 ⟨4,true,32,78⟩ t448_463
def t398_463 : Tree := .node t398_430 ⟨4,true,18,85⟩ t431_463
def t464_480 : Tree := (.node (.node (.node (.node (.node .empty ⟨4,true,39,111⟩ .empty) ⟨4,true,42,36⟩ .empty) ⟨4,true,42,40⟩ (.node .empty ⟨4,true,42,82⟩ .empty)) ⟨4,true,42,96⟩ (.node (.node .empty ⟨4,true,42,106⟩ .empty) ⟨5,false,6,1⟩ (.node .empty ⟨5,false,10,0⟩ .empty))) ⟨5,false,19,26⟩ (.node (.node (.node .empty ⟨5,false,33,51⟩ .empty) ⟨5,true,0,9⟩ (.node .empty ⟨5,true,0,22⟩ .empty)) ⟨5,true,0,47⟩ (.node (.node .empty ⟨5,true,1,3⟩ .empty) ⟨5,true,2,15⟩ (.node .empty ⟨5,true,3,24⟩ .empty))))
def t481_496 : Tree := (.node (.node (.node (.node .empty ⟨5,true,3,49⟩ .empty) ⟨5,true,3,60⟩ (.node .empty ⟨5,true,3,95⟩ .empty)) ⟨5,true,9,3⟩ (.node (.node .empty ⟨5,true,14,28⟩ .empty) ⟨5,true,16,38⟩ (.node .empty ⟨5,true,17,34⟩ .empty))) ⟨5,true,17,47⟩ (.node (.node (.node .empty ⟨5,true,17,49⟩ .empty) ⟨5,true,17,60⟩ (.node .empty ⟨5,true,17,62⟩ .empty)) ⟨5,true,17,80⟩ (.node (.node .empty ⟨5,true,17,95⟩ .empty) ⟨5,true,23,7⟩ (.node .empty ⟨5,true,24,9⟩ .empty))))
def t464_496 : Tree := .node t464_480 ⟨5,true,3,47⟩ t481_496
def t497_513 : Tree := (.node (.node (.node (.node (.node .empty ⟨5,true,30,38⟩ .empty) ⟨5,true,30,84⟩ .empty) ⟨5,true,30,99⟩ (.node .empty ⟨5,true,30,108⟩ .empty)) ⟨5,true,31,34⟩ (.node (.node .empty ⟨5,true,31,47⟩ .empty) ⟨5,true,31,49⟩ (.node .empty ⟨5,true,31,60⟩ .empty))) ⟨5,true,31,62⟩ (.node (.node (.node .empty ⟨5,true,31,80⟩ .empty) ⟨5,true,31,95⟩ (.node .empty ⟨5,true,37,10⟩ .empty)) ⟨5,true,37,33⟩ (.node (.node .empty ⟨5,true,37,39⟩ .empty) ⟨5,true,37,50⟩ (.node .empty ⟨5,true,37,68⟩ .empty))))
def t514_529 : Tree := (.node (.node (.node (.node .empty ⟨5,true,37,77⟩ .empty) ⟨5,true,37,78⟩ (.node .empty ⟨5,true,37,79⟩ .empty)) ⟨5,true,37,85⟩ (.node (.node .empty ⟨5,true,37,91⟩ .empty) ⟨5,true,37,97⟩ (.node .empty ⟨5,true,37,105⟩ .empty))) ⟨5,true,38,44⟩ (.node (.node (.node .empty ⟨5,true,38,49⟩ .empty) ⟨5,true,38,66⟩ (.node .empty ⟨5,true,38,67⟩ .empty)) ⟨5,true,38,87⟩ (.node (.node .empty ⟨5,true,38,95⟩ .empty) ⟨5,true,38,101⟩ (.node .empty ⟨5,true,42,53⟩ .empty))))
def t497_529 : Tree := .node t497_513 ⟨5,true,37,69⟩ t514_529
def t464_529 : Tree := .node t464_496 ⟨5,true,28,53⟩ t497_529
def t398_529 : Tree := .node t398_463 ⟨4,true,39,98⟩ t464_529
def t265_529 : Tree := .node t265_397 ⟨4,false,36,72⟩ t398_529
def t0_529 : Tree := .node t0_264 ⟨3,false,4,17⟩ t265_529
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 14, 0, 5, 0, 0, 6, 7, 0, 0, 8, 13, 0, 9, 10, 11, 0, 0, 12, 0, 0, 0, 0, 0, 15, 16, 0, 0, 17, 28, 0, 18, 19, 20, 0, 0, 21, 27, 0, 22, 23, 24, 0, 0, 0, 25, 26, 0, 0, 0, 0, 0, 29, 30, 0, 0, 31, 42, 0, 32, 33, 34, 0, 0, 35, 41, 0, 36, 37, 38, 0, 0, 0, 39, 40, 0, 0, 0, 0, 0, 43, 30, 0, 0],#[0, 1, 3, 2, 0, 0, 4, 0, 6, 5, 9, 8, 7, 0, 11, 13, 66, 65, 10, 0, 64, 30, 12, 0, 0, 0, 15, 14, 0, 0, 16, 26, 24, 17, 19, 18, 22, 21, 20, 0, 0, 0, 0, 0, 23, 0, 0, 0, 25, 0, 0, 0, 28, 27, 0, 0, 29, 0, 0, 16, 32, 31, 67, 65, 33, 51, 34, 36, 35, 0, 0, 0, 38, 37, 49, 42, 39, 51, 34, 40, 38, 41, 49, 42, 44, 43, 47, 46, 45, 0, 0, 103, 19, 59, 48, 0, 0, 0, 50, 0, 64, 72, 53, 52, 0, 0, 54, 0, 0, 55, 62, 56, 0, 57, 60, 58, 19, 59, 47, 46, 61, 0, 0, 0, 63, 0, 0, 0, 0, 0, 101, 86, 68, 0, 69, 0, 64, 70, 64, 71, 74, 73, 75, 73, 76, 73, 87, 86, 77, 51, 78, 51, 79, 51, 80, 82, 80, 36, 80, 40, 81, 0, 0, 0, 84, 83, 95, 94, 85, 51, 34, 36, 0, 0, 88, 0, 0, 89, 90, 73, 91, 0, 92, 96, 93, 0, 0, 0, 101, 100, 97, 0, 99, 98, 64, 71, 67, 65, 33, 51, 47, 58, 102, 0, 0, 103, 104, 73, 105, 0, 92, 106, 108, 107, 0, 0, 109, 51, 62, 110, 0, 111, 95, 94],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,3)],[(false,5)],[(true,5)],[(false,7)],[(true,8)],[(false,9)],[(true,9)],[(false,11)],[(true,7)],[(true,2)],[(false,14)],[(true,14)],[(false,16)],[(true,17)],[(false,18)],[(true,18)],[(false,20)],[(true,21)],[(false,22)],[(true,22)],[(true,24)],[(false,25)],[(true,20)],[(true,16)],[(false,28)],[(true,28),(true,42)],[(false,30)],[(true,31)],[(false,32)],[(true,32)],[(false,34)],[(true,35)],[(false,36)],[(true,36)],[(true,38)],[(false,39)],[(true,34)],[(true,30)],[(false,42)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(true,4)],[(false,4)],[(false,6)],[(true,5)],[(false,5)],[(false,9)],[(false,7)],[(false,11)],[(true,7)],[(true,13)],[(false,13)],[(false,15),(true,29)],[(true,16)],[(true,17)],[(false,17),(false,46),(false,58)],[(false,19)],[(true,18)],[(false,18)],[(false,22)],[(false,16)],[(false,24)],[(true,15)],[(true,26)],[(false,26)],[(false,28)],[(true,10)],[(true,30)],[(false,30)],[(false,32),(false,99)],[(false,33),(false,39),(false,85)],[(false,34)],[(true,33),(true,78),(true,85)],[(true,36)],[(false,36),(false,40)],[(false,38)],[(true,39),(true,79)],[(true,40)],[(true,37),(true,41)],[(true,42)],[(false,42)],[(false,44)],[(true,43),(true,59)],[(false,43),(false,59),(false,100)],[(false,47)],[(false,37),(false,41)],[(false,49)],[(true,32),(true,38),(true,74),(true,75),(true,76),(true,84),(true,99),(true,108)],[(true,51)],[(false,51)],[(false,53)],[(true,54)],[(true,55)],[(true,56)],[(true,57),(true,100)],[(true,46),(true,58)],[(false,57)],[(false,60)],[(false,55),(false,109)],[(false,62)],[(false,10),(false,50),(false,68),(false,69),(false,97)],[(true,8),(true,31),(true,98)],[(false,8)],[(false,31),(false,98)],[(false,66)],[(false,67)],[(true,68)],[(true,69),(true,97)],[(true,50)],[(true,70),(true,71),(true,72),(true,89),(true,103)],[(false,70)],[(false,71)],[(false,72)],[(false,74)],[(false,75)],[(false,76)],[(false,77),(false,78),(false,79)],[(false,80)],[(true,77)],[(true,82)],[(false,82)],[(false,84)],[(true,65),(true,73)],[(false,73)],[(false,87)],[(true,88)],[(false,89)],[(false,90)],[(false,91),(false,105)],[(false,92)],[(true,83),(true,111)],[(false,83),(false,111)],[(true,91)],[(false,95)],[(true,96)],[(false,96)],[(true,94)],[(false,65),(false,94)],[(false,101)],[(true,45),(true,102)],[(false,103)],[(false,104)],[(true,105)],[(true,106)],[(false,106)],[(false,108)],[(true,109)],[(true,110)]],
  t0_529⟩
theorem check0_16 : t0_16.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check17_33 : t17_33.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node16 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,16,50⟩ = true := by decide
theorem check0_33 : t0_33.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node16 check0_16 check17_33
theorem check34_50 : t34_50.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check51_66 : t51_66.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node50 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,2,56⟩ = true := by decide
theorem check34_66 : t34_66.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node50 check34_50 check51_66
theorem node33 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,36,80⟩ = true := by decide
theorem check0_66 : t0_66.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node33 check0_33 check34_66
theorem check67_83 : t67_83.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check84_99 : t84_99.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node83 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,28,100⟩ = true := by decide
theorem check67_99 : t67_99.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node83 check67_83 check84_99
theorem check100_116 : t100_116.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check117_132 : t117_132.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node116 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,42,100⟩ = true := by decide
theorem check100_132 : t100_132.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node116 check100_116 check117_132
theorem node99 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,35,103⟩ = true := by decide
theorem check67_132 : t67_132.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node99 check67_99 check100_132
theorem node66 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,16,46⟩ = true := by decide
theorem check0_132 : t0_132.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node66 check0_66 check67_132
theorem check133_149 : t133_149.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check150_165 : t150_165.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node149 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,38,39⟩ = true := by decide
theorem check133_165 : t133_165.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node149 check133_149 check150_165
theorem check166_182 : t166_182.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check183_198 : t183_198.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node182 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,27,30⟩ = true := by decide
theorem check166_198 : t166_198.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node182 check166_182 check183_198
theorem node165 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,42,80⟩ = true := by decide
theorem check133_198 : t133_198.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node165 check133_165 check166_198
theorem check199_215 : t199_215.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check216_231 : t216_231.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node215 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,16,43⟩ = true := by decide
theorem check199_231 : t199_231.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node215 check199_215 check216_231
theorem check232_248 : t232_248.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check249_264 : t249_264.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node248 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,39,75⟩ = true := by decide
theorem check232_264 : t232_264.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node248 check232_248 check249_264
theorem node231 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,30,59⟩ = true := by decide
theorem check199_264 : t199_264.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node231 check199_231 check232_264
theorem node198 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,41,89⟩ = true := by decide
theorem check133_264 : t133_264.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node198 check133_198 check199_264
theorem node132 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,14,60⟩ = true := by decide
theorem check0_264 : t0_264.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node132 check0_132 check133_264
theorem check265_281 : t265_281.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check282_298 : t282_298.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node281 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,30,51⟩ = true := by decide
theorem check265_298 : t265_298.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node281 check265_281 check282_298
theorem check299_315 : t299_315.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check316_331 : t316_331.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node315 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,40,98⟩ = true := by decide
theorem check299_331 : t299_331.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node315 check299_315 check316_331
theorem node298 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,39,94⟩ = true := by decide
theorem check265_331 : t265_331.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node298 check265_298 check299_331
theorem check332_348 : t332_348.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check349_364 : t349_364.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node348 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,17,46⟩ = true := by decide
theorem check332_364 : t332_364.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node348 check332_348 check349_364
theorem check365_381 : t365_381.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check382_397 : t382_397.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node381 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,38,43⟩ = true := by decide
theorem check365_397 : t365_397.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node381 check365_381 check382_397
theorem node364 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,31,42⟩ = true := by decide
theorem check332_397 : t332_397.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node364 check332_364 check365_397
theorem node331 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,1,2⟩ = true := by decide
theorem check265_397 : t265_397.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node331 check265_331 check332_397
theorem check398_414 : t398_414.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check415_430 : t415_430.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node414 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,5,111⟩ = true := by decide
theorem check398_430 : t398_430.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node414 check398_414 check415_430
theorem check431_447 : t431_447.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check448_463 : t448_463.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node447 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,32,78⟩ = true := by decide
theorem check431_463 : t431_463.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node447 check431_447 check448_463
theorem node430 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,18,85⟩ = true := by decide
theorem check398_463 : t398_463.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node430 check398_430 check431_463
theorem check464_480 : t464_480.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check481_496 : t481_496.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node480 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,3,47⟩ = true := by decide
theorem check464_496 : t464_496.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node480 check464_480 check481_496
theorem check497_513 : t497_513.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check514_529 : t514_529.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node513 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,37,69⟩ = true := by decide
theorem check497_529 : t497_529.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node513 check497_513 check514_529
theorem node496 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,28,53⟩ = true := by decide
theorem check464_529 : t464_529.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node496 check464_496 check497_529
theorem node463 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,39,98⟩ = true := by decide
theorem check398_529 : t398_529.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node463 check398_463 check464_529
theorem node397 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,36,72⟩ = true := by decide
theorem check265_529 : t265_529.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node397 check265_397 check398_529
theorem node264 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,4,17⟩ = true := by decide
theorem check0_529 : t0_529.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node264 check0_264 check265_529
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_529
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M023
