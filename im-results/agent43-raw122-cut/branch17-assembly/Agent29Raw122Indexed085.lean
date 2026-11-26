import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M085
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def t0_16 : Tree := (.node (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,6⟩ .empty) ⟨0,false,0,11⟩ (.node .empty ⟨0,false,0,14⟩ .empty)) ⟨0,false,0,31⟩ (.node (.node .empty ⟨0,false,7,0⟩ .empty) ⟨0,false,7,13⟩ (.node .empty ⟨0,false,7,23⟩ .empty))) ⟨0,false,7,29⟩ (.node (.node (.node .empty ⟨0,false,7,31⟩ .empty) ⟨0,false,7,33⟩ (.node .empty ⟨0,false,7,39⟩ .empty)) ⟨0,false,7,40⟩ (.node (.node .empty ⟨0,true,0,4⟩ .empty) ⟨0,true,0,9⟩ (.node .empty ⟨0,true,0,13⟩ .empty))))
def t17_32 : Tree := (.node (.node (.node (.node .empty ⟨0,true,0,19⟩ .empty) ⟨0,true,0,24⟩ (.node .empty ⟨0,true,0,29⟩ .empty)) ⟨0,true,1,12⟩ (.node (.node .empty ⟨0,true,1,14⟩ .empty) ⟨0,true,1,27⟩ (.node .empty ⟨0,true,1,31⟩ .empty))) ⟨0,true,1,40⟩ (.node (.node (.node .empty ⟨0,true,2,8⟩ .empty) ⟨0,true,2,10⟩ (.node .empty ⟨0,true,2,13⟩ .empty)) ⟨0,true,2,29⟩ (.node (.node .empty ⟨0,true,2,39⟩ .empty) ⟨0,true,4,12⟩ (.node .empty ⟨0,true,4,27⟩ .empty))))
def t0_32 : Tree := .node t0_16 ⟨0,true,0,15⟩ t17_32
def t33_48 : Tree := (.node (.node (.node (.node .empty ⟨0,true,5,8⟩ .empty) ⟨0,true,5,10⟩ (.node .empty ⟨0,true,5,34⟩ .empty)) ⟨0,true,8,0⟩ (.node (.node .empty ⟨0,true,8,12⟩ .empty) ⟨0,true,8,21⟩ (.node .empty ⟨0,true,8,26⟩ .empty))) ⟨0,true,8,27⟩ (.node (.node (.node .empty ⟨0,true,8,29⟩ .empty) ⟨0,true,8,33⟩ (.node .empty ⟨0,true,8,38⟩ .empty)) ⟨0,true,8,39⟩ (.node (.node .empty ⟨1,false,1,0⟩ .empty) ⟨1,false,1,4⟩ (.node .empty ⟨1,false,1,9⟩ .empty))))
def t49_64 : Tree := (.node (.node (.node (.node .empty ⟨1,false,1,15⟩ .empty) ⟨1,false,1,19⟩ (.node .empty ⟨1,false,1,24⟩ .empty)) ⟨1,false,1,29⟩ (.node (.node .empty ⟨1,false,4,1⟩ .empty) ⟨1,false,4,9⟩ (.node .empty ⟨1,false,4,16⟩ .empty))) ⟨1,false,4,24⟩ (.node (.node (.node .empty ⟨1,false,4,32⟩ .empty) ⟨1,false,4,37⟩ (.node .empty ⟨1,false,6,0⟩ .empty)) ⟨1,false,6,12⟩ (.node (.node .empty ⟨1,false,6,27⟩ .empty) ⟨1,false,6,38⟩ (.node .empty ⟨1,false,10,0⟩ .empty))))
def t33_64 : Tree := .node t33_48 ⟨1,false,1,13⟩ t49_64
def t0_64 : Tree := .node t0_32 ⟨0,true,4,38⟩ t33_64
def t65_80 : Tree := (.node (.node (.node (.node .empty ⟨1,false,10,21⟩ .empty) ⟨1,false,10,26⟩ (.node .empty ⟨1,false,10,27⟩ .empty)) ⟨1,false,10,29⟩ (.node (.node .empty ⟨1,false,10,33⟩ .empty) ⟨1,false,10,38⟩ (.node .empty ⟨1,false,10,39⟩ .empty))) ⟨1,true,4,7⟩ (.node (.node (.node .empty ⟨1,true,4,9⟩ .empty) ⟨1,true,4,24⟩ (.node .empty ⟨1,true,6,7⟩ .empty)) ⟨1,true,6,9⟩ (.node (.node .empty ⟨1,true,6,24⟩ .empty) ⟨1,true,6,25⟩ (.node .empty ⟨1,true,6,37⟩ .empty))))
def t81_96 : Tree := (.node (.node (.node (.node .empty ⟨2,false,2,12⟩ .empty) ⟨2,false,2,14⟩ (.node .empty ⟨2,false,2,27⟩ .empty)) ⟨2,false,2,31⟩ (.node (.node .empty ⟨2,false,2,40⟩ .empty) ⟨2,false,7,0⟩ (.node .empty ⟨2,false,7,2⟩ .empty))) ⟨2,false,7,3⟩ (.node (.node (.node .empty ⟨2,false,7,5⟩ .empty) ⟨2,false,7,8⟩ (.node .empty ⟨2,false,7,10⟩ .empty)) ⟨2,false,7,11⟩ (.node (.node .empty ⟨2,false,7,26⟩ .empty) ⟨2,false,7,27⟩ (.node .empty ⟨2,false,7,30⟩ .empty))))
def t65_96 : Tree := .node t65_80 ⟨2,false,2,0⟩ t81_96
def t97_112 : Tree := (.node (.node (.node (.node .empty ⟨2,false,7,35⟩ .empty) ⟨2,false,7,38⟩ (.node .empty ⟨2,false,7,41⟩ .empty)) ⟨2,true,2,3⟩ (.node (.node .empty ⟨2,true,2,8⟩ .empty) ⟨2,true,2,10⟩ (.node .empty ⟨2,true,2,11⟩ .empty))) ⟨2,true,2,18⟩ (.node (.node (.node .empty ⟨2,true,2,41⟩ .empty) ⟨2,true,5,0⟩ (.node .empty ⟨2,true,5,8⟩ .empty)) ⟨2,true,5,10⟩ (.node (.node .empty ⟨2,true,5,13⟩ .empty) ⟨2,true,5,29⟩ (.node .empty ⟨2,true,5,34⟩ .empty))))
def t113_128 : Tree := (.node (.node (.node (.node .empty ⟨3,false,2,1⟩ .empty) ⟨3,false,2,9⟩ (.node .empty ⟨3,false,2,16⟩ .empty)) ⟨3,false,2,24⟩ (.node (.node .empty ⟨3,false,2,32⟩ .empty) ⟨3,false,3,0⟩ (.node .empty ⟨3,false,3,8⟩ .empty))) ⟨3,false,3,10⟩ (.node (.node (.node .empty ⟨3,false,3,13⟩ .empty) ⟨3,false,3,29⟩ (.node .empty ⟨3,false,3,39⟩ .empty)) ⟨3,false,7,1⟩ (.node (.node .empty ⟨3,false,7,2⟩ .empty) ⟨3,false,7,10⟩ (.node .empty ⟨3,false,7,24⟩ .empty))))
def t97_128 : Tree := .node t97_112 ⟨2,true,5,39⟩ t113_128
def t65_128 : Tree := .node t65_96 ⟨2,false,7,34⟩ t97_128
def t0_128 : Tree := .node t0_64 ⟨1,false,10,12⟩ t65_128
def t129_145 : Tree := (.node (.node (.node (.node (.node .empty ⟨3,false,7,34⟩ .empty) ⟨3,false,7,37⟩ .empty) ⟨3,false,8,0⟩ (.node .empty ⟨3,false,8,1⟩ .empty)) ⟨3,false,8,2⟩ (.node (.node .empty ⟨3,false,8,9⟩ .empty) ⟨3,false,8,10⟩ (.node .empty ⟨3,false,8,24⟩ .empty))) ⟨3,false,8,25⟩ (.node (.node (.node .empty ⟨3,false,8,34⟩ .empty) ⟨3,false,8,37⟩ (.node .empty ⟨3,true,1,2⟩ .empty)) ⟨3,true,1,10⟩ (.node (.node .empty ⟨3,true,1,17⟩ .empty) ⟨3,true,6,2⟩ (.node .empty ⟨3,true,6,10⟩ .empty))))
def t146_161 : Tree := (.node (.node (.node (.node .empty ⟨3,true,6,25⟩ .empty) ⟨3,true,6,34⟩ (.node .empty ⟨3,true,6,37⟩ .empty)) ⟨3,true,8,1⟩ (.node (.node .empty ⟨3,true,8,4⟩ .empty) ⟨3,true,8,7⟩ (.node .empty ⟨3,true,8,9⟩ .empty))) ⟨3,true,8,24⟩ (.node (.node (.node .empty ⟨3,true,8,25⟩ .empty) ⟨3,true,8,28⟩ (.node .empty ⟨3,true,8,36⟩ .empty)) ⟨3,true,8,37⟩ (.node (.node .empty ⟨3,true,10,2⟩ .empty) ⟨3,true,10,10⟩ (.node .empty ⟨3,true,10,24⟩ .empty))))
def t129_161 : Tree := .node t129_145 ⟨3,true,6,24⟩ t146_161
def t162_177 : Tree := (.node (.node (.node (.node .empty ⟨3,true,10,34⟩ .empty) ⟨3,true,10,37⟩ (.node .empty ⟨4,true,2,1⟩ .empty)) ⟨4,true,2,9⟩ (.node (.node .empty ⟨4,true,2,16⟩ .empty) ⟨4,true,2,24⟩ (.node .empty ⟨4,true,2,32⟩ .empty))) ⟨4,true,7,1⟩ (.node (.node (.node .empty ⟨4,true,7,2⟩ .empty) ⟨4,true,7,9⟩ (.node .empty ⟨4,true,7,10⟩ .empty)) ⟨4,true,7,24⟩ (.node (.node .empty ⟨4,true,7,25⟩ .empty) ⟨4,true,7,34⟩ (.node .empty ⟨4,true,7,37⟩ .empty))))
def t178_193 : Tree := (.node (.node (.node (.node .empty ⟨4,true,9,2⟩ .empty) ⟨4,true,9,3⟩ (.node .empty ⟨4,true,9,5⟩ .empty)) ⟨4,true,9,8⟩ (.node (.node .empty ⟨4,true,9,10⟩ .empty) ⟨4,true,9,11⟩ (.node .empty ⟨4,true,9,26⟩ .empty))) ⟨4,true,9,27⟩ (.node (.node (.node .empty ⟨4,true,9,30⟩ .empty) ⟨4,true,9,34⟩ (.node .empty ⟨4,true,9,35⟩ .empty)) ⟨4,true,9,38⟩ (.node (.node .empty ⟨4,true,9,41⟩ .empty) ⟨5,false,0,5⟩ (.node .empty ⟨5,false,0,10⟩ .empty))))
def t162_193 : Tree := .node t162_177 ⟨4,true,9,0⟩ t178_193
def t129_193 : Tree := .node t129_161 ⟨3,true,10,25⟩ t162_193
def t194_209 : Tree := (.node (.node (.node (.node .empty ⟨5,false,7,1⟩ .empty) ⟨5,false,7,22⟩ (.node .empty ⟨5,false,7,28⟩ .empty)) ⟨5,false,7,32⟩ (.node (.node .empty ⟨5,true,0,4⟩ .empty) ⟨5,true,0,9⟩ (.node .empty ⟨5,true,0,19⟩ .empty))) ⟨5,true,0,24⟩ (.node (.node (.node .empty ⟨5,true,1,3⟩ .empty) ⟨5,true,1,8⟩ (.node .empty ⟨5,true,1,10⟩ .empty)) ⟨5,true,1,11⟩ (.node (.node .empty ⟨5,true,1,18⟩ .empty) ⟨5,true,2,7⟩ (.node .empty ⟨5,true,2,9⟩ .empty))))
def t210_225 : Tree := (.node (.node (.node (.node .empty ⟨5,true,4,5⟩ .empty) ⟨5,true,4,8⟩ (.node .empty ⟨5,true,4,10⟩ .empty)) ⟨5,true,4,30⟩ (.node (.node .empty ⟨5,true,5,4⟩ .empty) ⟨5,true,5,7⟩ (.node .empty ⟨5,true,5,9⟩ .empty))) ⟨5,true,5,24⟩ (.node (.node (.node .empty ⟨5,true,5,28⟩ .empty) ⟨5,true,5,36⟩ (.node .empty ⟨5,true,6,3⟩ .empty)) ⟨5,true,6,5⟩ (.node (.node .empty ⟨5,true,6,8⟩ .empty) ⟨5,true,6,10⟩ (.node .empty ⟨5,true,6,11⟩ .empty))))
def t194_225 : Tree := .node t194_209 ⟨5,true,2,24⟩ t210_225
def t226_241 : Tree := (.node (.node (.node (.node .empty ⟨5,true,6,27⟩ .empty) ⟨5,true,6,30⟩ (.node .empty ⟨5,true,6,35⟩ .empty)) ⟨5,true,6,38⟩ (.node (.node .empty ⟨5,true,6,41⟩ .empty) ⟨5,true,7,4⟩ (.node .empty ⟨5,true,7,7⟩ .empty))) ⟨5,true,7,9⟩ (.node (.node (.node .empty ⟨5,true,7,24⟩ .empty) ⟨5,true,7,28⟩ (.node .empty ⟨5,true,7,36⟩ .empty)) ⟨5,true,8,0⟩ (.node (.node .empty ⟨5,true,8,12⟩ .empty) ⟨5,true,8,21⟩ (.node .empty ⟨5,true,8,26⟩ .empty))))
def t242_257 : Tree := (.node (.node (.node (.node .empty ⟨5,true,8,29⟩ .empty) ⟨5,true,8,33⟩ (.node .empty ⟨5,true,8,38⟩ .empty)) ⟨5,true,8,39⟩ (.node (.node .empty ⟨5,true,10,3⟩ .empty) ⟨5,true,10,5⟩ (.node .empty ⟨5,true,10,8⟩ .empty))) ⟨5,true,10,10⟩ (.node (.node (.node .empty ⟨5,true,10,11⟩ .empty) ⟨5,true,10,26⟩ (.node .empty ⟨5,true,10,27⟩ .empty)) ⟨5,true,10,30⟩ (.node (.node .empty ⟨5,true,10,35⟩ .empty) ⟨5,true,10,38⟩ (.node .empty ⟨5,true,10,41⟩ .empty))))
def t226_257 : Tree := .node t226_241 ⟨5,true,8,27⟩ t242_257
def t194_257 : Tree := .node t194_225 ⟨5,true,6,26⟩ t226_257
def t129_257 : Tree := .node t129_193 ⟨5,false,0,20⟩ t194_257
def t0_257 : Tree := .node t0_128 ⟨3,false,7,25⟩ t129_257
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 4, 0, 0, 0, 5, 0, 6, 0, 7, 8, 10, 0, 9, 0, 0, 0, 7],#[0, 1, 3, 2, 26, 25, 21, 4, 6, 5, 21, 7, 0, 0, 0, 8, 12, 9, 11, 10, 27, 24, 21, 4, 13, 22, 14, 16, 15, 0, 6, 0, 18, 17, 0, 0, 0, 19, 6, 20, 0, 0, 23, 22, 0, 0, 0, 0, 11, 10, 35, 34, 33, 28, 29, 28, 0, 30, 31, 32, 21, 7, 15, 0, 18, 17, 23, 22, 38, 37, 21, 36, 0, 30, 41, 34, 39, 28, 40, 32, 15, 0, 21, 4],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(true,2)],[(true,4)],[(true,5)],[(true,6),(true,10)],[(false,7)],[(true,8)],[(true,7)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3),(true,11),(true,41)],[(true,4)],[(false,4),(false,15),(false,19)],[(true,5),(true,30)],[(true,7)],[(true,8)],[(true,9),(true,24)],[(false,9),(false,24)],[(false,8)],[(false,12)],[(false,13)],[(false,14),(false,31),(false,40)],[(true,13)],[(true,16),(true,32)],[(false,16),(false,32)],[(true,18)],[(true,19)],[(false,3),(false,5),(false,11),(false,30),(false,35),(false,41)],[(true,12),(true,21),(true,33)],[(false,21),(false,33)],[(true,10)],[(true,2)],[(false,2)],[(false,10)],[(true,26),(true,27),(true,38)],[(false,27)],[(true,28),(true,36)],[(false,29)],[(true,29),(true,39)],[(false,26)],[(true,25),(true,37)],[(false,25)],[(true,35)],[(true,34)],[(false,34)],[(false,38)],[(false,39)],[(false,37)]],
  t0_257⟩
theorem check0_16 : t0_16.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check17_32 : t17_32.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node16 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,0,15⟩ = true := by decide
theorem check0_32 : t0_32.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node16 check0_16 check17_32
theorem check33_48 : t33_48.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check49_64 : t49_64.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node48 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,1,13⟩ = true := by decide
theorem check33_64 : t33_64.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node48 check33_48 check49_64
theorem node32 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,4,38⟩ = true := by decide
theorem check0_64 : t0_64.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node32 check0_32 check33_64
theorem check65_80 : t65_80.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check81_96 : t81_96.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node80 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,2,0⟩ = true := by decide
theorem check65_96 : t65_96.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node80 check65_80 check81_96
theorem check97_112 : t97_112.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check113_128 : t113_128.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node112 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,5,39⟩ = true := by decide
theorem check97_128 : t97_128.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node112 check97_112 check113_128
theorem node96 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,7,34⟩ = true := by decide
theorem check65_128 : t65_128.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node96 check65_96 check97_128
theorem node64 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,10,12⟩ = true := by decide
theorem check0_128 : t0_128.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node64 check0_64 check65_128
theorem check129_145 : t129_145.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check146_161 : t146_161.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node145 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,6,24⟩ = true := by decide
theorem check129_161 : t129_161.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node145 check129_145 check146_161
theorem check162_177 : t162_177.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check178_193 : t178_193.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node177 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,9,0⟩ = true := by decide
theorem check162_193 : t162_193.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node177 check162_177 check178_193
theorem node161 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,10,25⟩ = true := by decide
theorem check129_193 : t129_193.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node161 check129_161 check162_193
theorem check194_209 : t194_209.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check210_225 : t210_225.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node209 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,2,24⟩ = true := by decide
theorem check194_225 : t194_225.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node209 check194_209 check210_225
theorem check226_241 : t226_241.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check242_257 : t242_257.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node241 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,8,27⟩ = true := by decide
theorem check226_257 : t226_257.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node241 check226_241 check242_257
theorem node225 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,6,26⟩ = true := by decide
theorem check194_257 : t194_257.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node225 check194_225 check226_257
theorem node193 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,0,20⟩ = true := by decide
theorem check129_257 : t129_257.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node193 check129_193 check194_257
theorem node128 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,7,25⟩ = true := by decide
theorem check0_257 : t0_257.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node128 check0_128 check129_257
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_257
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M085
