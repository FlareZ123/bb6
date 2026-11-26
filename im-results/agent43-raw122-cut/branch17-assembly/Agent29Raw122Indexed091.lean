import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M091
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def t0_11 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,3⟩ .empty) ⟨0,false,0,11⟩ (.node (.node .empty ⟨0,false,0,16⟩ .empty) ⟨0,false,2,0⟩ .empty)) ⟨0,false,2,11⟩ (.node (.node (.node .empty ⟨0,false,2,13⟩ .empty) ⟨0,false,7,0⟩ .empty) ⟨0,false,7,11⟩ (.node (.node .empty ⟨0,false,7,13⟩ .empty) ⟨1,false,0,6⟩ .empty)))
def t12_23 : Tree := (.node (.node (.node (.node .empty ⟨1,false,1,1⟩ .empty) ⟨1,false,1,4⟩ .empty) ⟨1,false,1,8⟩ (.node (.node .empty ⟨1,false,1,9⟩ .empty) ⟨1,false,6,0⟩ .empty)) ⟨1,false,6,6⟩ (.node (.node (.node .empty ⟨1,false,6,9⟩ .empty) ⟨1,false,6,11⟩ .empty) ⟨1,true,0,3⟩ (.node (.node .empty ⟨1,true,0,16⟩ .empty) ⟨1,true,1,1⟩ .empty)))
def t0_23 : Tree := .node t0_11 ⟨1,false,1,0⟩ t12_23
def t24_35 : Tree := (.node (.node (.node (.node .empty ⟨1,true,1,8⟩ .empty) ⟨2,false,1,3⟩ .empty) ⟨2,false,1,16⟩ (.node (.node .empty ⟨2,false,1,18⟩ .empty) ⟨2,false,2,0⟩ .empty)) ⟨2,false,2,2⟩ (.node (.node (.node .empty ⟨2,false,2,5⟩ .empty) ⟨2,false,2,14⟩ .empty) ⟨2,false,2,15⟩ (.node (.node .empty ⟨2,false,2,17⟩ .empty) ⟨2,false,7,0⟩ .empty)))
def t36_47 : Tree := (.node (.node (.node (.node .empty ⟨2,false,7,3⟩ .empty) ⟨2,false,7,5⟩ .empty) ⟨2,false,7,9⟩ (.node (.node .empty ⟨2,false,7,14⟩ .empty) ⟨2,false,7,15⟩ .empty)) ⟨2,false,7,16⟩ (.node (.node (.node .empty ⟨2,false,7,17⟩ .empty) ⟨2,false,7,18⟩ .empty) ⟨2,true,2,0⟩ (.node (.node .empty ⟨2,true,2,3⟩ .empty) ⟨2,true,2,5⟩ .empty)))
def t24_47 : Tree := .node t24_35 ⟨2,false,7,2⟩ t36_47
def t0_47 : Tree := .node t0_23 ⟨1,true,1,4⟩ t24_47
def t48_59 : Tree := (.node (.node (.node (.node .empty ⟨2,true,2,15⟩ .empty) ⟨3,false,1,2⟩ .empty) ⟨3,false,1,5⟩ (.node (.node .empty ⟨3,false,1,15⟩ .empty) ⟨3,false,1,17⟩ .empty)) ⟨3,false,2,1⟩ (.node (.node (.node .empty ⟨3,false,3,0⟩ .empty) ⟨3,false,4,1⟩ .empty) ⟨3,false,4,4⟩ (.node (.node .empty ⟨3,false,4,7⟩ .empty) ⟨3,false,4,8⟩ .empty)))
def t60_71 : Tree := (.node (.node (.node (.node .empty ⟨3,false,7,2⟩ .empty) ⟨3,false,7,5⟩ .empty) ⟨3,false,7,7⟩ (.node (.node .empty ⟨3,false,7,8⟩ .empty) ⟨3,false,7,15⟩ .empty)) ⟨3,false,7,17⟩ (.node (.node (.node .empty ⟨3,false,8,0⟩ .empty) ⟨3,false,8,1⟩ .empty) ⟨3,false,8,2⟩ (.node (.node .empty ⟨3,false,8,4⟩ .empty) ⟨3,false,8,5⟩ .empty)))
def t48_71 : Tree := .node t48_59 ⟨3,false,7,1⟩ t60_71
def t72_83 : Tree := (.node (.node (.node (.node .empty ⟨3,false,8,8⟩ .empty) ⟨3,false,8,14⟩ .empty) ⟨3,false,8,15⟩ (.node (.node .empty ⟨3,false,8,17⟩ .empty) ⟨3,true,0,7⟩ .empty)) ⟨3,true,0,8⟩ (.node (.node (.node .empty ⟨3,true,1,2⟩ .empty) ⟨3,true,3,1⟩ .empty) ⟨3,true,3,4⟩ (.node (.node .empty ⟨3,true,3,7⟩ .empty) ⟨3,true,3,8⟩ .empty)))
def t84_95 : Tree := (.node (.node (.node (.node .empty ⟨3,true,3,19⟩ .empty) ⟨3,true,6,2⟩ .empty) ⟨3,true,6,7⟩ (.node (.node .empty ⟨3,true,6,8⟩ .empty) ⟨3,true,6,15⟩ .empty)) ⟨3,true,6,17⟩ (.node (.node (.node .empty ⟨3,true,8,1⟩ .empty) ⟨3,true,8,4⟩ .empty) ⟨3,true,8,7⟩ (.node (.node .empty ⟨3,true,8,8⟩ .empty) ⟨3,true,8,10⟩ .empty)))
def t72_95 : Tree := .node t72_83 ⟨3,true,3,10⟩ t84_95
def t48_95 : Tree := .node t48_71 ⟨3,false,8,7⟩ t72_95
def t0_95 : Tree := .node t0_47 ⟨2,true,2,14⟩ t48_95
def t96_107 : Tree := (.node (.node (.node (.node .empty ⟨4,false,0,1⟩ .empty) ⟨4,false,0,4⟩ .empty) ⟨4,false,0,8⟩ (.node (.node .empty ⟨4,false,0,9⟩ .empty) ⟨4,false,3,0⟩ .empty)) ⟨4,false,3,6⟩ (.node (.node (.node .empty ⟨4,false,3,9⟩ .empty) ⟨4,false,3,11⟩ .empty) ⟨4,false,8,0⟩ (.node (.node .empty ⟨4,false,8,6⟩ .empty) ⟨4,false,8,9⟩ .empty)))
def t108_119 : Tree := (.node (.node (.node (.node .empty ⟨4,true,0,4⟩ .empty) ⟨4,true,0,8⟩ .empty) ⟨4,true,0,9⟩ (.node (.node .empty ⟨4,true,1,2⟩ .empty) ⟨4,true,1,5⟩ .empty)) ⟨4,true,1,14⟩ (.node (.node (.node .empty ⟨4,true,1,15⟩ .empty) ⟨4,true,1,17⟩ .empty) ⟨4,true,2,1⟩ (.node (.node .empty ⟨4,true,3,0⟩ .empty) ⟨4,true,3,6⟩ .empty)))
def t96_119 : Tree := .node t96_107 ⟨4,false,8,11⟩ t108_119
def t120_131 : Tree := (.node (.node (.node (.node .empty ⟨4,true,3,11⟩ .empty) ⟨4,true,5,0⟩ .empty) ⟨4,true,5,2⟩ (.node (.node .empty ⟨4,true,5,3⟩ .empty) ⟨4,true,5,5⟩ .empty)) ⟨4,true,5,9⟩ (.node (.node (.node .empty ⟨4,true,5,14⟩ .empty) ⟨4,true,5,15⟩ .empty) ⟨4,true,5,16⟩ (.node (.node .empty ⟨4,true,5,17⟩ .empty) ⟨4,true,5,18⟩ .empty)))
def t132_143 : Tree := (.node (.node (.node (.node .empty ⟨4,true,7,2⟩ .empty) ⟨4,true,7,5⟩ .empty) ⟨4,true,7,7⟩ (.node (.node .empty ⟨4,true,7,8⟩ .empty) ⟨4,true,7,14⟩ .empty)) ⟨4,true,7,15⟩ (.node (.node (.node .empty ⟨4,true,7,17⟩ .empty) ⟨4,true,8,0⟩ .empty) ⟨4,true,8,6⟩ (.node (.node .empty ⟨4,true,8,9⟩ .empty) ⟨4,true,8,11⟩ .empty)))
def t120_143 : Tree := .node t120_131 ⟨4,true,7,1⟩ t132_143
def t96_143 : Tree := .node t96_119 ⟨4,true,3,9⟩ t120_143
def t144_155 : Tree := (.node (.node (.node (.node .empty ⟨5,false,0,5⟩ .empty) ⟨5,false,0,10⟩ .empty) ⟨5,false,0,11⟩ (.node (.node .empty ⟨5,false,0,15⟩ .empty) ⟨5,false,0,16⟩ .empty)) ⟨5,false,2,0⟩ (.node (.node (.node .empty ⟨5,false,2,1⟩ .empty) ⟨5,false,2,10⟩ .empty) ⟨5,false,2,11⟩ (.node (.node .empty ⟨5,false,2,12⟩ .empty) ⟨5,false,2,13⟩ .empty)))
def t156_167 : Tree := (.node (.node (.node (.node .empty ⟨5,false,7,1⟩ .empty) ⟨5,false,7,10⟩ .empty) ⟨5,false,7,11⟩ (.node (.node .empty ⟨5,false,7,12⟩ .empty) ⟨5,false,7,13⟩ .empty)) ⟨5,true,0,4⟩ (.node (.node (.node .empty ⟨5,true,0,8⟩ .empty) ⟨5,true,0,9⟩ .empty) ⟨5,true,1,3⟩ (.node (.node .empty ⟨5,true,1,5⟩ .empty) ⟨5,true,1,14⟩ .empty)))
def t144_167 : Tree := .node t144_155 ⟨5,false,7,0⟩ t156_167
def t168_179 : Tree := (.node (.node (.node (.node .empty ⟨5,true,2,4⟩ .empty) ⟨5,true,2,8⟩ .empty) ⟨5,true,2,10⟩ (.node (.node .empty ⟨5,true,2,19⟩ .empty) ⟨5,true,3,0⟩ .empty)) ⟨5,true,3,6⟩ (.node (.node (.node .empty ⟨5,true,3,9⟩ .empty) ⟨5,true,3,11⟩ .empty) ⟨5,true,6,3⟩ (.node (.node .empty ⟨5,true,6,5⟩ .empty) ⟨5,true,6,9⟩ .empty)))
def t180_191 : Tree := (.node (.node (.node (.node .empty ⟨5,true,6,15⟩ .empty) ⟨5,true,6,16⟩ .empty) ⟨5,true,6,18⟩ (.node (.node .empty ⟨5,true,7,4⟩ .empty) ⟨5,true,7,8⟩ .empty)) ⟨5,true,7,10⟩ (.node (.node (.node .empty ⟨5,true,7,19⟩ .empty) ⟨5,true,8,0⟩ .empty) ⟨5,true,8,6⟩ (.node (.node .empty ⟨5,true,8,9⟩ .empty) ⟨5,true,8,11⟩ .empty)))
def t168_191 : Tree := .node t168_179 ⟨5,true,6,14⟩ t180_191
def t144_191 : Tree := .node t144_167 ⟨5,true,1,15⟩ t168_191
def t96_191 : Tree := .node t96_143 ⟨5,false,0,3⟩ t144_191
def t0_191 : Tree := .node t0_95 ⟨3,true,8,19⟩ t96_191
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 6, 0, 5, 0, 0, 0, 0, 0, 7, 8, 6, 0, 5],#[0, 1, 3, 2, 9, 7, 6, 4, 3, 5, 9, 8, 13, 12, 18, 17, 16, 15, 11, 10, 0, 14, 13, 12, 0, 0, 0, 0, 9, 8, 9, 8, 6, 19, 9, 7, 6, 19, 0, 14],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,3),(true,8)],[(true,2),(true,7)],[(true,6)],[(false,7)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1),(false,4)],[(true,3)],[(true,4)],[(false,3),(false,16),(false,18)],[(true,2),(true,17)],[(true,5),(true,14),(true,15)],[(false,2),(false,5),(false,14),(false,15),(false,17)],[(true,9)],[(false,9)],[(true,6),(true,11)],[(false,6),(false,11)],[(true,10),(true,19)],[(true,8)],[(false,8)],[(true,7)],[(false,7)],[(true,16),(true,18)]],
  t0_191⟩
theorem check0_11 : t0_11.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check12_23 : t12_23.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node11 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,1,0⟩ = true := by decide
theorem check0_23 : t0_23.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node11 check0_11 check12_23
theorem check24_35 : t24_35.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check36_47 : t36_47.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node35 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,7,2⟩ = true := by decide
theorem check24_47 : t24_47.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node35 check24_35 check36_47
theorem node23 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,1,4⟩ = true := by decide
theorem check0_47 : t0_47.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node23 check0_23 check24_47
theorem check48_59 : t48_59.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check60_71 : t60_71.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node59 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,7,1⟩ = true := by decide
theorem check48_71 : t48_71.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node59 check48_59 check60_71
theorem check72_83 : t72_83.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check84_95 : t84_95.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node83 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,3,10⟩ = true := by decide
theorem check72_95 : t72_95.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node83 check72_83 check84_95
theorem node71 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,8,7⟩ = true := by decide
theorem check48_95 : t48_95.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node71 check48_71 check72_95
theorem node47 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,2,14⟩ = true := by decide
theorem check0_95 : t0_95.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node47 check0_47 check48_95
theorem check96_107 : t96_107.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check108_119 : t108_119.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node107 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,8,11⟩ = true := by decide
theorem check96_119 : t96_119.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node107 check96_107 check108_119
theorem check120_131 : t120_131.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check132_143 : t132_143.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node131 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,7,1⟩ = true := by decide
theorem check120_143 : t120_143.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node131 check120_131 check132_143
theorem node119 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,3,9⟩ = true := by decide
theorem check96_143 : t96_143.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node119 check96_119 check120_143
theorem check144_155 : t144_155.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check156_167 : t156_167.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node155 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,7,0⟩ = true := by decide
theorem check144_167 : t144_167.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node155 check144_155 check156_167
theorem check168_179 : t168_179.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check180_191 : t180_191.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node179 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,6,14⟩ = true := by decide
theorem check168_191 : t168_191.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node179 check168_179 check180_191
theorem node167 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,1,15⟩ = true := by decide
theorem check144_191 : t144_191.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node167 check144_167 check168_191
theorem node143 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,0,3⟩ = true := by decide
theorem check96_191 : t96_191.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node143 check96_143 check144_191
theorem node95 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,8,19⟩ = true := by decide
theorem check0_191 : t0_191.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node95 check0_95 check96_191
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_191
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M091
