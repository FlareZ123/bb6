import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M089
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def t0_10 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,3⟩ .empty) ⟨0,false,0,11⟩ (.node (.node .empty ⟨0,false,0,16⟩ .empty) ⟨0,false,2,0⟩ .empty)) ⟨0,false,2,11⟩ (.node (.node (.node .empty ⟨0,false,2,13⟩ .empty) ⟨0,false,7,0⟩ .empty) ⟨0,false,7,11⟩ (.node .empty ⟨0,false,7,13⟩ .empty)))
def t11_21 : Tree := (.node (.node (.node (.node .empty ⟨0,true,0,16⟩ .empty) ⟨1,false,0,6⟩ .empty) ⟨1,false,1,0⟩ (.node (.node .empty ⟨1,false,1,1⟩ .empty) ⟨1,false,1,4⟩ .empty)) ⟨1,false,1,8⟩ (.node (.node (.node .empty ⟨1,false,1,9⟩ .empty) ⟨1,false,6,0⟩ .empty) ⟨1,false,6,6⟩ (.node .empty ⟨1,false,6,9⟩ .empty)))
def t0_21 : Tree := .node t0_10 ⟨0,true,0,3⟩ t11_21
def t22_32 : Tree := (.node (.node (.node (.node .empty ⟨1,true,0,4⟩ .empty) ⟨1,true,0,8⟩ .empty) ⟨1,true,0,9⟩ (.node (.node .empty ⟨1,true,1,1⟩ .empty) ⟨1,true,1,4⟩ .empty)) ⟨1,true,1,8⟩ (.node (.node (.node .empty ⟨1,true,3,0⟩ .empty) ⟨1,true,3,6⟩ .empty) ⟨1,true,3,9⟩ (.node .empty ⟨1,true,3,11⟩ .empty)))
def t33_42 : Tree := (.node (.node (.node (.node .empty ⟨1,true,8,6⟩ .empty) ⟨1,true,8,9⟩ .empty) ⟨1,true,8,11⟩ (.node .empty ⟨2,false,1,3⟩ .empty)) ⟨2,false,1,16⟩ (.node (.node (.node .empty ⟨2,false,1,18⟩ .empty) ⟨2,false,2,0⟩ .empty) ⟨2,false,2,2⟩ (.node .empty ⟨2,false,2,5⟩ .empty)))
def t22_42 : Tree := .node t22_32 ⟨1,true,8,0⟩ t33_42
def t0_42 : Tree := .node t0_21 ⟨1,false,6,11⟩ t22_42
def t43_53 : Tree := (.node (.node (.node (.node .empty ⟨2,false,2,15⟩ .empty) ⟨2,false,2,17⟩ .empty) ⟨2,false,7,0⟩ (.node (.node .empty ⟨2,false,7,2⟩ .empty) ⟨2,false,7,3⟩ .empty)) ⟨2,false,7,5⟩ (.node (.node (.node .empty ⟨2,false,7,9⟩ .empty) ⟨2,false,7,14⟩ .empty) ⟨2,false,7,15⟩ (.node .empty ⟨2,false,7,16⟩ .empty)))
def t54_64 : Tree := (.node (.node (.node (.node .empty ⟨2,false,7,18⟩ .empty) ⟨2,true,2,0⟩ .empty) ⟨2,true,2,3⟩ (.node (.node .empty ⟨2,true,2,5⟩ .empty) ⟨2,true,2,14⟩ .empty)) ⟨2,true,2,15⟩ (.node (.node (.node .empty ⟨3,false,1,2⟩ .empty) ⟨3,false,1,5⟩ .empty) ⟨3,false,1,15⟩ (.node .empty ⟨3,false,1,17⟩ .empty)))
def t43_64 : Tree := .node t43_53 ⟨2,false,7,17⟩ t54_64
def t65_75 : Tree := (.node (.node (.node (.node .empty ⟨3,false,3,0⟩ .empty) ⟨3,false,4,1⟩ .empty) ⟨3,false,4,4⟩ (.node (.node .empty ⟨3,false,4,7⟩ .empty) ⟨3,false,4,8⟩ .empty)) ⟨3,false,7,1⟩ (.node (.node (.node .empty ⟨3,false,7,2⟩ .empty) ⟨3,false,7,5⟩ .empty) ⟨3,false,7,7⟩ (.node .empty ⟨3,false,7,8⟩ .empty)))
def t76_85 : Tree := (.node (.node (.node (.node .empty ⟨3,false,7,17⟩ .empty) ⟨3,false,8,0⟩ .empty) ⟨3,false,8,1⟩ (.node .empty ⟨3,false,8,2⟩ .empty)) ⟨3,false,8,4⟩ (.node (.node (.node .empty ⟨3,false,8,5⟩ .empty) ⟨3,false,8,7⟩ .empty) ⟨3,false,8,8⟩ (.node .empty ⟨3,false,8,14⟩ .empty)))
def t65_85 : Tree := .node t65_75 ⟨3,false,7,15⟩ t76_85
def t43_85 : Tree := .node t43_64 ⟨3,false,2,1⟩ t65_85
def t0_85 : Tree := .node t0_42 ⟨2,false,2,14⟩ t43_85
def t86_96 : Tree := (.node (.node (.node (.node .empty ⟨3,false,8,17⟩ .empty) ⟨3,true,0,7⟩ .empty) ⟨3,true,0,8⟩ (.node (.node .empty ⟨3,true,1,2⟩ .empty) ⟨3,true,3,1⟩ .empty)) ⟨3,true,3,4⟩ (.node (.node (.node .empty ⟨3,true,3,7⟩ .empty) ⟨3,true,3,8⟩ .empty) ⟨3,true,3,10⟩ (.node .empty ⟨3,true,3,19⟩ .empty)))
def t97_107 : Tree := (.node (.node (.node (.node .empty ⟨3,true,6,7⟩ .empty) ⟨3,true,6,8⟩ .empty) ⟨3,true,6,15⟩ (.node (.node .empty ⟨3,true,6,17⟩ .empty) ⟨3,true,8,1⟩ .empty)) ⟨3,true,8,4⟩ (.node (.node (.node .empty ⟨3,true,8,7⟩ .empty) ⟨3,true,8,8⟩ .empty) ⟨3,true,8,10⟩ (.node .empty ⟨3,true,8,19⟩ .empty)))
def t86_107 : Tree := .node t86_96 ⟨3,true,6,2⟩ t97_107
def t108_118 : Tree := (.node (.node (.node (.node .empty ⟨4,true,1,5⟩ .empty) ⟨4,true,1,14⟩ .empty) ⟨4,true,1,15⟩ (.node (.node .empty ⟨4,true,1,17⟩ .empty) ⟨4,true,2,1⟩ .empty)) ⟨4,true,5,0⟩ (.node (.node (.node .empty ⟨4,true,5,2⟩ .empty) ⟨4,true,5,3⟩ .empty) ⟨4,true,5,5⟩ (.node .empty ⟨4,true,5,9⟩ .empty)))
def t119_128 : Tree := (.node (.node (.node (.node .empty ⟨4,true,5,15⟩ .empty) ⟨4,true,5,16⟩ .empty) ⟨4,true,5,17⟩ (.node .empty ⟨4,true,5,18⟩ .empty)) ⟨4,true,7,1⟩ (.node (.node (.node .empty ⟨4,true,7,2⟩ .empty) ⟨4,true,7,5⟩ .empty) ⟨4,true,7,7⟩ (.node .empty ⟨4,true,7,8⟩ .empty)))
def t108_128 : Tree := .node t108_118 ⟨4,true,5,14⟩ t119_128
def t86_128 : Tree := .node t86_107 ⟨4,true,1,2⟩ t108_128
def t129_139 : Tree := (.node (.node (.node (.node .empty ⟨4,true,7,15⟩ .empty) ⟨4,true,7,17⟩ .empty) ⟨5,false,0,5⟩ (.node (.node .empty ⟨5,false,0,10⟩ .empty) ⟨5,false,0,15⟩ .empty)) ⟨5,false,2,1⟩ (.node (.node (.node .empty ⟨5,false,2,10⟩ .empty) ⟨5,false,2,12⟩ .empty) ⟨5,false,7,1⟩ (.node .empty ⟨5,false,7,10⟩ .empty)))
def t140_149 : Tree := (.node (.node (.node (.node .empty ⟨5,true,0,4⟩ .empty) ⟨5,true,0,8⟩ .empty) ⟨5,true,0,9⟩ (.node .empty ⟨5,true,1,3⟩ .empty)) ⟨5,true,1,5⟩ (.node (.node (.node .empty ⟨5,true,1,14⟩ .empty) ⟨5,true,1,15⟩ .empty) ⟨5,true,2,4⟩ (.node .empty ⟨5,true,2,8⟩ .empty)))
def t129_149 : Tree := .node t129_139 ⟨5,false,7,12⟩ t140_149
def t150_160 : Tree := (.node (.node (.node (.node .empty ⟨5,true,2,19⟩ .empty) ⟨5,true,3,0⟩ .empty) ⟨5,true,3,6⟩ (.node (.node .empty ⟨5,true,3,9⟩ .empty) ⟨5,true,3,11⟩ .empty)) ⟨5,true,6,3⟩ (.node (.node (.node .empty ⟨5,true,6,5⟩ .empty) ⟨5,true,6,9⟩ .empty) ⟨5,true,6,14⟩ (.node .empty ⟨5,true,6,15⟩ .empty)))
def t161_170 : Tree := (.node (.node (.node (.node .empty ⟨5,true,6,18⟩ .empty) ⟨5,true,7,4⟩ .empty) ⟨5,true,7,8⟩ (.node .empty ⟨5,true,7,10⟩ .empty)) ⟨5,true,7,19⟩ (.node (.node (.node .empty ⟨5,true,8,0⟩ .empty) ⟨5,true,8,6⟩ .empty) ⟨5,true,8,9⟩ (.node .empty ⟨5,true,8,11⟩ .empty)))
def t150_170 : Tree := .node t150_160 ⟨5,true,6,16⟩ t161_170
def t129_170 : Tree := .node t129_149 ⟨5,true,2,10⟩ t150_170
def t86_170 : Tree := .node t86_128 ⟨4,true,7,14⟩ t129_170
def t0_170 : Tree := .node t0_85 ⟨3,false,8,15⟩ t86_170
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 6, 0, 5, 0, 0, 0, 0, 0, 7, 8, 6, 0, 5],#[0, 1, 3, 2, 9, 7, 6, 4, 3, 5, 9, 8, 13, 12, 18, 17, 16, 15, 11, 10, 0, 14, 13, 12, 0, 0, 0, 0, 9, 8, 9, 8, 6, 19, 9, 7, 6, 19, 0, 14],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1)],[(true,3),(true,8)],[(true,2),(true,7)],[(true,6)],[(false,7)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1),(false,4)],[(true,3)],[(true,4)],[(false,3),(false,16),(false,18)],[(true,2),(true,17)],[(true,5),(true,14),(true,15)],[(false,2),(false,5),(false,14),(false,15),(false,17)],[(true,9)],[(false,9)],[(true,6),(true,11)],[(false,6),(false,11)],[(true,10),(true,19)],[(true,8)],[(false,8)],[(true,7)],[(false,7)],[(true,16),(true,18)]],
  t0_170⟩
theorem check0_10 : t0_10.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check11_21 : t11_21.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node10 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,0,3⟩ = true := by decide
theorem check0_21 : t0_21.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node10 check0_10 check11_21
theorem check22_32 : t22_32.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check33_42 : t33_42.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node32 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,8,0⟩ = true := by decide
theorem check22_42 : t22_42.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node32 check22_32 check33_42
theorem node21 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,6,11⟩ = true := by decide
theorem check0_42 : t0_42.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node21 check0_21 check22_42
theorem check43_53 : t43_53.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check54_64 : t54_64.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node53 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,7,17⟩ = true := by decide
theorem check43_64 : t43_64.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node53 check43_53 check54_64
theorem check65_75 : t65_75.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check76_85 : t76_85.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node75 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,7,15⟩ = true := by decide
theorem check65_85 : t65_85.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node75 check65_75 check76_85
theorem node64 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,2,1⟩ = true := by decide
theorem check43_85 : t43_85.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node64 check43_64 check65_85
theorem node42 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,2,14⟩ = true := by decide
theorem check0_85 : t0_85.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node42 check0_42 check43_85
theorem check86_96 : t86_96.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check97_107 : t97_107.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node96 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,6,2⟩ = true := by decide
theorem check86_107 : t86_107.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node96 check86_96 check97_107
theorem check108_118 : t108_118.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check119_128 : t119_128.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node118 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,5,14⟩ = true := by decide
theorem check108_128 : t108_128.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node118 check108_118 check119_128
theorem node107 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,1,2⟩ = true := by decide
theorem check86_128 : t86_128.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node107 check86_107 check108_128
theorem check129_139 : t129_139.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check140_149 : t140_149.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node139 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,7,12⟩ = true := by decide
theorem check129_149 : t129_149.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node139 check129_139 check140_149
theorem check150_160 : t150_160.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check161_170 : t161_170.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node160 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,6,16⟩ = true := by decide
theorem check150_170 : t150_170.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node160 check150_160 check161_170
theorem node149 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,2,10⟩ = true := by decide
theorem check129_170 : t129_170.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node149 check129_149 check150_170
theorem node128 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,7,14⟩ = true := by decide
theorem check86_170 : t86_170.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node128 check86_128 check129_170
theorem node85 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,8,15⟩ = true := by decide
theorem check0_170 : t0_170.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node85 check0_85 check86_170
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_170
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M089
