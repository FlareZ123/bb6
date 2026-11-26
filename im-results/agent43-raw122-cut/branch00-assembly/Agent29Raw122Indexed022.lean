import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M022
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_10 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,7⟩ .empty) ⟨0,false,1,1⟩ (.node (.node .empty ⟨0,false,1,5⟩ .empty) ⟨0,false,2,0⟩ .empty)) ⟨0,false,2,7⟩ (.node (.node (.node .empty ⟨0,false,7,1⟩ .empty) ⟨0,false,7,5⟩ .empty) ⟨0,false,10,2⟩ (.node .empty ⟨0,true,0,4⟩ .empty)))
def t11_21 : Tree := (.node (.node (.node (.node .empty ⟨0,true,2,4⟩ .empty) ⟨0,true,8,7⟩ .empty) ⟨1,false,0,5⟩ (.node (.node .empty ⟨1,false,1,0⟩ .empty) ⟨1,false,1,2⟩ .empty)) ⟨1,false,1,6⟩ (.node (.node (.node .empty ⟨1,false,2,5⟩ .empty) ⟨1,false,8,0⟩ .empty) ⟨1,false,8,2⟩ (.node .empty ⟨1,false,8,6⟩ .empty)))
def t0_21 : Tree := .node t0_10 ⟨0,true,1,7⟩ t11_21
def t22_32 : Tree := (.node (.node (.node (.node .empty ⟨1,true,1,1⟩ .empty) ⟨1,true,1,5⟩ .empty) ⟨1,true,2,0⟩ (.node (.node .empty ⟨1,true,2,2⟩ .empty) ⟨1,true,3,2⟩ .empty)) ⟨1,true,4,5⟩ (.node (.node (.node .empty ⟨1,true,7,1⟩ .empty) ⟨1,true,7,5⟩ .empty) ⟨1,true,8,1⟩ (.node .empty ⟨1,true,8,5⟩ .empty)))
def t33_42 : Tree := (.node (.node (.node (.node .empty ⟨1,true,9,2⟩ .empty) ⟨1,true,10,2⟩ .empty) ⟨1,true,11,1⟩ (.node .empty ⟨1,true,11,5⟩ .empty)) ⟨2,false,2,0⟩ (.node (.node (.node .empty ⟨2,false,2,2⟩ .empty) ⟨2,false,6,0⟩ .empty) ⟨2,true,1,2⟩ (.node .empty ⟨2,true,2,1⟩ .empty)))
def t22_42 : Tree := .node t22_32 ⟨1,true,9,0⟩ t33_42
def t0_42 : Tree := .node t0_21 ⟨1,true,0,2⟩ t22_42
def t43_53 : Tree := (.node (.node (.node (.node .empty ⟨2,true,3,0⟩ .empty) ⟨2,true,3,2⟩ .empty) ⟨2,true,4,1⟩ (.node (.node .empty ⟨2,true,4,5⟩ .empty) ⟨2,true,5,0⟩ .empty)) ⟨2,true,5,2⟩ (.node (.node (.node .empty ⟨2,true,6,1⟩ .empty) ⟨2,true,6,5⟩ .empty) ⟨2,true,8,2⟩ (.node .empty ⟨3,false,1,2⟩ .empty)))
def t54_64 : Tree := (.node (.node (.node (.node .empty ⟨3,false,2,5⟩ .empty) ⟨3,false,3,0⟩ .empty) ⟨3,false,3,2⟩ (.node (.node .empty ⟨3,false,4,1⟩ .empty) ⟨3,false,4,5⟩ .empty)) ⟨3,false,5,0⟩ (.node (.node (.node .empty ⟨3,false,5,2⟩ .empty) ⟨3,false,6,1⟩ .empty) ⟨3,false,6,5⟩ (.node .empty ⟨3,false,8,2⟩ .empty)))
def t43_64 : Tree := .node t43_53 ⟨3,false,2,1⟩ t54_64
def t65_75 : Tree := (.node (.node (.node (.node .empty ⟨3,true,1,2⟩ .empty) ⟨3,true,2,5⟩ .empty) ⟨3,true,3,1⟩ (.node (.node .empty ⟨3,true,3,5⟩ .empty) ⟨3,true,8,2⟩ .empty)) ⟨4,true,1,2⟩ (.node (.node (.node .empty ⟨4,true,2,1⟩ .empty) ⟨4,true,2,5⟩ .empty) ⟨4,true,7,0⟩ (.node .empty ⟨4,true,7,2⟩ .empty)))
def t76_85 : Tree := (.node (.node (.node (.node .empty ⟨5,false,0,3⟩ .empty) ⟨5,false,3,3⟩ .empty) ⟨5,false,4,6⟩ (.node .empty ⟨5,true,0,6⟩ .empty)) ⟨5,true,1,3⟩ (.node (.node (.node .empty ⟨5,true,2,6⟩ .empty) ⟨5,true,3,0⟩ .empty) ⟨5,true,3,6⟩ (.node .empty ⟨5,true,8,3⟩ .empty)))
def t65_85 : Tree := .node t65_75 ⟨4,true,8,2⟩ t76_85
def t43_85 : Tree := .node t43_64 ⟨3,true,0,5⟩ t65_85
def t0_85 : Tree := .node t0_42 ⟨2,true,2,5⟩ t43_85
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 8, 6, 7, 5, 10, 6, 0, 5, 0, 0, 9, 4, 2, 0, 0, 0, 11, 0, 0],#[0, 1, 3, 2, 6, 5, 4, 0, 0, 0, 3, 2, 7, 0, 0, 0],
  #[[(false,0)],[(true,0)],[(true,1),(true,8)],[(false,2)],[(false,1),(false,8)],[(false,4),(false,6)],[(false,3),(false,5)],[(true,3)],[(true,2)],[(true,7)],[(true,4)],[(true,10)]],
  #[[(false,0)],[(true,0)],[(true,1),(true,5)],[(false,1),(false,5)],[(false,3)],[(true,2)],[(false,2)],[(false,6)]],
  t0_85⟩
theorem check0_10 : t0_10.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check11_21 : t11_21.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node10 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,1,7⟩ = true := by decide
theorem check0_21 : t0_21.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node10 check0_10 check11_21
theorem check22_32 : t22_32.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check33_42 : t33_42.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node32 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,9,0⟩ = true := by decide
theorem check22_42 : t22_42.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node32 check22_32 check33_42
theorem node21 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,0,2⟩ = true := by decide
theorem check0_42 : t0_42.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node21 check0_21 check22_42
theorem check43_53 : t43_53.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check54_64 : t54_64.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node53 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,2,1⟩ = true := by decide
theorem check43_64 : t43_64.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node53 check43_53 check54_64
theorem check65_75 : t65_75.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check76_85 : t76_85.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node75 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,8,2⟩ = true := by decide
theorem check65_85 : t65_85.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node75 check65_75 check76_85
theorem node64 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,0,5⟩ = true := by decide
theorem check43_85 : t43_85.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node64 check43_64 check65_85
theorem node42 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,2,5⟩ = true := by decide
theorem check0_85 : t0_85.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node42 check0_42 check43_85
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_85
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M022
