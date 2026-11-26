import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M096
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def t0_14 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,2,3⟩ (.node .empty ⟨0,false,2,4⟩ .empty)) ⟨0,false,2,7⟩ (.node (.node .empty ⟨0,false,2,9⟩ .empty) ⟨0,false,2,11⟩ (.node .empty ⟨0,false,5,0⟩ .empty))) ⟨0,false,5,4⟩ (.node (.node (.node .empty ⟨0,false,6,0⟩ .empty) ⟨0,false,6,1⟩ (.node .empty ⟨0,false,8,0⟩ .empty)) ⟨0,false,11,1⟩ (.node (.node .empty ⟨0,false,11,3⟩ .empty) ⟨0,false,11,4⟩ .empty)))
def t15_28 : Tree := (.node (.node (.node (.node .empty ⟨0,false,11,9⟩ .empty) ⟨0,false,11,11⟩ (.node .empty ⟨0,true,1,4⟩ .empty)) ⟨0,true,1,5⟩ (.node (.node .empty ⟨0,true,1,9⟩ .empty) ⟨0,true,1,10⟩ .empty)) ⟨0,true,6,4⟩ (.node (.node (.node .empty ⟨0,true,6,5⟩ .empty) ⟨0,true,6,9⟩ (.node .empty ⟨0,true,6,10⟩ .empty)) ⟨0,true,11,5⟩ (.node (.node .empty ⟨1,false,1,0⟩ .empty) ⟨1,false,5,1⟩ .empty)))
def t0_28 : Tree := .node t0_14 ⟨0,false,11,7⟩ t15_28
def t29_42 : Tree := (.node (.node (.node (.node .empty ⟨1,false,9,0⟩ .empty) ⟨1,false,11,0⟩ (.node .empty ⟨1,true,5,0⟩ .empty)) ⟨1,true,5,3⟩ (.node (.node .empty ⟨1,true,5,5⟩ .empty) ⟨1,true,5,7⟩ .empty)) ⟨1,true,5,10⟩ (.node (.node (.node .empty ⟨1,true,5,11⟩ .empty) ⟨1,true,6,3⟩ (.node .empty ⟨1,true,11,0⟩ .empty)) ⟨2,false,2,0⟩ (.node (.node .empty ⟨2,false,5,0⟩ .empty) ⟨2,false,10,0⟩ .empty)))
def t43_56 : Tree := (.node (.node (.node (.node .empty ⟨2,true,6,0⟩ .empty) ⟨3,false,2,1⟩ (.node .empty ⟨3,false,3,0⟩ .empty)) ⟨3,false,5,1⟩ (.node (.node .empty ⟨3,false,10,1⟩ .empty) ⟨3,false,11,1⟩ .empty)) ⟨3,false,12,0⟩ (.node (.node (.node .empty ⟨3,true,1,2⟩ .empty) ⟨3,true,2,2⟩ (.node .empty ⟨3,true,6,2⟩ .empty)) ⟨3,true,9,2⟩ (.node (.node .empty ⟨3,true,11,2⟩ .empty) ⟨4,true,2,1⟩ .empty)))
def t29_56 : Tree := .node t29_42 ⟨2,false,11,0⟩ t43_56
def t0_56 : Tree := .node t0_28 ⟨1,false,6,0⟩ t29_56
def t57_70 : Tree := (.node (.node (.node (.node .empty ⟨4,true,4,4⟩ .empty) ⟨4,true,4,7⟩ (.node .empty ⟨4,true,4,9⟩ .empty)) ⟨4,true,4,11⟩ (.node (.node .empty ⟨4,true,5,1⟩ .empty) ⟨4,true,7,3⟩ .empty)) ⟨4,true,7,4⟩ (.node (.node (.node .empty ⟨4,true,7,7⟩ .empty) ⟨4,true,7,9⟩ (.node .empty ⟨4,true,7,11⟩ .empty)) ⟨4,true,10,1⟩ (.node (.node .empty ⟨4,true,11,1⟩ .empty) ⟨4,true,12,4⟩ .empty)))
def t71_84 : Tree := (.node (.node (.node (.node .empty ⟨5,false,0,7⟩ .empty) ⟨5,false,0,10⟩ (.node .empty ⟨5,false,0,11⟩ .empty)) ⟨5,false,1,6⟩ (.node (.node .empty ⟨5,false,1,8⟩ .empty) ⟨5,false,6,6⟩ .empty)) ⟨5,false,6,7⟩ (.node (.node (.node .empty ⟨5,false,6,8⟩ .empty) ⟨5,false,7,0⟩ (.node .empty ⟨5,false,11,8⟩ .empty)) ⟨5,true,0,4⟩ (.node (.node .empty ⟨5,true,0,5⟩ .empty) ⟨5,true,0,9⟩ .empty)))
def t57_84 : Tree := .node t57_70 ⟨5,false,0,5⟩ t71_84
def t85_98 : Tree := (.node (.node (.node (.node .empty ⟨5,true,1,3⟩ .empty) ⟨5,true,1,4⟩ (.node .empty ⟨5,true,1,7⟩ .empty)) ⟨5,true,1,9⟩ (.node (.node .empty ⟨5,true,1,11⟩ .empty) ⟨5,true,2,3⟩ .empty)) ⟨5,true,2,5⟩ (.node (.node (.node .empty ⟨5,true,2,7⟩ .empty) ⟨5,true,2,10⟩ (.node .empty ⟨5,true,2,11⟩ .empty)) ⟨5,true,5,4⟩ (.node (.node .empty ⟨5,true,5,5⟩ .empty) ⟨5,true,5,9⟩ .empty)))
def t99_112 : Tree := (.node (.node (.node (.node .empty ⟨5,true,6,3⟩ .empty) ⟨5,true,6,4⟩ (.node .empty ⟨5,true,6,7⟩ .empty)) ⟨5,true,6,9⟩ (.node (.node .empty ⟨5,true,6,11⟩ .empty) ⟨5,true,7,5⟩ .empty)) ⟨5,true,8,4⟩ (.node (.node (.node .empty ⟨5,true,9,3⟩ .empty) ⟨5,true,11,3⟩ (.node .empty ⟨5,true,11,5⟩ .empty)) ⟨5,true,11,7⟩ (.node (.node .empty ⟨5,true,11,10⟩ .empty) ⟨5,true,11,11⟩ .empty)))
def t85_112 : Tree := .node t85_98 ⟨5,true,5,10⟩ t99_112
def t57_112 : Tree := .node t57_84 ⟨5,true,0,10⟩ t85_112
def t0_112 : Tree := .node t0_56 ⟨4,true,4,3⟩ t57_112
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 5, 0, 0, 0, 0, 3, 6, 7, 11, 0, 8, 0, 9, 0, 10, 3, 0, 12, 5, 0, 0],#[0, 1, 3, 2, 0, 0, 6, 4, 8, 5, 0, 7, 0, 0, 6, 9, 0, 0, 6, 10, 0, 11, 6, 9],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2),(false,5),(false,10)],[(false,1)],[(true,2),(true,11)],[(true,5)],[(false,6)],[(true,7)],[(true,8)],[(true,9)],[(true,6)],[(false,11)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3)],[(true,4)],[(false,3),(false,7),(false,9),(false,11)],[(true,5)],[(false,4)],[(true,7),(true,11)],[(true,9)],[(true,10)]],
  t0_112⟩
theorem check0_14 : t0_14.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check15_28 : t15_28.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node14 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,11,7⟩ = true := by decide
theorem check0_28 : t0_28.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node14 check0_14 check15_28
theorem check29_42 : t29_42.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check43_56 : t43_56.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node42 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,11,0⟩ = true := by decide
theorem check29_56 : t29_56.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node42 check29_42 check43_56
theorem node28 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,6,0⟩ = true := by decide
theorem check0_56 : t0_56.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node28 check0_28 check29_56
theorem check57_70 : t57_70.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check71_84 : t71_84.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node70 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,0,5⟩ = true := by decide
theorem check57_84 : t57_84.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node70 check57_70 check71_84
theorem check85_98 : t85_98.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check99_112 : t99_112.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node98 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,5,10⟩ = true := by decide
theorem check85_112 : t85_112.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node98 check85_98 check99_112
theorem node84 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,0,10⟩ = true := by decide
theorem check57_112 : t57_112.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node84 check57_84 check85_112
theorem node56 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,4,3⟩ = true := by decide
theorem check0_112 : t0_112.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node56 check0_56 check57_112
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_112
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M096
