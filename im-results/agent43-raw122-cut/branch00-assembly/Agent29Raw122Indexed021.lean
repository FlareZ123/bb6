import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M021
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_9 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,4⟩ .empty) ⟨0,false,2,8⟩ (.node .empty ⟨0,false,3,1⟩ .empty)) ⟨0,false,3,13⟩ (.node (.node (.node .empty ⟨0,false,8,0⟩ .empty) ⟨0,false,8,4⟩ .empty) ⟨0,true,0,4⟩ (.node .empty ⟨0,true,2,9⟩ .empty)))
def t10_18 : Tree := (.node (.node (.node (.node .empty ⟨1,false,1,0⟩ .empty) ⟨1,false,1,3⟩ .empty) ⟨1,false,1,10⟩ (.node .empty ⟨1,false,7,7⟩ .empty)) ⟨1,true,4,0⟩ (.node (.node .empty ⟨1,true,4,4⟩ .empty) ⟨2,false,2,0⟩ (.node .empty ⟨2,false,2,1⟩ .empty)))
def t0_18 : Tree := .node t0_9 ⟨0,true,8,4⟩ t10_18
def t19_28 : Tree := (.node (.node (.node (.node .empty ⟨2,false,2,11⟩ .empty) ⟨2,false,5,0⟩ .empty) ⟨2,false,5,3⟩ (.node .empty ⟨2,false,5,10⟩ .empty)) ⟨2,false,8,2⟩ (.node (.node (.node .empty ⟨2,false,8,6⟩ .empty) ⟨2,false,8,16⟩ .empty) ⟨3,false,2,1⟩ (.node .empty ⟨3,false,2,11⟩ .empty)))
def t29_37 : Tree := (.node (.node (.node (.node .empty ⟨3,false,3,5⟩ .empty) ⟨3,false,4,2⟩ .empty) ⟨3,false,4,6⟩ (.node .empty ⟨3,false,4,16⟩ .empty)) ⟨3,false,5,1⟩ (.node (.node .empty ⟨3,false,5,2⟩ .empty) ⟨3,false,5,12⟩ (.node .empty ⟨3,false,5,15⟩ .empty)))
def t19_37 : Tree := .node t19_28 ⟨3,false,3,0⟩ t29_37
def t0_37 : Tree := .node t0_18 ⟨2,false,2,9⟩ t19_37
def t38_47 : Tree := (.node (.node (.node (.node .empty ⟨3,false,6,1⟩ .empty) ⟨3,false,6,9⟩ .empty) ⟨3,false,6,11⟩ (.node .empty ⟨3,true,1,2⟩ .empty)) ⟨3,true,1,12⟩ (.node (.node (.node .empty ⟨3,true,3,0⟩ .empty) ⟨3,true,3,5⟩ .empty) ⟨3,true,3,6⟩ (.node .empty ⟨3,true,3,17⟩ .empty)))
def t48_56 : Tree := (.node (.node (.node (.node .empty ⟨3,true,9,2⟩ .empty) ⟨3,true,9,12⟩ .empty) ⟨3,true,9,15⟩ (.node .empty ⟨4,false,4,0⟩ .empty)) ⟨4,false,4,4⟩ (.node (.node .empty ⟨4,true,2,1⟩ .empty) ⟨4,true,2,11⟩ (.node .empty ⟨4,true,3,1⟩ .empty)))
def t38_56 : Tree := .node t38_47 ⟨3,true,9,1⟩ t48_56
def t57_65 : Tree := (.node (.node (.node (.node .empty ⟨4,true,4,2⟩ .empty) ⟨4,true,4,6⟩ .empty) ⟨4,true,4,16⟩ (.node .empty ⟨4,true,10,0⟩ .empty)) ⟨4,true,10,1⟩ (.node (.node .empty ⟨4,true,10,9⟩ .empty) ⟨4,true,10,11⟩ (.node .empty ⟨5,false,0,5⟩ .empty)))
def t66_74 : Tree := (.node (.node (.node (.node .empty ⟨5,false,2,14⟩ .empty) ⟨5,true,1,3⟩ .empty) ⟨5,true,1,10⟩ (.node .empty ⟨5,true,3,7⟩ .empty)) ⟨5,true,7,5⟩ (.node (.node .empty ⟨5,true,9,0⟩ .empty) ⟨5,true,9,3⟩ (.node .empty ⟨5,true,9,10⟩ .empty)))
def t57_74 : Tree := .node t57_65 ⟨5,false,2,3⟩ t66_74
def t38_74 : Tree := .node t38_56 ⟨4,true,3,13⟩ t57_74
def t0_74 : Tree := .node t0_37 ⟨3,false,6,0⟩ t38_74
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 7, 0, 4, 5, 0, 6, 0, 0, 0, 0, 8, 9, 1, 0, 10, 0, 0],#[0, 1, 3, 2, 7, 6, 4, 0, 5, 13, 9, 11, 7, 17, 8, 0, 0, 0, 10, 15, 4, 0, 10, 12, 0, 16, 14, 0, 0, 0, 0, 16, 7, 17, 0, 0],
  #[[(false,0)],[(true,0),(true,8)],[(true,1)],[(false,2)],[(true,3)],[(false,4)],[(false,5)],[(true,2)],[(true,7)],[(false,8)],[(true,9)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3),(false,10)],[(false,4)],[(true,2)],[(false,2),(false,6),(false,16)],[(false,7)],[(false,5)],[(false,9),(false,11)],[(true,5)],[(true,11)],[(true,4)],[(false,13)],[(true,9)],[(true,12),(true,15)],[(true,6),(true,16)]],
  t0_74⟩
theorem check0_9 : t0_9.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check10_18 : t10_18.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node9 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,8,4⟩ = true := by decide
theorem check0_18 : t0_18.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node9 check0_9 check10_18
theorem check19_28 : t19_28.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check29_37 : t29_37.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node28 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,3,0⟩ = true := by decide
theorem check19_37 : t19_37.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node28 check19_28 check29_37
theorem node18 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,2,9⟩ = true := by decide
theorem check0_37 : t0_37.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node18 check0_18 check19_37
theorem check38_47 : t38_47.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check48_56 : t48_56.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node47 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,9,1⟩ = true := by decide
theorem check38_56 : t38_56.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node47 check38_47 check48_56
theorem check57_65 : t57_65.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check66_74 : t66_74.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node65 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,2,3⟩ = true := by decide
theorem check57_74 : t57_74.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node65 check57_65 check66_74
theorem node56 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,3,13⟩ = true := by decide
theorem check38_74 : t38_74.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node56 check38_56 check57_74
theorem node37 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,6,0⟩ = true := by decide
theorem check0_74 : t0_74.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node37 check0_37 check38_74
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_74
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M021
