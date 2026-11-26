import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M076
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
def t0_14 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,4⟩ (.node .empty ⟨0,false,0,6⟩ .empty)) ⟨0,false,4,4⟩ (.node (.node .empty ⟨0,false,4,6⟩ .empty) ⟨0,true,0,4⟩ (.node .empty ⟨0,true,0,6⟩ .empty))) ⟨0,true,4,4⟩ (.node (.node (.node .empty ⟨0,true,4,6⟩ .empty) ⟨1,false,1,0⟩ (.node .empty ⟨1,false,4,1⟩ .empty)) ⟨1,false,4,4⟩ (.node (.node .empty ⟨1,true,1,3⟩ .empty) ⟨1,true,1,5⟩ .empty)))
def t15_28 : Tree := (.node (.node (.node (.node .empty ⟨1,true,4,4⟩ .empty) ⟨1,true,4,6⟩ (.node .empty ⟨1,true,5,3⟩ .empty)) ⟨1,true,5,5⟩ (.node (.node .empty ⟨1,true,5,7⟩ .empty) ⟨1,true,7,3⟩ .empty)) ⟨1,true,7,5⟩ (.node (.node (.node .empty ⟨1,true,7,7⟩ .empty) ⟨2,false,2,0⟩ (.node .empty ⟨2,true,5,0⟩ .empty)) ⟨2,true,5,3⟩ (.node (.node .empty ⟨3,false,2,1⟩ .empty) ⟨3,false,3,0⟩ .empty)))
def t0_28 : Tree := .node t0_14 ⟨1,true,1,7⟩ t15_28
def t29_43 : Tree := (.node (.node (.node (.node .empty ⟨3,false,6,1⟩ .empty) ⟨3,false,6,4⟩ (.node .empty ⟨3,true,1,2⟩ .empty)) ⟨3,true,5,1⟩ (.node (.node .empty ⟨3,true,5,2⟩ .empty) ⟨3,true,5,5⟩ (.node .empty ⟨4,true,0,4⟩ .empty))) ⟨4,true,2,1⟩ (.node (.node (.node .empty ⟨4,true,4,1⟩ .empty) ⟨4,true,4,4⟩ (.node .empty ⟨4,true,6,0⟩ .empty)) ⟨4,true,6,1⟩ (.node (.node .empty ⟨4,true,6,4⟩ .empty) ⟨5,false,0,3⟩ .empty)))
def t44_57 : Tree := (.node (.node (.node (.node .empty ⟨5,false,0,7⟩ .empty) ⟨5,false,1,3⟩ (.node .empty ⟨5,false,1,5⟩ .empty)) ⟨5,false,1,7⟩ (.node (.node .empty ⟨5,false,5,3⟩ .empty) ⟨5,false,5,5⟩ .empty)) ⟨5,false,5,7⟩ (.node (.node (.node .empty ⟨5,false,7,3⟩ .empty) ⟨5,false,7,5⟩ (.node .empty ⟨5,false,7,7⟩ .empty)) ⟨5,true,1,3⟩ (.node (.node .empty ⟨5,true,5,0⟩ .empty) ⟨5,true,5,3⟩ .empty)))
def t29_57 : Tree := .node t29_43 ⟨5,false,0,5⟩ t44_57
def t0_57 : Tree := .node t0_28 ⟨3,false,6,0⟩ t29_57
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 0, 0, 0, 7, 5, 4, 6, 0, 0, 4, 0],#[0, 1, 3, 2, 0, 0, 0, 4, 3, 5, 0, 6, 0, 7, 0, 6],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,2)],[(false,1),(false,5),(false,7)],[(true,4)],[(true,5)],[(false,4)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1),(false,4)],[(true,3)],[(true,4)],[(true,5),(true,7)],[(true,6)]],
  t0_57⟩
theorem check0_14 : t0_14.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check15_28 : t15_28.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node14 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,1,7⟩ = true := by decide
theorem check0_28 : t0_28.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node14 check0_14 check15_28
theorem check29_43 : t29_43.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check44_57 : t44_57.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node43 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,0,5⟩ = true := by decide
theorem check29_57 : t29_57.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node43 check29_43 check44_57
theorem node28 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,6,0⟩ = true := by decide
theorem check0_57 : t0_57.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node28 check0_28 check29_57
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_57
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M076
