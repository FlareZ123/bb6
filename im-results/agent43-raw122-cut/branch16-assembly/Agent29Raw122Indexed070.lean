import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M070
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
def t0_10 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,2,0⟩ .empty) ⟨0,false,2,1⟩ (.node (.node .empty ⟨0,false,2,2⟩ .empty) ⟨0,false,2,4⟩ .empty)) ⟨0,false,2,6⟩ (.node (.node (.node .empty ⟨0,false,5,0⟩ .empty) ⟨0,false,5,1⟩ .empty) ⟨0,false,5,4⟩ (.node .empty ⟨0,false,9,0⟩ .empty)))
def t11_20 : Tree := (.node (.node (.node (.node .empty ⟨0,false,9,4⟩ .empty) ⟨0,true,2,0⟩ .empty) ⟨0,true,2,3⟩ (.node .empty ⟨1,false,0,5⟩ .empty)) ⟨1,false,1,0⟩ (.node (.node (.node .empty ⟨1,false,2,0⟩ .empty) ⟨1,false,2,3⟩ .empty) ⟨1,false,5,0⟩ (.node .empty ⟨1,false,8,0⟩ .empty)))
def t0_20 : Tree := .node t0_10 ⟨0,false,9,1⟩ t11_20
def t21_30 : Tree := (.node (.node (.node (.node .empty ⟨1,true,1,8⟩ .empty) ⟨1,true,2,0⟩ .empty) ⟨1,true,2,3⟩ (.node .empty ⟨1,true,5,0⟩ .empty)) ⟨1,true,5,1⟩ (.node (.node (.node .empty ⟨1,true,5,3⟩ .empty) ⟨1,true,5,4⟩ .empty) ⟨1,true,8,0⟩ (.node .empty ⟨1,true,8,3⟩ .empty)))
def t31_40 : Tree := (.node (.node (.node (.node .empty ⟨2,false,2,0⟩ .empty) ⟨2,false,5,0⟩ .empty) ⟨2,false,5,1⟩ (.node .empty ⟨2,false,5,4⟩ .empty)) ⟨2,false,9,0⟩ (.node (.node (.node .empty ⟨3,false,1,2⟩ .empty) ⟨3,false,1,6⟩ .empty) ⟨3,false,2,1⟩ (.node .empty ⟨3,false,3,0⟩ .empty)))
def t21_40 : Tree := .node t21_30 ⟨2,false,1,3⟩ t31_40
def t0_40 : Tree := .node t0_20 ⟨1,true,1,3⟩ t21_40
def t41_51 : Tree := (.node (.node (.node (.node .empty ⟨3,false,4,4⟩ .empty) ⟨3,false,5,1⟩ .empty) ⟨3,false,6,0⟩ (.node (.node .empty ⟨3,false,9,1⟩ .empty) ⟨3,true,0,7⟩ .empty)) ⟨3,true,1,2⟩ (.node (.node (.node .empty ⟨3,true,2,2⟩ .empty) ⟨3,true,5,2⟩ .empty) ⟨3,true,6,0⟩ (.node .empty ⟨3,true,6,3⟩ .empty)))
def t52_61 : Tree := (.node (.node (.node (.node .empty ⟨4,false,0,4⟩ .empty) ⟨4,false,0,9⟩ .empty) ⟨4,false,5,4⟩ (.node .empty ⟨4,false,7,0⟩ .empty)) ⟨4,false,7,1⟩ (.node (.node (.node .empty ⟨4,false,7,4⟩ .empty) ⟨4,false,9,4⟩ .empty) ⟨4,true,0,4⟩ (.node .empty ⟨4,true,1,2⟩ .empty)))
def t41_61 : Tree := .node t41_51 ⟨3,true,8,2⟩ t52_61
def t62_71 : Tree := (.node (.node (.node (.node .empty ⟨4,true,1,6⟩ .empty) ⟨4,true,2,1⟩ .empty) ⟨4,true,2,4⟩ (.node .empty ⟨4,true,5,1⟩ .empty)) ⟨4,true,5,4⟩ (.node (.node (.node .empty ⟨4,true,7,4⟩ .empty) ⟨4,true,9,1⟩ .empty) ⟨4,true,9,4⟩ (.node .empty ⟨5,false,0,3⟩ .empty)))
def t72_81 : Tree := (.node (.node (.node (.node .empty ⟨5,false,3,1⟩ .empty) ⟨5,false,3,4⟩ .empty) ⟨5,true,0,3⟩ (.node .empty ⟨5,true,0,8⟩ .empty)) ⟨5,true,1,3⟩ (.node (.node (.node .empty ⟨5,true,2,3⟩ .empty) ⟨5,true,5,3⟩ .empty) ⟨5,true,6,3⟩ (.node .empty ⟨5,true,8,3⟩ .empty)))
def t62_81 : Tree := .node t62_71 ⟨5,false,3,0⟩ t72_81
def t41_81 : Tree := .node t41_61 ⟨4,true,1,4⟩ t62_81
def t0_81 : Tree := .node t0_40 ⟨3,false,4,1⟩ t41_81
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 5, 0, 0, 0, 0, 6, 2, 0, 7, 0, 8, 0, 9, 6, 8],#[0, 1, 3, 2, 8, 7, 5, 4, 3, 6, 0, 0, 8, 7, 0, 0, 0, 9, 0, 0],
  #[[(false,0)],[(true,0)],[(true,1),(true,5)],[(false,2)],[(false,1)],[(true,2)],[(false,5),(false,9)],[(true,6)],[(true,7),(true,9)],[(true,8)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1),(false,4)],[(true,3)],[(false,3)],[(true,4)],[(true,2),(true,6)],[(false,2),(false,6)],[(true,8)]],
  t0_81⟩
theorem check0_10 : t0_10.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check11_20 : t11_20.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node10 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,9,1⟩ = true := by decide
theorem check0_20 : t0_20.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node10 check0_10 check11_20
theorem check21_30 : t21_30.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check31_40 : t31_40.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node30 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,1,3⟩ = true := by decide
theorem check21_40 : t21_40.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node30 check21_30 check31_40
theorem node20 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,1,3⟩ = true := by decide
theorem check0_40 : t0_40.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node20 check0_20 check21_40
theorem check41_51 : t41_51.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check52_61 : t52_61.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node51 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,8,2⟩ = true := by decide
theorem check41_61 : t41_61.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node51 check41_51 check52_61
theorem check62_71 : t62_71.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check72_81 : t72_81.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node71 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,3,0⟩ = true := by decide
theorem check62_81 : t62_81.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node71 check62_71 check72_81
theorem node61 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,1,4⟩ = true := by decide
theorem check41_81 : t41_81.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node61 check41_61 check62_81
theorem node40 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,4,1⟩ = true := by decide
theorem check0_81 : t0_81.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node40 check0_40 check41_81
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_81
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M070
