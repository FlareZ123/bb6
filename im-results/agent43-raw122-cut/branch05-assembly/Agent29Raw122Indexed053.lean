import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M053
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
def t0_10 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,4⟩ .empty) ⟨0,false,2,2⟩ (.node (.node .empty ⟨0,false,2,11⟩ .empty) ⟨0,false,7,0⟩ .empty)) ⟨0,false,7,4⟩ (.node (.node (.node .empty ⟨0,true,2,2⟩ .empty) ⟨0,true,2,11⟩ .empty) ⟨0,true,5,1⟩ (.node .empty ⟨0,true,5,10⟩ .empty)))
def t11_20 : Tree := (.node (.node (.node (.node .empty ⟨0,true,6,5⟩ .empty) ⟨1,false,1,0⟩ .empty) ⟨1,false,1,3⟩ (.node .empty ⟨1,true,3,1⟩ .empty)) ⟨1,true,3,10⟩ (.node (.node (.node .empty ⟨1,true,5,1⟩ .empty) ⟨1,true,5,10⟩ .empty) ⟨2,false,2,0⟩ (.node .empty ⟨2,false,2,1⟩ .empty)))
def t0_20 : Tree := .node t0_10 ⟨0,true,6,0⟩ t11_20
def t21_31 : Tree := (.node (.node (.node (.node .empty ⟨2,false,2,8⟩ .empty) ⟨3,false,2,1⟩ .empty) ⟨3,false,2,8⟩ (.node (.node .empty ⟨3,false,3,0⟩ .empty) ⟨3,false,3,6⟩ .empty)) ⟨3,true,1,2⟩ (.node (.node (.node .empty ⟨3,true,1,9⟩ .empty) ⟨3,true,3,0⟩ .empty) ⟨3,true,3,6⟩ (.node .empty ⟨4,false,4,0⟩ .empty)))
def t32_41 : Tree := (.node (.node (.node (.node .empty ⟨4,true,2,1⟩ .empty) ⟨4,true,2,8⟩ .empty) ⟨5,false,0,5⟩ (.node .empty ⟨5,true,0,4⟩ .empty)) ⟨5,true,1,3⟩ (.node (.node (.node .empty ⟨5,true,2,7⟩ .empty) ⟨5,true,5,6⟩ .empty) ⟨5,true,6,5⟩ (.node .empty ⟨5,true,7,4⟩ .empty)))
def t21_41 : Tree := .node t21_31 ⟨4,false,4,5⟩ t32_41
def t0_41 : Tree := .node t0_20 ⟨2,false,2,7⟩ t21_41
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 5, 0, 4, 0, 0, 0, 6, 0, 7, 0, 1],#[0, 1, 3, 2, 0, 0, 4, 0, 5, 0, 6, 10, 7, 8, 3, 0, 3, 9, 0, 0, 0, 11, 0, 0],
  #[[(false,0)],[(true,0),(true,7)],[(true,1)],[(false,2)],[(true,3)],[(true,2)],[(true,5)],[(true,6)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1),(false,7),(false,8)],[(false,3)],[(false,4)],[(false,5)],[(false,6)],[(true,6)],[(true,8)],[(true,5)],[(true,10)]],
  t0_41⟩
theorem check0_10 : t0_10.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check11_20 : t11_20.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node10 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,true,6,0⟩ = true := by decide
theorem check0_20 : t0_20.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node10 check0_10 check11_20
theorem check21_31 : t21_31.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check32_41 : t32_41.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node31 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,4,5⟩ = true := by decide
theorem check21_41 : t21_41.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node31 check21_31 check32_41
theorem node20 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,2,7⟩ = true := by decide
theorem check0_41 : t0_41.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node20 check0_20 check21_41
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_41
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M053
