import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M017
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,0⟩)
  | _,_ => none
def t0_15 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,4⟩ (.node .empty ⟨0,false,2,8⟩ .empty)) ⟨0,false,8,0⟩ (.node (.node .empty ⟨0,false,8,4⟩ .empty) ⟨0,true,0,4⟩ (.node .empty ⟨0,true,2,9⟩ .empty))) ⟨0,true,8,4⟩ (.node (.node (.node .empty ⟨1,false,1,0⟩ .empty) ⟨1,false,1,3⟩ (.node .empty ⟨1,false,7,7⟩ .empty)) ⟨2,false,2,0⟩ (.node (.node .empty ⟨2,false,2,1⟩ .empty) ⟨2,false,2,9⟩ (.node .empty ⟨2,false,2,10⟩ .empty))))
def t16_31 : Tree := (.node (.node (.node (.node .empty ⟨2,false,5,3⟩ .empty) ⟨2,false,8,2⟩ (.node .empty ⟨2,false,8,6⟩ .empty)) ⟨2,false,8,13⟩ (.node (.node .empty ⟨3,false,2,1⟩ .empty) ⟨3,false,2,10⟩ (.node .empty ⟨3,false,3,0⟩ .empty))) ⟨3,false,3,5⟩ (.node (.node (.node .empty ⟨3,false,4,2⟩ .empty) ⟨3,false,4,6⟩ (.node .empty ⟨3,false,4,13⟩ .empty)) ⟨3,false,5,1⟩ (.node (.node .empty ⟨3,false,5,2⟩ .empty) ⟨3,false,5,11⟩ (.node .empty ⟨3,false,5,12⟩ .empty))))
def t0_31 : Tree := .node t0_15 ⟨2,false,5,0⟩ t16_31
def t32_47 : Tree := (.node (.node (.node (.node .empty ⟨3,false,6,1⟩ .empty) ⟨3,false,6,9⟩ (.node .empty ⟨3,false,6,10⟩ .empty)) ⟨3,true,1,2⟩ (.node (.node .empty ⟨3,true,1,11⟩ .empty) ⟨3,true,3,0⟩ (.node .empty ⟨3,true,3,5⟩ .empty))) ⟨3,true,3,6⟩ (.node (.node (.node .empty ⟨3,true,3,14⟩ .empty) ⟨3,true,9,1⟩ (.node .empty ⟨3,true,9,2⟩ .empty)) ⟨3,true,9,11⟩ (.node (.node .empty ⟨3,true,9,12⟩ .empty) ⟨4,false,4,0⟩ (.node .empty ⟨4,false,4,4⟩ .empty))))
def t48_62 : Tree := (.node (.node (.node (.node .empty ⟨4,true,2,10⟩ .empty) ⟨4,true,4,2⟩ (.node .empty ⟨4,true,4,6⟩ .empty)) ⟨4,true,4,13⟩ (.node (.node .empty ⟨4,true,10,0⟩ .empty) ⟨4,true,10,1⟩ (.node .empty ⟨4,true,10,9⟩ .empty))) ⟨4,true,10,10⟩ (.node (.node (.node .empty ⟨5,false,0,5⟩ .empty) ⟨5,true,1,3⟩ (.node .empty ⟨5,true,3,7⟩ .empty)) ⟨5,true,7,5⟩ (.node (.node .empty ⟨5,true,9,0⟩ .empty) ⟨5,true,9,3⟩ .empty)))
def t32_62 : Tree := .node t32_47 ⟨4,true,2,1⟩ t48_62
def t0_62 : Tree := .node t0_31 ⟨3,false,6,0⟩ t32_62
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 0, 2, 3, 7, 0, 4, 5, 0, 6, 0, 0, 0, 0, 8, 9, 1, 0, 10, 0, 0],#[0, 1, 3, 2, 7, 6, 4, 0, 5, 0, 9, 10, 7, 14, 8, 0, 0, 0, 3, 12, 3, 11, 0, 13, 0, 13, 7, 14, 0, 0],
  #[[(false,0)],[(true,0),(true,8)],[(true,1)],[(false,2)],[(true,3)],[(false,4)],[(false,5)],[(true,2)],[(true,7)],[(false,8)],[(true,9)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1),(false,9),(false,10)],[(false,3)],[(false,4)],[(true,2)],[(false,2),(false,6),(false,13)],[(false,7)],[(false,5)],[(true,5)],[(true,10)],[(true,9)],[(true,11),(true,12)],[(true,6),(true,13)]],
  t0_62⟩
theorem check0_15 : t0_15.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check16_31 : t16_31.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node15 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,5,0⟩ = true := by decide
theorem check0_31 : t0_31.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node15 check0_15 check16_31
theorem check32_47 : t32_47.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check48_62 : t48_62.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node47 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,2,1⟩ = true := by decide
theorem check32_62 : t32_62.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node47 check32_47 check48_62
theorem node31 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,6,0⟩ = true := by decide
theorem check0_62 : t0_62.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node31 check0_31 check32_62
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_62
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M017
