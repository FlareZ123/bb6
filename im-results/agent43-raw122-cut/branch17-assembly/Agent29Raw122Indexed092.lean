import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M092
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none
def t0_8 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,4⟩ .empty) ⟨0,false,0,6⟩ (.node .empty ⟨0,false,4,8⟩ .empty)) ⟨0,false,8,0⟩ (.node (.node .empty ⟨0,false,8,4⟩ .empty) ⟨0,false,11,0⟩ (.node .empty ⟨0,false,11,4⟩ .empty)))
def t9_17 : Tree := (.node (.node (.node (.node .empty ⟨0,true,0,8⟩ .empty) ⟨0,true,0,10⟩ .empty) ⟨0,true,4,4⟩ (.node .empty ⟨0,true,4,6⟩ .empty)) ⟨0,true,6,6⟩ (.node (.node .empty ⟨0,true,8,8⟩ .empty) ⟨0,true,11,8⟩ (.node .empty ⟨0,true,11,10⟩ .empty)))
def t0_17 : Tree := .node t0_8 ⟨0,false,11,6⟩ t9_17
def t18_34 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,false,4,1⟩ .empty) ⟨1,false,4,8⟩ .empty) ⟨1,false,4,10⟩ (.node .empty ⟨1,false,6,1⟩ .empty)) ⟨1,false,6,10⟩ (.node (.node .empty ⟨1,false,9,0⟩ .empty) ⟨1,false,11,6⟩ (.node .empty ⟨1,false,12,0⟩ .empty))) ⟨1,true,1,3⟩ (.node (.node (.node .empty ⟨1,true,1,5⟩ .empty) ⟨1,true,1,11⟩ (.node .empty ⟨1,true,4,4⟩ .empty)) ⟨1,true,5,3⟩ (.node (.node .empty ⟨1,true,5,11⟩ .empty) ⟨1,true,9,3⟩ (.node .empty ⟨1,true,9,11⟩ .empty))))
def t0_34 : Tree := .node t0_17 ⟨1,false,1,0⟩ t18_34
def t35_51 : Tree := (.node (.node (.node (.node (.node .empty ⟨1,true,12,3⟩ .empty) ⟨1,true,12,5⟩ .empty) ⟨1,true,12,11⟩ (.node .empty ⟨2,false,2,0⟩ .empty)) ⟨2,true,7,0⟩ (.node (.node .empty ⟨2,true,7,9⟩ .empty) ⟨2,true,10,0⟩ (.node .empty ⟨2,true,10,7⟩ .empty))) ⟨2,true,10,9⟩ (.node (.node (.node .empty ⟨2,true,12,5⟩ .empty) ⟨3,false,2,1⟩ (.node .empty ⟨3,false,3,0⟩ .empty)) ⟨3,true,1,2⟩ (.node (.node .empty ⟨3,true,9,2⟩ .empty) ⟨3,true,12,2⟩ (.node .empty ⟨4,true,2,1⟩ .empty))))
def t52_68 : Tree := (.node (.node (.node (.node (.node .empty ⟨5,false,0,11⟩ .empty) ⟨5,false,1,7⟩ .empty) ⟨5,false,1,9⟩ (.node .empty ⟨5,false,5,7⟩ .empty)) ⟨5,false,7,5⟩ (.node (.node .empty ⟨5,false,9,7⟩ .empty) ⟨5,false,10,5⟩ (.node .empty ⟨5,false,10,11⟩ .empty))) ⟨5,false,12,7⟩ (.node (.node (.node .empty ⟨5,false,12,9⟩ .empty) ⟨5,true,0,4⟩ (.node .empty ⟨5,true,1,3⟩ .empty)) ⟨5,true,8,4⟩ (.node (.node .empty ⟨5,true,9,3⟩ .empty) ⟨5,true,11,4⟩ (.node .empty ⟨5,true,12,3⟩ .empty))))
def t35_68 : Tree := .node t35_51 ⟨5,false,0,5⟩ t52_68
def t0_68 : Tree := .node t0_34 ⟨1,true,10,7⟩ t35_68
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 0, 0, 0, 5, 10, 6, 0, 0, 7, 8, 0, 0, 9, 6, 2, 11, 0, 0, 12, 4, 2],#[0, 1, 3, 2, 0, 0, 0, 4, 9, 5, 0, 6, 7, 0, 0, 8, 5, 0, 0, 10, 11, 0, 0, 4],
  #[[(false,0)],[(true,0)],[(true,1),(true,9),(true,12)],[(false,2)],[(false,1),(false,12)],[(false,4)],[(false,5),(false,9)],[(true,6)],[(false,7)],[(true,8)],[(true,4)],[(false,10)],[(true,11)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3),(true,11)],[(false,8),(true,4)],[(true,5)],[(false,6)],[(true,7)],[(false,4)],[(true,9)],[(false,10)]],
  t0_68⟩
theorem check0_8 : t0_8.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check9_17 : t9_17.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node8 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,11,6⟩ = true := by decide
theorem check0_17 : t0_17.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node8 check0_8 check9_17
theorem check18_34 : t18_34.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node17 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,false,1,0⟩ = true := by decide
theorem check0_34 : t0_34.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node17 check0_17 check18_34
theorem check35_51 : t35_51.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check52_68 : t52_68.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node51 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,false,0,5⟩ = true := by decide
theorem check35_68 : t35_68.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node51 check35_51 check52_68
theorem node34 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,10,7⟩ = true := by decide
theorem check0_68 : t0_68.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node34 check0_34 check35_68
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_68
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M092
