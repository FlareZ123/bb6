import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M069
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
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
def t0_10 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,2,0⟩ .empty) ⟨0,false,2,1⟩ (.node (.node .empty ⟨0,false,2,2⟩ .empty) ⟨0,false,2,4⟩ .empty)) ⟨0,false,2,5⟩ (.node (.node (.node .empty ⟨0,false,2,6⟩ .empty) ⟨0,false,2,11⟩ .empty) ⟨0,false,8,0⟩ (.node .empty ⟨0,false,8,1⟩ .empty)))
def t11_21 : Tree := (.node (.node (.node (.node .empty ⟨0,true,2,0⟩ .empty) ⟨0,true,2,3⟩ .empty) ⟨1,false,0,5⟩ (.node (.node .empty ⟨1,false,1,0⟩ .empty) ⟨1,false,5,0⟩ .empty)) ⟨1,false,5,3⟩ (.node (.node (.node .empty ⟨1,false,7,0⟩ .empty) ⟨1,true,1,0⟩ .empty) ⟨1,true,1,3⟩ (.node .empty ⟨1,true,1,8⟩ .empty)))
def t0_21 : Tree := .node t0_10 ⟨0,false,8,4⟩ t11_21
def t22_32 : Tree := (.node (.node (.node (.node .empty ⟨1,true,5,0⟩ .empty) ⟨1,true,5,1⟩ .empty) ⟨1,true,5,3⟩ (.node (.node .empty ⟨1,true,5,4⟩ .empty) ⟨1,true,5,10⟩ .empty)) ⟨1,true,7,0⟩ (.node (.node (.node .empty ⟨1,true,7,3⟩ .empty) ⟨2,false,1,3⟩ .empty) ⟨2,false,2,0⟩ (.node .empty ⟨2,false,2,1⟩ .empty)))
def t33_43 : Tree := (.node (.node (.node (.node .empty ⟨2,false,8,0⟩ .empty) ⟨3,false,1,2⟩ .empty) ⟨3,false,1,6⟩ (.node (.node .empty ⟨3,false,2,1⟩ .empty) ⟨3,false,3,0⟩ .empty)) ⟨3,false,4,1⟩ (.node (.node (.node .empty ⟨3,false,4,4⟩ .empty) ⟨3,false,8,1⟩ .empty) ⟨3,false,9,0⟩ (.node .empty ⟨3,true,0,7⟩ .empty)))
def t22_43 : Tree := .node t22_32 ⟨2,false,2,4⟩ t33_43
def t0_43 : Tree := .node t0_21 ⟨1,true,1,10⟩ t22_43
def t44_54 : Tree := (.node (.node (.node (.node .empty ⟨3,true,3,0⟩ .empty) ⟨3,true,3,3⟩ .empty) ⟨3,true,5,2⟩ (.node (.node .empty ⟨3,true,7,2⟩ .empty) ⟨4,false,0,1⟩ .empty)) ⟨4,false,0,4⟩ (.node (.node (.node .empty ⟨4,false,0,9⟩ .empty) ⟨4,false,0,11⟩ .empty) ⟨4,false,2,4⟩ (.node .empty ⟨4,false,6,0⟩ .empty)))
def t55_65 : Tree := (.node (.node (.node (.node .empty ⟨4,false,6,4⟩ .empty) ⟨4,true,0,4⟩ .empty) ⟨4,true,1,0⟩ (.node (.node .empty ⟨4,true,1,1⟩ .empty) ⟨4,true,1,2⟩ .empty)) ⟨4,true,1,4⟩ (.node (.node (.node .empty ⟨4,true,1,5⟩ .empty) ⟨4,true,1,6⟩ .empty) ⟨4,true,1,11⟩ (.node .empty ⟨4,true,2,1⟩ .empty)))
def t44_65 : Tree := .node t44_54 ⟨4,false,6,1⟩ t55_65
def t66_76 : Tree := (.node (.node (.node (.node .empty ⟨4,true,5,0⟩ .empty) ⟨4,true,5,1⟩ .empty) ⟨4,true,5,4⟩ (.node (.node .empty ⟨4,true,5,5⟩ .empty) ⟨4,true,5,11⟩ .empty)) ⟨4,true,6,4⟩ (.node (.node (.node .empty ⟨4,true,8,1⟩ .empty) ⟨4,true,8,4⟩ .empty) ⟨5,false,0,3⟩ (.node .empty ⟨5,true,0,0⟩ .empty)))
def t77_86 : Tree := (.node (.node (.node (.node .empty ⟨5,true,0,8⟩ .empty) ⟨5,true,0,10⟩ .empty) ⟨5,true,1,3⟩ (.node .empty ⟨5,true,2,0⟩ .empty)) ⟨5,true,2,3⟩ (.node (.node (.node .empty ⟨5,true,2,10⟩ .empty) ⟨5,true,3,3⟩ .empty) ⟨5,true,5,3⟩ (.node .empty ⟨5,true,7,3⟩ .empty)))
def t66_86 : Tree := .node t66_76 ⟨5,true,0,3⟩ t77_86
def t44_86 : Tree := .node t44_65 ⟨4,true,2,4⟩ t66_86
def t0_86 : Tree := .node t0_43 ⟨3,true,1,2⟩ t44_86
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 5, 0, 6, 0, 0, 0, 2, 0, 7, 0, 8, 9, 7, 0, 0],#[0, 1, 3, 2, 8, 7, 5, 4, 3, 6, 10, 0, 8, 7, 0, 0, 0, 9, 0, 0, 0, 11, 10, 0],
  #[[(false,0)],[(true,0)],[(true,1),(true,5)],[(false,2)],[(false,1)],[(true,2)],[(true,3)],[(true,6),(true,8)],[(true,7)],[(false,8)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1),(false,4)],[(true,3)],[(false,3)],[(true,4)],[(true,2),(true,6)],[(false,2),(false,6)],[(true,8)],[(false,5),(false,11)],[(true,10)]],
  t0_86⟩
theorem check0_10 : t0_10.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check11_21 : t11_21.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node10 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,8,4⟩ = true := by decide
theorem check0_21 : t0_21.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node10 check0_10 check11_21
theorem check22_32 : t22_32.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check33_43 : t33_43.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node32 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,false,2,4⟩ = true := by decide
theorem check22_43 : t22_43.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node32 check22_32 check33_43
theorem node21 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,1,10⟩ = true := by decide
theorem check0_43 : t0_43.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node21 check0_21 check22_43
theorem check44_54 : t44_54.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check55_65 : t55_65.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node54 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,6,1⟩ = true := by decide
theorem check44_65 : t44_65.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node54 check44_54 check55_65
theorem check66_76 : t66_76.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check77_86 : t77_86.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node76 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,0,3⟩ = true := by decide
theorem check66_86 : t66_86.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node76 check66_76 check77_86
theorem node65 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,2,4⟩ = true := by decide
theorem check44_86 : t44_86.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node65 check44_65 check66_86
theorem node43 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,true,1,2⟩ = true := by decide
theorem check0_86 : t0_86.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node43 check0_43 check44_86
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_86
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M069
