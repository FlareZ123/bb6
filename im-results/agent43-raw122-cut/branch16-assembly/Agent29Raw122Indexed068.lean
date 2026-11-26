import IndexedBiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent29Raw122Indexed.M068
open BB6Coverage BB6Coverage.Agent16BiDFA BB6Coverage.Agent16BiDFA.TreeCheck
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,4⟩)
  | _,_ => none
def t0_12 : Tree := (.node (.node (.node (.node .empty ⟨0,false,0,0⟩ .empty) ⟨0,false,0,5⟩ (.node .empty ⟨0,false,0,11⟩ .empty)) ⟨0,false,5,0⟩ (.node (.node .empty ⟨0,false,5,1⟩ .empty) ⟨0,false,5,2⟩ .empty)) ⟨0,false,5,7⟩ (.node (.node (.node .empty ⟨0,false,5,13⟩ .empty) ⟨0,false,5,15⟩ .empty) ⟨0,false,5,16⟩ (.node (.node .empty ⟨0,false,5,18⟩ .empty) ⟨0,false,6,0⟩ .empty)))
def t13_25 : Tree := (.node (.node (.node (.node .empty ⟨0,false,6,11⟩ .empty) ⟨1,false,0,6⟩ (.node .empty ⟨1,false,1,0⟩ .empty)) ⟨1,false,1,4⟩ (.node (.node .empty ⟨1,false,1,10⟩ .empty) ⟨1,false,6,0⟩ .empty)) ⟨1,false,6,6⟩ (.node (.node (.node .empty ⟨1,false,6,12⟩ .empty) ⟨1,false,9,0⟩ .empty) ⟨1,false,9,4⟩ (.node (.node .empty ⟨1,false,9,10⟩ .empty) ⟨1,true,5,0⟩ .empty)))
def t0_25 : Tree := .node t0_12 ⟨0,false,6,5⟩ t13_25
def t26_38 : Tree := (.node (.node (.node (.node .empty ⟨1,true,6,0⟩ .empty) ⟨1,true,6,1⟩ (.node .empty ⟨1,true,6,4⟩ .empty)) ⟨1,true,6,5⟩ (.node (.node .empty ⟨1,true,6,11⟩ .empty) ⟨1,true,6,16⟩ .empty)) ⟨2,false,1,5⟩ (.node (.node (.node .empty ⟨2,false,2,0⟩ .empty) ⟨2,false,9,0⟩ .empty) ⟨2,false,9,3⟩ (.node (.node .empty ⟨2,false,9,5⟩ .empty) ⟨2,false,9,17⟩ .empty)))
def t39_51 : Tree := (.node (.node (.node (.node .empty ⟨2,true,2,9⟩ .empty) ⟨2,true,2,17⟩ (.node .empty ⟨3,false,1,7⟩ .empty)) ⟨3,false,2,1⟩ (.node (.node .empty ⟨3,false,3,0⟩ .empty) ⟨3,false,4,4⟩ .empty)) ⟨3,false,9,1⟩ (.node (.node (.node .empty ⟨3,false,9,2⟩ .empty) ⟨3,false,9,7⟩ .empty) ⟨3,false,9,18⟩ (.node (.node .empty ⟨3,false,10,0⟩ .empty) ⟨3,false,10,1⟩ .empty)))
def t26_51 : Tree := .node t26_38 ⟨2,true,2,3⟩ t39_51
def t0_51 : Tree := .node t0_25 ⟨1,true,5,13⟩ t26_51
def t52_64 : Tree := (.node (.node (.node (.node .empty ⟨3,false,10,16⟩ .empty) ⟨3,true,0,8⟩ (.node .empty ⟨3,true,1,2⟩ .empty)) ⟨3,true,6,2⟩ (.node (.node .empty ⟨3,true,6,8⟩ .empty) ⟨3,true,6,14⟩ .empty)) ⟨3,true,9,2⟩ (.node (.node (.node .empty ⟨4,false,0,4⟩ .empty) ⟨4,false,0,10⟩ .empty) ⟨4,false,7,0⟩ (.node (.node .empty ⟨4,false,7,4⟩ .empty) ⟨4,false,7,10⟩ .empty)))
def t65_77 : Tree := (.node (.node (.node (.node .empty ⟨4,false,8,6⟩ .empty) ⟨4,false,8,12⟩ (.node .empty ⟨4,true,0,4⟩ .empty)) ⟨4,true,1,7⟩ (.node (.node .empty ⟨4,true,1,15⟩ .empty) ⟨4,true,1,16⟩ .empty)) ⟨4,true,2,1⟩ (.node (.node (.node .empty ⟨4,true,2,16⟩ .empty) ⟨4,true,5,4⟩ .empty) ⟨4,true,5,10⟩ (.node (.node .empty ⟨4,true,6,4⟩ .empty) ⟨4,true,7,0⟩ .empty)))
def t52_77 : Tree := .node t52_64 ⟨4,false,8,0⟩ t65_77
def t78_90 : Tree := (.node (.node (.node (.node .empty ⟨4,true,7,5⟩ .empty) ⟨4,true,7,17⟩ (.node .empty ⟨4,true,9,1⟩ .empty)) ⟨4,true,9,2⟩ (.node (.node .empty ⟨4,true,9,7⟩ .empty) ⟨4,true,9,15⟩ .empty)) ⟨4,true,9,16⟩ (.node (.node (.node .empty ⟨4,true,9,18⟩ .empty) ⟨5,false,0,5⟩ .empty) ⟨5,false,6,0⟩ (.node (.node .empty ⟨5,false,6,6⟩ .empty) ⟨5,false,6,12⟩ .empty)))
def t91_102 : Tree := (.node (.node (.node (.node .empty ⟨5,true,0,17⟩ .empty) ⟨5,true,1,3⟩ .empty) ⟨5,true,1,17⟩ (.node (.node .empty ⟨5,true,2,5⟩ .empty) ⟨5,true,2,11⟩ .empty)) ⟨5,true,5,5⟩ (.node (.node (.node .empty ⟨5,true,6,3⟩ .empty) ⟨5,true,6,9⟩ .empty) ⟨5,true,6,17⟩ (.node (.node .empty ⟨5,true,9,3⟩ .empty) ⟨5,true,9,17⟩ .empty)))
def t78_102 : Tree := .node t78_90 ⟨5,true,0,9⟩ t91_102
def t52_102 : Tree := .node t52_77 ⟨4,true,7,3⟩ t78_102
def t0_102 : Tree := .node t0_51 ⟨3,false,10,4⟩ t52_102
def cert : BB6Coverage.Agent1IndexedBiDFA.Cert := ⟨#[0, 1, 4, 2, 3, 5, 0, 0, 0, 0, 8, 6, 7, 9, 0, 0, 0, 0, 10, 2, 0, 0],#[0, 1, 3, 2, 9, 14, 12, 4, 5, 7, 6, 16, 13, 0, 9, 8, 0, 0, 0, 10, 11, 0, 0, 15, 13, 0, 0, 0, 0, 0, 9, 0, 17, 18, 12, 4, 9, 14],
  #[[(false,0)],[(true,0)],[(true,1),(true,9)],[(false,2)],[(false,1)],[(true,2)],[(true,5)],[(false,6)],[(false,5)],[(true,6)],[(false,9)]],
  #[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3),(true,17)],[(false,4)],[(false,5)],[(true,4)],[(true,7)],[(false,2),(false,7),(false,15),(false,18)],[(true,9)],[(false,10)],[(false,3),(false,17)],[(false,6),(false,12)],[(true,2),(true,18)],[(true,11)],[(true,5)],[(false,16)],[(true,16)]],
  t0_102⟩
theorem check0_12 : t0_12.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check13_25 : t13_25.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node12 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨0,false,6,5⟩ = true := by decide
theorem check0_25 : t0_25.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node12 check0_12 check13_25
theorem check26_38 : t26_38.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check39_51 : t39_51.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node38 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨2,true,2,3⟩ = true := by decide
theorem check26_51 : t26_51.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node38 check26_38 check39_51
theorem node25 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨1,true,5,13⟩ = true := by decide
theorem check0_51 : t0_51.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node25 check0_25 check26_51
theorem check52_64 : t52_64.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check65_77 : t65_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node64 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,false,8,0⟩ = true := by decide
theorem check52_77 : t52_77.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node64 check52_64 check65_77
theorem check78_90 : t78_90.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem check91_102 : t91_102.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := by decide
theorem node90 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨5,true,0,9⟩ = true := by decide
theorem check78_102 : t78_102.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node90 check78_90 check91_102
theorem node77 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨4,true,7,3⟩ = true := by decide
theorem check52_102 : t52_102.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node77 check52_77 check78_102
theorem node51 : BB6Coverage.Agent1IndexedBiDFA.stepOK table cert ⟨3,false,10,4⟩ = true := by decide
theorem check0_102 : t0_102.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := Tree.all_node node51 check0_51 check52_102
theorem checked : cert.states.all (BB6Coverage.Agent1IndexedBiDFA.stepOK table cert) = true := check0_102
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6Coverage.Agent1IndexedBiDFA.never table cert (by decide) (by decide) (by decide) checked m hm
#print axioms never
end BB6Coverage.Agent29Raw122Indexed.M068
