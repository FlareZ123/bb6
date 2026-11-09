import QNodesB
import AffineParamRoot
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace BB6.Agent28Affine4096
open BB6.Agent13AdaptiveParam

/-- Exact root lifting for any affine shadow graph. -/
theorem root_mem (c q P k : Nat)
    (nodes : List (Nat×Nat×Nat×Nat))
    (hroot : (0,c*q+4,c*P,k) ∈ nodes) (r : Nat) :
    (0,c*(q+P*r)+4) ∈ BB6.Agent9Adaptive.decode r nodes := by
  apply List.mem_map.mpr
  refine ⟨(0,c*q+4,c*P,k), hroot, ?_⟩
  change (0,c*q+4+(c*P)*r)=(0,c*(q+P*r)+4)
  simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Authentic P1 critical gateway is excluded on q=109+4096*r. -/
theorem q109_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(109+P4096*r)+2)-2*(16*(109+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 109 P4096 (by decide) (by decide)
    q109nodes0 q109nodes1 q109check0 q109check1
    (root_mem 12 109 P4096 6 q109nodes0 (by decide))
    (root_mem 10 109 P4096 2 q109nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=165+4096*r. -/
theorem q165_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(165+P4096*r)+2)-2*(16*(165+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 165 P4096 (by decide) (by decide)
    q165nodes0 q165nodes1 q165check0 q165check1
    (root_mem 12 165 P4096 7 q165nodes0 (by decide))
    (root_mem 10 165 P4096 2 q165nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=225+4096*r. -/
theorem q225_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(225+P4096*r)+2)-2*(16*(225+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 225 P4096 (by decide) (by decide)
    q225nodes0 q225nodes1 q225check0 q225check1
    (root_mem 12 225 P4096 5 q225nodes0 (by decide))
    (root_mem 10 225 P4096 2 q225nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=253+4096*r. -/
theorem q253_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(253+P4096*r)+2)-2*(16*(253+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 253 P4096 (by decide) (by decide)
    q253nodes0 q253nodes1 q253check0 q253check1
    (root_mem 12 253 P4096 6 q253nodes0 (by decide))
    (root_mem 10 253 P4096 2 q253nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=397+4096*r. -/
theorem q397_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(397+P4096*r)+2)-2*(16*(397+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 397 P4096 (by decide) (by decide)
    q397nodes0 q397nodes1 q397check0 q397check1
    (root_mem 12 397 P4096 6 q397nodes0 (by decide))
    (root_mem 10 397 P4096 2 q397nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=409+4096*r. -/
theorem q409_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(409+P4096*r)+2)-2*(16*(409+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 409 P4096 (by decide) (by decide)
    q409nodes0 q409nodes1 q409check0 q409check1
    (root_mem 12 409 P4096 5 q409nodes0 (by decide))
    (root_mem 10 409 P4096 2 q409nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=413+4096*r. -/
theorem q413_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(413+P4096*r)+2)-2*(16*(413+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 413 P4096 (by decide) (by decide)
    q413nodes0 q413nodes1 q413check0 q413check1
    (root_mem 12 413 P4096 6 q413nodes0 (by decide))
    (root_mem 10 413 P4096 2 q413nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=433+4096*r. -/
theorem q433_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(433+P4096*r)+2)-2*(16*(433+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 433 P4096 (by decide) (by decide)
    q433nodes0 q433nodes1 q433check0 q433check1
    (root_mem 12 433 P4096 5 q433nodes0 (by decide))
    (root_mem 10 433 P4096 2 q433nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=533+4096*r. -/
theorem q533_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(533+P4096*r)+2)-2*(16*(533+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 533 P4096 (by decide) (by decide)
    q533nodes0 q533nodes1 q533check0 q533check1
    (root_mem 12 533 P4096 9 q533nodes0 (by decide))
    (root_mem 10 533 P4096 2 q533nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=629+4096*r. -/
theorem q629_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(629+P4096*r)+2)-2*(16*(629+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 629 P4096 (by decide) (by decide)
    q629nodes0 q629nodes1 q629check0 q629check1
    (root_mem 12 629 P4096 8 q629nodes0 (by decide))
    (root_mem 10 629 P4096 2 q629nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=681+4096*r. -/
theorem q681_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(681+P4096*r)+2)-2*(16*(681+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 681 P4096 (by decide) (by decide)
    q681nodes0 q681nodes1 q681check0 q681check1
    (root_mem 12 681 P4096 5 q681nodes0 (by decide))
    (root_mem 10 681 P4096 2 q681nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=737+4096*r. -/
theorem q737_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(737+P4096*r)+2)-2*(16*(737+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 737 P4096 (by decide) (by decide)
    q737nodes0 q737nodes1 q737check0 q737check1
    (root_mem 12 737 P4096 5 q737nodes0 (by decide))
    (root_mem 10 737 P4096 2 q737nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=793+4096*r. -/
theorem q793_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(793+P4096*r)+2)-2*(16*(793+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 793 P4096 (by decide) (by decide)
    q793nodes0 q793nodes1 q793check0 q793check1
    (root_mem 12 793 P4096 5 q793nodes0 (by decide))
    (root_mem 10 793 P4096 2 q793nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=821+4096*r. -/
theorem q821_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(821+P4096*r)+2)-2*(16*(821+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 821 P4096 (by decide) (by decide)
    q821nodes0 q821nodes1 q821check0 q821check1
    (root_mem 12 821 P4096 8 q821nodes0 (by decide))
    (root_mem 10 821 P4096 2 q821nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=865+4096*r. -/
theorem q865_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(865+P4096*r)+2)-2*(16*(865+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 865 P4096 (by decide) (by decide)
    q865nodes0 q865nodes1 q865check0 q865check1
    (root_mem 12 865 P4096 5 q865nodes0 (by decide))
    (root_mem 10 865 P4096 2 q865nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=877+4096*r. -/
theorem q877_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(877+P4096*r)+2)-2*(16*(877+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 877 P4096 (by decide) (by decide)
    q877nodes0 q877nodes1 q877check0 q877check1
    (root_mem 12 877 P4096 6 q877nodes0 (by decide))
    (root_mem 10 877 P4096 2 q877nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=993+4096*r. -/
theorem q993_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(993+P4096*r)+2)-2*(16*(993+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 993 P4096 (by decide) (by decide)
    q993nodes0 q993nodes1 q993check0 q993check1
    (root_mem 12 993 P4096 5 q993nodes0 (by decide))
    (root_mem 10 993 P4096 2 q993nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1013+4096*r. -/
theorem q1013_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1013+P4096*r)+2)-2*(16*(1013+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1013 P4096 (by decide) (by decide)
    q1013nodes0 q1013nodes1 q1013check0 q1013check1
    (root_mem 12 1013 P4096 8 q1013nodes0 (by decide))
    (root_mem 10 1013 P4096 2 q1013nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1017+4096*r. -/
theorem q1017_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1017+P4096*r)+2)-2*(16*(1017+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1017 P4096 (by decide) (by decide)
    q1017nodes0 q1017nodes1 q1017check0 q1017check1
    (root_mem 12 1017 P4096 5 q1017nodes0 (by decide))
    (root_mem 10 1017 P4096 2 q1017nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1021+4096*r. -/
theorem q1021_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1021+P4096*r)+2)-2*(16*(1021+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1021 P4096 (by decide) (by decide)
    q1021nodes0 q1021nodes1 q1021check0 q1021check1
    (root_mem 12 1021 P4096 6 q1021nodes0 (by decide))
    (root_mem 10 1021 P4096 2 q1021nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1065+4096*r. -/
theorem q1065_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1065+P4096*r)+2)-2*(16*(1065+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1065 P4096 (by decide) (by decide)
    q1065nodes0 q1065nodes1 q1065check0 q1065check1
    (root_mem 12 1065 P4096 5 q1065nodes0 (by decide))
    (root_mem 10 1065 P4096 2 q1065nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1073+4096*r. -/
theorem q1073_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1073+P4096*r)+2)-2*(16*(1073+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1073 P4096 (by decide) (by decide)
    q1073nodes0 q1073nodes1 q1073check0 q1073check1
    (root_mem 12 1073 P4096 5 q1073nodes0 (by decide))
    (root_mem 10 1073 P4096 2 q1073nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1109+4096*r. -/
theorem q1109_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1109+P4096*r)+2)-2*(16*(1109+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1109 P4096 (by decide) (by decide)
    q1109nodes0 q1109nodes1 q1109check0 q1109check1
    (root_mem 12 1109 P4096 11 q1109nodes0 (by decide))
    (root_mem 10 1109 P4096 2 q1109nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1137+4096*r. -/
theorem q1137_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1137+P4096*r)+2)-2*(16*(1137+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1137 P4096 (by decide) (by decide)
    q1137nodes0 q1137nodes1 q1137check0 q1137check1
    (root_mem 12 1137 P4096 5 q1137nodes0 (by decide))
    (root_mem 10 1137 P4096 2 q1137nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1181+4096*r. -/
theorem q1181_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1181+P4096*r)+2)-2*(16*(1181+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1181 P4096 (by decide) (by decide)
    q1181nodes0 q1181nodes1 q1181check0 q1181check1
    (root_mem 12 1181 P4096 6 q1181nodes0 (by decide))
    (root_mem 10 1181 P4096 2 q1181nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1201+4096*r. -/
theorem q1201_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1201+P4096*r)+2)-2*(16*(1201+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1201 P4096 (by decide) (by decide)
    q1201nodes0 q1201nodes1 q1201check0 q1201check1
    (root_mem 12 1201 P4096 5 q1201nodes0 (by decide))
    (root_mem 10 1201 P4096 2 q1201nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1233+4096*r. -/
theorem q1233_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1233+P4096*r)+2)-2*(16*(1233+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1233 P4096 (by decide) (by decide)
    q1233nodes0 q1233nodes1 q1233check0 q1233check1
    (root_mem 12 1233 P4096 5 q1233nodes0 (by decide))
    (root_mem 10 1233 P4096 2 q1233nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1285+4096*r. -/
theorem q1285_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1285+P4096*r)+2)-2*(16*(1285+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1285 P4096 (by decide) (by decide)
    q1285nodes0 q1285nodes1 q1285check0 q1285check1
    (root_mem 12 1285 P4096 7 q1285nodes0 (by decide))
    (root_mem 10 1285 P4096 2 q1285nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1401+4096*r. -/
theorem q1401_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1401+P4096*r)+2)-2*(16*(1401+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1401 P4096 (by decide) (by decide)
    q1401nodes0 q1401nodes1 q1401check0 q1401check1
    (root_mem 12 1401 P4096 5 q1401nodes0 (by decide))
    (root_mem 10 1401 P4096 2 q1401nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1505+4096*r. -/
theorem q1505_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1505+P4096*r)+2)-2*(16*(1505+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1505 P4096 (by decide) (by decide)
    q1505nodes0 q1505nodes1 q1505check0 q1505check1
    (root_mem 12 1505 P4096 5 q1505nodes0 (by decide))
    (root_mem 10 1505 P4096 2 q1505nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1517+4096*r. -/
theorem q1517_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1517+P4096*r)+2)-2*(16*(1517+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1517 P4096 (by decide) (by decide)
    q1517nodes0 q1517nodes1 q1517check0 q1517check1
    (root_mem 12 1517 P4096 6 q1517nodes0 (by decide))
    (root_mem 10 1517 P4096 2 q1517nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1633+4096*r. -/
theorem q1633_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1633+P4096*r)+2)-2*(16*(1633+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1633 P4096 (by decide) (by decide)
    q1633nodes0 q1633nodes1 q1633check0 q1633check1
    (root_mem 12 1633 P4096 5 q1633nodes0 (by decide))
    (root_mem 10 1633 P4096 2 q1633nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1661+4096*r. -/
theorem q1661_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1661+P4096*r)+2)-2*(16*(1661+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1661 P4096 (by decide) (by decide)
    q1661nodes0 q1661nodes1 q1661check0 q1661check1
    (root_mem 12 1661 P4096 6 q1661nodes0 (by decide))
    (root_mem 10 1661 P4096 2 q1661nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1689+4096*r. -/
theorem q1689_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1689+P4096*r)+2)-2*(16*(1689+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1689 P4096 (by decide) (by decide)
    q1689nodes0 q1689nodes1 q1689check0 q1689check1
    (root_mem 12 1689 P4096 5 q1689nodes0 (by decide))
    (root_mem 10 1689 P4096 2 q1689nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1765+4096*r. -/
theorem q1765_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1765+P4096*r)+2)-2*(16*(1765+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1765 P4096 (by decide) (by decide)
    q1765nodes0 q1765nodes1 q1765check0 q1765check1
    (root_mem 12 1765 P4096 7 q1765nodes0 (by decide))
    (root_mem 10 1765 P4096 2 q1765nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1777+4096*r. -/
theorem q1777_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1777+P4096*r)+2)-2*(16*(1777+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1777 P4096 (by decide) (by decide)
    q1777nodes0 q1777nodes1 q1777check0 q1777check1
    (root_mem 12 1777 P4096 5 q1777nodes0 (by decide))
    (root_mem 10 1777 P4096 2 q1777nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1821+4096*r. -/
theorem q1821_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1821+P4096*r)+2)-2*(16*(1821+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1821 P4096 (by decide) (by decide)
    q1821nodes0 q1821nodes1 q1821check0 q1821check1
    (root_mem 12 1821 P4096 6 q1821nodes0 (by decide))
    (root_mem 10 1821 P4096 2 q1821nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1841+4096*r. -/
theorem q1841_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1841+P4096*r)+2)-2*(16*(1841+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1841 P4096 (by decide) (by decide)
    q1841nodes0 q1841nodes1 q1841check0 q1841check1
    (root_mem 12 1841 P4096 5 q1841nodes0 (by decide))
    (root_mem 10 1841 P4096 2 q1841nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1857+4096*r. -/
theorem q1857_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1857+P4096*r)+2)-2*(16*(1857+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1857 P4096 (by decide) (by decide)
    q1857nodes0 q1857nodes1 q1857check0 q1857check1
    (root_mem 12 1857 P4096 5 q1857nodes0 (by decide))
    (root_mem 10 1857 P4096 2 q1857nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1905+4096*r. -/
theorem q1905_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1905+P4096*r)+2)-2*(16*(1905+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1905 P4096 (by decide) (by decide)
    q1905nodes0 q1905nodes1 q1905check0 q1905check1
    (root_mem 12 1905 P4096 5 q1905nodes0 (by decide))
    (root_mem 10 1905 P4096 2 q1905nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=1985+4096*r. -/
theorem q1985_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(1985+P4096*r)+2)-2*(16*(1985+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 1985 P4096 (by decide) (by decide)
    q1985nodes0 q1985nodes1 q1985check0 q1985check1
    (root_mem 12 1985 P4096 5 q1985nodes0 (by decide))
    (root_mem 10 1985 P4096 2 q1985nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2057+4096*r. -/
theorem q2057_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2057+P4096*r)+2)-2*(16*(2057+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2057 P4096 (by decide) (by decide)
    q2057nodes0 q2057nodes1 q2057check0 q2057check1
    (root_mem 12 2057 P4096 5 q2057nodes0 (by decide))
    (root_mem 10 2057 P4096 2 q2057nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2073+4096*r. -/
theorem q2073_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2073+P4096*r)+2)-2*(16*(2073+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2073 P4096 (by decide) (by decide)
    q2073nodes0 q2073nodes1 q2073check0 q2073check1
    (root_mem 12 2073 P4096 5 q2073nodes0 (by decide))
    (root_mem 10 2073 P4096 2 q2073nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2101+4096*r. -/
theorem q2101_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2101+P4096*r)+2)-2*(16*(2101+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2101 P4096 (by decide) (by decide)
    q2101nodes0 q2101nodes1 q2101check0 q2101check1
    (root_mem 12 2101 P4096 8 q2101nodes0 (by decide))
    (root_mem 10 2101 P4096 2 q2101nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2193+4096*r. -/
theorem q2193_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2193+P4096*r)+2)-2*(16*(2193+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2193 P4096 (by decide) (by decide)
    q2193nodes0 q2193nodes1 q2193check0 q2193check1
    (root_mem 12 2193 P4096 5 q2193nodes0 (by decide))
    (root_mem 10 2193 P4096 2 q2193nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2285+4096*r. -/
theorem q2285_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2285+P4096*r)+2)-2*(16*(2285+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2285 P4096 (by decide) (by decide)
    q2285nodes0 q2285nodes1 q2285check0 q2285check1
    (root_mem 12 2285 P4096 6 q2285nodes0 (by decide))
    (root_mem 10 2285 P4096 2 q2285nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2293+4096*r. -/
theorem q2293_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2293+P4096*r)+2)-2*(16*(2293+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2293 P4096 (by decide) (by decide)
    q2293nodes0 q2293nodes1 q2293check0 q2293check1
    (root_mem 12 2293 P4096 8 q2293nodes0 (by decide))
    (root_mem 10 2293 P4096 2 q2293nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2297+4096*r. -/
theorem q2297_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2297+P4096*r)+2)-2*(16*(2297+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2297 P4096 (by decide) (by decide)
    q2297nodes0 q2297nodes1 q2297check0 q2297check1
    (root_mem 12 2297 P4096 5 q2297nodes0 (by decide))
    (root_mem 10 2297 P4096 2 q2297nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2317+4096*r. -/
theorem q2317_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2317+P4096*r)+2)-2*(16*(2317+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2317 P4096 (by decide) (by decide)
    q2317nodes0 q2317nodes1 q2317check0 q2317check1
    (root_mem 12 2317 P4096 6 q2317nodes0 (by decide))
    (root_mem 10 2317 P4096 2 q2317nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2353+4096*r. -/
theorem q2353_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2353+P4096*r)+2)-2*(16*(2353+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2353 P4096 (by decide) (by decide)
    q2353nodes0 q2353nodes1 q2353check0 q2353check1
    (root_mem 12 2353 P4096 5 q2353nodes0 (by decide))
    (root_mem 10 2353 P4096 2 q2353nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2373+4096*r. -/
theorem q2373_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2373+P4096*r)+2)-2*(16*(2373+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2373 P4096 (by decide) (by decide)
    q2373nodes0 q2373nodes1 q2373check0 q2373check1
    (root_mem 12 2373 P4096 7 q2373nodes0 (by decide))
    (root_mem 10 2373 P4096 2 q2373nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2429+4096*r. -/
theorem q2429_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2429+P4096*r)+2)-2*(16*(2429+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2429 P4096 (by decide) (by decide)
    q2429nodes0 q2429nodes1 q2429check0 q2429check1
    (root_mem 12 2429 P4096 6 q2429nodes0 (by decide))
    (root_mem 10 2429 P4096 2 q2429nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2441+4096*r. -/
theorem q2441_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2441+P4096*r)+2)-2*(16*(2441+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2441 P4096 (by decide) (by decide)
    q2441nodes0 q2441nodes1 q2441check0 q2441check1
    (root_mem 12 2441 P4096 5 q2441nodes0 (by decide))
    (root_mem 10 2441 P4096 2 q2441nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2453+4096*r. -/
theorem q2453_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2453+P4096*r)+2)-2*(16*(2453+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2453 P4096 (by decide) (by decide)
    q2453nodes0 q2453nodes1 q2453check0 q2453check1
    (root_mem 12 2453 P4096 9 q2453nodes0 (by decide))
    (root_mem 10 2453 P4096 2 q2453nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2465+4096*r. -/
theorem q2465_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2465+P4096*r)+2)-2*(16*(2465+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2465 P4096 (by decide) (by decide)
    q2465nodes0 q2465nodes1 q2465check0 q2465check1
    (root_mem 12 2465 P4096 5 q2465nodes0 (by decide))
    (root_mem 10 2465 P4096 2 q2465nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2485+4096*r. -/
theorem q2485_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2485+P4096*r)+2)-2*(16*(2485+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2485 P4096 (by decide) (by decide)
    q2485nodes0 q2485nodes1 q2485check0 q2485check1
    (root_mem 12 2485 P4096 8 q2485nodes0 (by decide))
    (root_mem 10 2485 P4096 2 q2485nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2545+4096*r. -/
theorem q2545_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2545+P4096*r)+2)-2*(16*(2545+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2545 P4096 (by decide) (by decide)
    q2545nodes0 q2545nodes1 q2545check0 q2545check1
    (root_mem 12 2545 P4096 5 q2545nodes0 (by decide))
    (root_mem 10 2545 P4096 2 q2545nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2577+4096*r. -/
theorem q2577_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2577+P4096*r)+2)-2*(16*(2577+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2577 P4096 (by decide) (by decide)
    q2577nodes0 q2577nodes1 q2577check0 q2577check1
    (root_mem 12 2577 P4096 5 q2577nodes0 (by decide))
    (root_mem 10 2577 P4096 2 q2577nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2589+4096*r. -/
theorem q2589_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2589+P4096*r)+2)-2*(16*(2589+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2589 P4096 (by decide) (by decide)
    q2589nodes0 q2589nodes1 q2589check0 q2589check1
    (root_mem 12 2589 P4096 6 q2589nodes0 (by decide))
    (root_mem 10 2589 P4096 2 q2589nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2613+4096*r. -/
theorem q2613_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2613+P4096*r)+2)-2*(16*(2613+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2613 P4096 (by decide) (by decide)
    q2613nodes0 q2613nodes1 q2613check0 q2613check1
    (root_mem 12 2613 P4096 8 q2613nodes0 (by decide))
    (root_mem 10 2613 P4096 2 q2613nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2681+4096*r. -/
theorem q2681_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2681+P4096*r)+2)-2*(16*(2681+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2681 P4096 (by decide) (by decide)
    q2681nodes0 q2681nodes1 q2681check0 q2681check1
    (root_mem 12 2681 P4096 5 q2681nodes0 (by decide))
    (root_mem 10 2681 P4096 2 q2681nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2769+4096*r. -/
theorem q2769_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2769+P4096*r)+2)-2*(16*(2769+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2769 P4096 (by decide) (by decide)
    q2769nodes0 q2769nodes1 q2769check0 q2769check1
    (root_mem 12 2769 P4096 5 q2769nodes0 (by decide))
    (root_mem 10 2769 P4096 2 q2769nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=2917+4096*r. -/
theorem q2917_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(2917+P4096*r)+2)-2*(16*(2917+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 2917 P4096 (by decide) (by decide)
    q2917nodes0 q2917nodes1 q2917check0 q2917check1
    (root_mem 12 2917 P4096 7 q2917nodes0 (by decide))
    (root_mem 10 2917 P4096 2 q2917nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=3029+4096*r. -/
theorem q3029_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(3029+P4096*r)+2)-2*(16*(3029+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 3029 P4096 (by decide) (by decide)
    q3029nodes0 q3029nodes1 q3029check0 q3029check1
    (root_mem 12 3029 P4096 10 q3029nodes0 (by decide))
    (root_mem 10 3029 P4096 2 q3029nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=3085+4096*r. -/
theorem q3085_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(3085+P4096*r)+2)-2*(16*(3085+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 3085 P4096 (by decide) (by decide)
    q3085nodes0 q3085nodes1 q3085check0 q3085check1
    (root_mem 12 3085 P4096 6 q3085nodes0 (by decide))
    (root_mem 10 3085 P4096 2 q3085nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=3137+4096*r. -/
theorem q3137_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(3137+P4096*r)+2)-2*(16*(3137+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 3137 P4096 (by decide) (by decide)
    q3137nodes0 q3137nodes1 q3137check0 q3137check1
    (root_mem 12 3137 P4096 5 q3137nodes0 (by decide))
    (root_mem 10 3137 P4096 2 q3137nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=3221+4096*r. -/
theorem q3221_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(3221+P4096*r)+2)-2*(16*(3221+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 3221 P4096 (by decide) (by decide)
    q3221nodes0 q3221nodes1 q3221check0 q3221check1
    (root_mem 12 3221 P4096 9 q3221nodes0 (by decide))
    (root_mem 10 3221 P4096 2 q3221nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=3337+4096*r. -/
theorem q3337_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(3337+P4096*r)+2)-2*(16*(3337+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 3337 P4096 (by decide) (by decide)
    q3337nodes0 q3337nodes1 q3337check0 q3337check1
    (root_mem 12 3337 P4096 5 q3337nodes0 (by decide))
    (root_mem 10 3337 P4096 2 q3337nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=3381+4096*r. -/
theorem q3381_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(3381+P4096*r)+2)-2*(16*(3381+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 3381 P4096 (by decide) (by decide)
    q3381nodes0 q3381nodes1 q3381check0 q3381check1
    (root_mem 12 3381 P4096 8 q3381nodes0 (by decide))
    (root_mem 10 3381 P4096 2 q3381nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=3429+4096*r. -/
theorem q3429_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(3429+P4096*r)+2)-2*(16*(3429+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 3429 P4096 (by decide) (by decide)
    q3429nodes0 q3429nodes1 q3429check0 q3429check1
    (root_mem 12 3429 P4096 7 q3429nodes0 (by decide))
    (root_mem 10 3429 P4096 2 q3429nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=3493+4096*r. -/
theorem q3493_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(3493+P4096*r)+2)-2*(16*(3493+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 3493 P4096 (by decide) (by decide)
    q3493nodes0 q3493nodes1 q3493check0 q3493check1
    (root_mem 12 3493 P4096 7 q3493nodes0 (by decide))
    (root_mem 10 3493 P4096 2 q3493nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=3497+4096*r. -/
theorem q3497_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(3497+P4096*r)+2)-2*(16*(3497+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 3497 P4096 (by decide) (by decide)
    q3497nodes0 q3497nodes1 q3497check0 q3497check1
    (root_mem 12 3497 P4096 5 q3497nodes0 (by decide))
    (root_mem 10 3497 P4096 2 q3497nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=3521+4096*r. -/
theorem q3521_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(3521+P4096*r)+2)-2*(16*(3521+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 3521 P4096 (by decide) (by decide)
    q3521nodes0 q3521nodes1 q3521check0 q3521check1
    (root_mem 12 3521 P4096 5 q3521nodes0 (by decide))
    (root_mem 10 3521 P4096 2 q3521nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=3541+4096*r. -/
theorem q3541_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(3541+P4096*r)+2)-2*(16*(3541+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 3541 P4096 (by decide) (by decide)
    q3541nodes0 q3541nodes1 q3541check0 q3541check1
    (root_mem 12 3541 P4096 10 q3541nodes0 (by decide))
    (root_mem 10 3541 P4096 2 q3541nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=3633+4096*r. -/
theorem q3633_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(3633+P4096*r)+2)-2*(16*(3633+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 3633 P4096 (by decide) (by decide)
    q3633nodes0 q3633nodes1 q3633check0 q3633check1
    (root_mem 12 3633 P4096 5 q3633nodes0 (by decide))
    (root_mem 10 3633 P4096 2 q3633nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=3721+4096*r. -/
theorem q3721_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(3721+P4096*r)+2)-2*(16*(3721+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 3721 P4096 (by decide) (by decide)
    q3721nodes0 q3721nodes1 q3721check0 q3721check1
    (root_mem 12 3721 P4096 5 q3721nodes0 (by decide))
    (root_mem 10 3721 P4096 2 q3721nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=3725+4096*r. -/
theorem q3725_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(3725+P4096*r)+2)-2*(16*(3725+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 3725 P4096 (by decide) (by decide)
    q3725nodes0 q3725nodes1 q3725check0 q3725check1
    (root_mem 12 3725 P4096 6 q3725nodes0 (by decide))
    (root_mem 10 3725 P4096 2 q3725nodes1 (by decide)) r

/-- Authentic P1 critical gateway is excluded on q=3881+4096*r. -/
theorem q3881_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(3881+P4096*r)+2)-2*(16*(3881+P4096*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 13 3881 P4096 (by decide) (by decide)
    q3881nodes0 q3881nodes1 q3881check0 q3881check1
    (root_mem 12 3881 P4096 5 q3881nodes0 (by decide))
    (root_mem 10 3881 P4096 2 q3881nodes1 (by decide)) r

/-- Seventy-eight distinct residue classes, all formerly outside the 701/1024 certificate. -/
def newQ : List Nat := [109,165,225,253,397,409,413,433,533,629,681,737,793,821,865,877,993,1013,1017,1021,1065,1073,1109,1137,1181,1201,1233,1285,1401,1505,1517,1633,1661,1689,1765,1777,1821,1841,1857,1905,1985,2057,2073,2101,2193,2285,2293,2297,2317,2353,2373,2429,2441,2453,2465,2485,2545,2577,2589,2613,2681,2769,2917,3029,3085,3137,3221,3337,3381,3429,3493,3497,3521,3541,3633,3721,3725,3881]

theorem newQ_unreachable (q r : Nat) (hq : q ∈ newQ) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(q+P4096*r)+2)-2*(16*(q+P4096*r)+2)-10) := by
  simp only [newQ, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst q
    exact q109_unreachable r
  · subst q
    exact q165_unreachable r
  · subst q
    exact q225_unreachable r
  · subst q
    exact q253_unreachable r
  · subst q
    exact q397_unreachable r
  · subst q
    exact q409_unreachable r
  · subst q
    exact q413_unreachable r
  · subst q
    exact q433_unreachable r
  · subst q
    exact q533_unreachable r
  · subst q
    exact q629_unreachable r
  · subst q
    exact q681_unreachable r
  · subst q
    exact q737_unreachable r
  · subst q
    exact q793_unreachable r
  · subst q
    exact q821_unreachable r
  · subst q
    exact q865_unreachable r
  · subst q
    exact q877_unreachable r
  · subst q
    exact q993_unreachable r
  · subst q
    exact q1013_unreachable r
  · subst q
    exact q1017_unreachable r
  · subst q
    exact q1021_unreachable r
  · subst q
    exact q1065_unreachable r
  · subst q
    exact q1073_unreachable r
  · subst q
    exact q1109_unreachable r
  · subst q
    exact q1137_unreachable r
  · subst q
    exact q1181_unreachable r
  · subst q
    exact q1201_unreachable r
  · subst q
    exact q1233_unreachable r
  · subst q
    exact q1285_unreachable r
  · subst q
    exact q1401_unreachable r
  · subst q
    exact q1505_unreachable r
  · subst q
    exact q1517_unreachable r
  · subst q
    exact q1633_unreachable r
  · subst q
    exact q1661_unreachable r
  · subst q
    exact q1689_unreachable r
  · subst q
    exact q1765_unreachable r
  · subst q
    exact q1777_unreachable r
  · subst q
    exact q1821_unreachable r
  · subst q
    exact q1841_unreachable r
  · subst q
    exact q1857_unreachable r
  · subst q
    exact q1905_unreachable r
  · subst q
    exact q1985_unreachable r
  · subst q
    exact q2057_unreachable r
  · subst q
    exact q2073_unreachable r
  · subst q
    exact q2101_unreachable r
  · subst q
    exact q2193_unreachable r
  · subst q
    exact q2285_unreachable r
  · subst q
    exact q2293_unreachable r
  · subst q
    exact q2297_unreachable r
  · subst q
    exact q2317_unreachable r
  · subst q
    exact q2353_unreachable r
  · subst q
    exact q2373_unreachable r
  · subst q
    exact q2429_unreachable r
  · subst q
    exact q2441_unreachable r
  · subst q
    exact q2453_unreachable r
  · subst q
    exact q2465_unreachable r
  · subst q
    exact q2485_unreachable r
  · subst q
    exact q2545_unreachable r
  · subst q
    exact q2577_unreachable r
  · subst q
    exact q2589_unreachable r
  · subst q
    exact q2613_unreachable r
  · subst q
    exact q2681_unreachable r
  · subst q
    exact q2769_unreachable r
  · subst q
    exact q2917_unreachable r
  · subst q
    exact q3029_unreachable r
  · subst q
    exact q3085_unreachable r
  · subst q
    exact q3137_unreachable r
  · subst q
    exact q3221_unreachable r
  · subst q
    exact q3337_unreachable r
  · subst q
    exact q3381_unreachable r
  · subst q
    exact q3429_unreachable r
  · subst q
    exact q3493_unreachable r
  · subst q
    exact q3497_unreachable r
  · subst q
    exact q3521_unreachable r
  · subst q
    exact q3541_unreachable r
  · subst q
    exact q3633_unreachable r
  · subst q
    exact q3721_unreachable r
  · subst q
    exact q3725_unreachable r
  · subst q
    exact q3881_unreachable r

#print axioms newQ_unreachable
end BB6.Agent28Affine4096
