import Lean.Elab.Tactic.Omega
import Boundary

set_option maxHeartbeats 10000000
set_option maxRecDepth 2000
set_option linter.unusedSimpArgs false

namespace BB6.Agent2EOneTriple
open CryptidBoundary

/-!
The complementary E(101101100111...) cylinder to EOneZeroHalt.
All prefix identities concern the exact original D-start machine transitions.
No assumption on the arbitrary binary tail.
-/
def packet : List Bool :=
  [false,true,true,true,true,false,true,false,true,false,
   true,false,true,false,true,false,true,false,true,false]

def e0 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[false,false] ++ pairs (m+3) ++ [true,true], false,
    [true,false,true,true,false,true,true,false,false,true,true,true] ++ ys, 4⟩

def e10 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[false,true,false,true,false,true] ++ pairs (m+3) ++ [true,true], false,
    [false,true,true,false,false,true,true,true] ++ ys, 2⟩

def e20 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[false,true,true,false,true,true,false,true,false,true] ++ pairs (m+3) ++ [true,true], false,
    [false,true,true,true] ++ ys, 0⟩

def e30 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[true,false,false,true,false,true] ++ pairs (m+3) ++ [true,true], true,
    [true,true,true,true,true,true,true,true] ++ ys, 1⟩

def e40 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[true,true,false,true] ++ pairs (m+3) ++ [true,true], true,
    [true,false,true,false,true,true,true,true,true,true] ++ ys, 1⟩

def e50 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[false,true,false,true,false,true,true,true,false,true] ++ pairs (m+3) ++ [true,true], true,
    [true,true,true,true] ++ ys, 0⟩

def e60 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[false,true,true,true,false,true] ++ pairs (m+3) ++ [true,true], false,
    [false,true,false,true,false,true,true,true] ++ ys, 1⟩

def e70 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[false,false] ++ pairs (m+2) ++ [true,true], false,
    [true,true,true,true,false,true,false,true,false,true,false,true,true,true] ++ ys, 0⟩

def e80 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[] ++ pairs (m+2) ++ [true,true], false,
    [true,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true] ++ ys, 0⟩

def e90 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[true,false,true,false,true,true] ++ pairs (m+2) ++ [true,true], true,
    [false,true,false,true,false,true,false,true,true,true] ++ ys, 1⟩

def e100 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true] ++ pairs (m+2) ++ [true,true], true,
    [] ++ ys, 4⟩

def e110 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[true,false,true,false,true,false,true,false,true,true] ++ pairs (m+2) ++ [true,true], false,
    [true,false,true,false,true,false] ++ ys, 2⟩

def e120 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[false,false,true,false,true,true] ++ pairs (m+2) ++ [true,true], true,
    [true,false,true,false,true,false,true,false,true,false] ++ ys, 4⟩

def e130 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[] ++ pairs (m+2) ++ [true,true], true,
    [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] ++ ys, 2⟩

def e134 (m : Nat) (ys : List Bool) : Cfg :=
  ⟨[] ++ pairs (m+0) ++ [true,true], false,
    [false,true,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false] ++ ys, 1⟩

theorem ee0 (m : Nat) (ys : List Bool) :
    run 10 (e0 m ys) = e10 m ys := by
  simp [e0,e10,run,step,goL,goR,pairs,List.append_assoc]

theorem ee10 (m : Nat) (ys : List Bool) :
    run 10 (e10 m ys) = e20 m ys := by
  simp [e10,e20,run,step,goL,goR,pairs,List.append_assoc]

theorem ee20 (m : Nat) (ys : List Bool) :
    run 10 (e20 m ys) = e30 m ys := by
  simp [e20,e30,run,step,goL,goR,pairs,List.append_assoc]

theorem ee30 (m : Nat) (ys : List Bool) :
    run 10 (e30 m ys) = e40 m ys := by
  simp [e30,e40,run,step,goL,goR,pairs,List.append_assoc]

theorem ee40 (m : Nat) (ys : List Bool) :
    run 10 (e40 m ys) = e50 m ys := by
  simp [e40,e50,run,step,goL,goR,pairs,List.append_assoc]

theorem ee50 (m : Nat) (ys : List Bool) :
    run 10 (e50 m ys) = e60 m ys := by
  simp [e50,e60,run,step,goL,goR,pairs,List.append_assoc]

theorem ee60 (m : Nat) (ys : List Bool) :
    run 10 (e60 m ys) = e70 m ys := by
  simp [e60,e70,run,step,goL,goR,pairs,List.append_assoc]

theorem ee70 (m : Nat) (ys : List Bool) :
    run 10 (e70 m ys) = e80 m ys := by
  simp [e70,e80,run,step,goL,goR,pairs,List.append_assoc]

theorem ee80 (m : Nat) (ys : List Bool) :
    run 10 (e80 m ys) = e90 m ys := by
  simp [e80,e90,run,step,goL,goR,pairs,List.append_assoc]

theorem ee90 (m : Nat) (ys : List Bool) :
    run 10 (e90 m ys) = e100 m ys := by
  simp [e90,e100,run,step,goL,goR,pairs,List.append_assoc]

theorem ee100 (m : Nat) (ys : List Bool) :
    run 10 (e100 m ys) = e110 m ys := by
  simp [e100,e110,run,step,goL,goR,pairs,List.append_assoc]

theorem ee110 (m : Nat) (ys : List Bool) :
    run 10 (e110 m ys) = e120 m ys := by
  simp [e110,e120,run,step,goL,goR,pairs,List.append_assoc]

theorem ee120 (m : Nat) (ys : List Bool) :
    run 10 (e120 m ys) = e130 m ys := by
  simp [e120,e130,run,step,goL,goR,pairs,List.append_assoc]

theorem ee130 (m : Nat) (ys : List Bool) :
    run 4 (e130 m ys) = e134 m ys := by
  simp [e130,e134,run,step,goL,goR,pairs,List.append_assoc]

/-- Uniform E-to-B bridge after exactly 134 raw primitive steps. -/
theorem to134 (m : Nat) (ys : List Bool) :
    run 134 (e0 m ys) = e134 m ys := by
  have ht0 : 134 = 10+124 := by omega
  rw [ht0,run_add,ee0]
  have ht10 : 124 = 10+114 := by omega
  rw [ht10,run_add,ee10]
  have ht20 : 114 = 10+104 := by omega
  rw [ht20,run_add,ee20]
  have ht30 : 104 = 10+94 := by omega
  rw [ht30,run_add,ee30]
  have ht40 : 94 = 10+84 := by omega
  rw [ht40,run_add,ee40]
  have ht50 : 84 = 10+74 := by omega
  rw [ht50,run_add,ee50]
  have ht60 : 74 = 10+64 := by omega
  rw [ht60,run_add,ee60]
  have ht70 : 64 = 10+54 := by omega
  rw [ht70,run_add,ee70]
  have ht80 : 54 = 10+44 := by omega
  rw [ht80,run_add,ee80]
  have ht90 : 44 = 10+34 := by omega
  rw [ht90,run_add,ee90]
  have ht100 : 34 = 10+24 := by omega
  rw [ht100,run_add,ee100]
  have ht110 : 24 = 10+14 := by omega
  rw [ht110,run_add,ee110]
  have ht120 : 14 = 10+4 := by omega
  rw [ht120,run_add,ee120]
  have ht130 : 4 = 4+0 := by omega
  rw [ht130,run_add,ee130]
  rfl

/-- The return front closes into the original symbolic B sweep. -/
theorem front (m : Nat) (ys : List Bool) :
    run 134 (e0 m ys) = sweepB m (packet ++ ys) := by
  rw [to134]
  rfl

theorem e111_run (m : Nat) (ys : List Bool) :
    run (2*m+137) (e0 m ys) =
      ⟨[],false,List.replicate (2*m+3) true ++ (packet ++ ys),5⟩ := by
  have ht : 2*m+137 = 134+(2*m+3) := by omega
  rw [ht,run_add,front,sweepB_run]

/-- A complete source-level E F-to-F return for all k and binary tails. -/
theorem full_E_one_triple_return (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+170)
      (init (List.replicate (3*k+2) true ++
        false :: ([true,false,true,true,false,true,true,false,false,
                   true,true,true] ++ ys))) =
      ⟨[],false,List.replicate (8*k+3) true ++ (packet ++ ys),5⟩ := by
  have ht : 12*k*k+49*k+170 = (12*k*k+41*k+33)+(2*(4*k)+137) := by omega
  rw [ht,run_add,prefix_E]
  change run (2*(4*k)+137) (e0 (4*k) ys) = _
  rw [e111_run]
  rw [show 2*(4*k)+3=8*k+3 by omega]

#print axioms to134
#print axioms front
#print axioms e111_run
#print axioms full_E_one_triple_return

end BB6.Agent2EOneTriple
