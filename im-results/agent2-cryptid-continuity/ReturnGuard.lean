import Lean
import Boundary

set_option maxRecDepth 2000
set_option maxHeartbeats 10000000

namespace BB6.Agent2ReturnGuard
open CryptidBoundary

/-!
Corrected physical F-section return criterion. In the original raw model
an F/0 scan can occur while cells to the left are still nonblank.
The old Agent 2 Python simulator incorrectly used that marker.
-/
def seed4 : Cfg := init (List.replicate 2 true ++ [false,true,true])
def seed7 : Cfg := init (List.replicate 5 true ++ [false,true,true])

def actualSection (c : Cfg) : Bool :=
  (c.st == 5) && (!c.h) && c.l.all (fun b => !b)

/-- False earlier marker: at step 91 F scans zero, but left tape is 1011. -/
theorem false91 : run 91 seed4 =
    ⟨[true,false,true,true], false,
      [true,true,true,false,true,false,true,false,true,false], 5⟩ := by rfl

/-- Full correct section at step 96; terminal explicit zero is physically blank. -/
theorem correct96 : run 96 seed4 =
    ⟨[],false, List.replicate 3 true ++
      [false,true,true,true,true,false,true,false,true,false,true,false],5⟩ := by rfl

theorem correct157 : run 157 seed7 =
    ⟨[],false, List.replicate 11 true ++
      [false,true,true,true,true,false,true,false,true,false,true,false],5⟩ := by rfl

/-- Complete finite certification that NO physical return occurs at steps 1...95. -/
theorem no_valid_return_before96 :
    (List.range 95).all
      (fun t => !(actualSection (run (t+1) seed4))) = true := by decide

/-- Complete finite certification that NO physical return occurs at steps 1...156. -/
theorem no_valid_return_before157 :
    (List.range 156).all
      (fun t => !(actualSection (run (t+1) seed7))) = true := by decide

theorem false91_not_section : actualSection (run 91 seed4) = false := by decide
theorem correct96_is_section : actualSection (run 96 seed4) = true := by decide
theorem correct157_is_section : actualSection (run 157 seed7) = true := by decide

#print axioms false91
#print axioms correct96
#print axioms correct157
#print axioms no_valid_return_before96
#print axioms no_valid_return_before157
#print axioms false91_not_section
#print axioms correct96_is_section
#print axioms correct157_is_section
end BB6.Agent2ReturnGuard
