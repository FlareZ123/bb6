import BoundaryExtra
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

namespace BB6.Agent36
open CryptidBoundary

def sourceBlank (s : Fin 6) : Cfg := ⟨[],false,[],s.val⟩

/-- Original D0 transition table, but every possible chosen blank state
    is represented explicitly in the same exact original-source interpreter. -/
theorem source_blank_A36 :
    run 36 (sourceBlank (0:Fin 6)) = init (List.replicate 7 true) := by
  decide

theorem source_blank_B15 :
    run 15 (sourceBlank (1:Fin 6)) = init (List.replicate 3 true) := by
  decide

theorem source_blank_C92 :
    run 92 (sourceBlank (2:Fin 6)) = init (List.replicate 13 true) := by
  decide

theorem source_blank_D15 :
    run 15 (sourceBlank (3:Fin 6)) = init (List.replicate 3 true) := by
  decide

theorem source_blank_E93 :
    run 93 (sourceBlank (4:Fin 6)) = init (List.replicate 13 true) := by
  decide

theorem source_blank_F403 :
    run 403 (sourceBlank (5:Fin 6)) = init (List.replicate 37 true) := by
  decide

/-- The exact further first F return is also source-certified for every
    rooted D-family blank initial state, using universal existing macros. -/
theorem source_blank_B116 :
    run 116 (sourceBlank (1:Fin 6)) = init (List.replicate 15 true) := by
  have ht : 116 = 15+(12*1*1+49*1+40) := by decide
  rw [ht, run_add, source_blank_B15]
  simpa [init] using full_B_nil 1

theorem source_blank_C524 :
    run 524 (sourceBlank (2:Fin 6)) = init (List.replicate 41 true) := by
  have ht : 524 = 92+(12*4*4+49*4+44) := by decide
  rw [ht, run_add, source_blank_C92]
  simpa [init] using full_A_nil 4

theorem source_blank_D116 :
    run 116 (sourceBlank (3:Fin 6)) = init (List.replicate 15 true) := by
  have ht : 116 = 15+(12*1*1+49*1+40) := by decide
  rw [ht, run_add, source_blank_D15]
  simpa [init] using full_B_nil 1

theorem source_blank_E525 :
    run 525 (sourceBlank (4:Fin 6)) = init (List.replicate 41 true) := by
  have ht : 525 = 93+(12*4*4+49*4+44) := by decide
  rw [ht, run_add, source_blank_E93]
  simpa [init] using full_A_nil 4

theorem source_blank_F2763 :
    run 2763 (sourceBlank (5:Fin 6)) = init (List.replicate 105 true) := by
  have ht : 2763 = 403+(12*12*12+49*12+44) := by decide
  rw [ht, run_add, source_blank_F403]
  simpa [init] using full_A_nil 12

#print axioms source_blank_A36
#print axioms source_blank_B15
#print axioms source_blank_C92
#print axioms source_blank_D15
#print axioms source_blank_E93
#print axioms source_blank_F403
#print axioms source_blank_B116
#print axioms source_blank_C524
#print axioms source_blank_D116
#print axioms source_blank_E525
#print axioms source_blank_F2763
end BB6.Agent36
