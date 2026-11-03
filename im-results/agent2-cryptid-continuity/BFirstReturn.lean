import Lean.Elab.Tactic.Omega
import PrefixNoF

namespace BB6.CryptidBFirstReturn
open CryptidBoundary
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidFirstReturn
open BB6.CryptidE111FirstReturn

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

def bStart (k : Nat) (ys : List Bool) : Cfg :=
  init (List.replicate (3*k) true ++ false::ys)

def bEnd (k : Nat) (ys : List Bool) : Cfg :=
  ⟨[],false,List.replicate (8*k+9) true ++ ys,5⟩

/-- An original-source exact *first* B return from F to physically blank-left
F on zero; all k and all arbitrary finite right suffixes. -/
theorem full_B_first_return (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+40) (bStart k ys) = bEnd k ys ∧
    ∀ t, 0<t → t<12*k*k+49*k+40 →
      ¬IsPhysicalReturn (run t (bStart k ys)) := by
  constructor
  · simpa [bStart,bEnd] using full_B k ys
  · intro t hpos ht hphys
    by_cases hpref : t<12*k*k+41*k+31
    · exact (prefixB_positive_noF k ys t hpos hpref) hphys.1
    · have hend :
        run (12*k*k+41*k+31) (bStart k ys) =
          sweepB (4*k+3) ys := by
        change run (12*k*k+41*k+31)
          (init (List.replicate (3*k) true ++ false::ys)) = _
        rw [prefix_B]
        rfl
      have htstep : t=(12*k*k+41*k+31)+(t-(12*k*k+41*k+31)) := by omega
      have hrest : t-(12*k*k+41*k+31) < 2*(4*k+3)+3 := by omega
      rw [htstep,run_add,hend] at hphys
      exact (sweepB_firstF (4*k+3) ys (t-(12*k*k+41*k+31)) hrest) hphys.1

/-- The B one-return relation is exactly shift-equivariant under k -> k+1:
the shifted first return has eight additional output ones and the same suffix.
This is a local branch theorem, not a claim about arbitrary branches. -/
theorem b_shift_three (k : Nat) (ys : List Bool) :
    bEnd (k+1) ys =
      ⟨[], false, List.replicate 8 true ++
        (List.replicate (8*k+9) true ++ ys), 5⟩ := by
  unfold bEnd
  have hn : 8*(k+1)+9 = 8+(8*k+9) := by omega
  rw [hn]
  rw [← List.append_assoc, List.replicate_append_replicate]

#print axioms full_B_first_return
#print axioms b_shift_three

end BB6.CryptidBFirstReturn
