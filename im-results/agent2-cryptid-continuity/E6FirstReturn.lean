import Lean.Elab.Tactic.Omega
import PrefixNoF

namespace BB6.CryptidE6FirstReturn
open CryptidBoundary
open BB6.CryptidE111FirstReturn
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidFirstReturn

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- The sixteen-step, six-ones E-boundary bridge has no physically blank-left
F-on-zero visit even at its internal, non-section F passages. -/
private theorem eSix_before16 (m : Nat) (ys : List Bool) :
    NoReturn (eSix m ys) 16 := by
  intro t ht hphys
  have hcases :
      t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨
      t=7 ∨ t=8 ∨ t=9 ∨ t=10 ∨ t=11 ∨ t=12 ∨
      t=13 ∨ t=14 ∨ t=15 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [IsPhysicalReturn,eSix,run,step,goL,goR,pairs,List.append_assoc] at hphys

theorem eSix_boundary_first_return (m : Nat) (ys : List Bool) :
    run (2*m+19) (eSix m ys) =
      ⟨[],false,List.replicate (2*m+3) true ++ (packetSix ++ ys),5⟩ ∧
    NoReturn (eSix m ys) (2*m+19) := by
  constructor
  · exact eSix_run m ys
  · intro t ht hphys
    by_cases hfront : t<16
    · exact eSix_before16 m ys t hfront hphys
    · have htime : t=16+(t-16) := by omega
      have hrest : t-16<2*m+3 := by omega
      rw [htime,run_add,eSix_front] at hphys
      exact sweepB_firstF m (packetSix++ys) (t-16) hrest hphys.1

def e6Start (k : Nat) (ys : List Bool) : Cfg :=
  init (List.replicate (3*k+2) true ++
    false :: (List.replicate 6 true ++ false::ys))

def e6End (k : Nat) (ys : List Bool) : Cfg :=
  ⟨[],false,List.replicate (8*k+9) true ++ (packetSix++ys),5⟩

/-- Fully source-authenticated first positive F/0 return in the E-six cylinder
for every unary count and arbitrary right tail. -/
theorem full_E_six_first_return (k : Nat) (ys : List Bool) :
    run (12*k*k+49*k+58) (e6Start k ys) = e6End k ys ∧
    ∀ t, 0<t → t<12*k*k+49*k+58 →
      ¬IsPhysicalReturn (run t (e6Start k ys)) := by
  constructor
  · simpa [e6Start,e6End] using full_E_six k ys
  · intro t hpos ht hphys
    by_cases hpref : t<12*k*k+41*k+33
    · exact (prefixE_positive_noF k
        (List.replicate 6 true ++ false::ys) t hpos hpref) hphys.1
    · have hend : run (12*k*k+41*k+33) (e6Start k ys) =
        eSix (4*k+3) ys := by
        change run (12*k*k+41*k+33)
          (init (List.replicate (3*k+2) true ++
            false :: (List.replicate 6 true ++ false::ys))) = _
        rw [prefix_E]
        rfl
      have htime : t=(12*k*k+41*k+33)+(t-(12*k*k+41*k+33)) := by omega
      have hrest : t-(12*k*k+41*k+33)<2*(4*k+3)+19 := by omega
      rw [htime,run_add,hend] at hphys
      exact (eSix_boundary_first_return (4*k+3) ys).2
        (t-(12*k*k+41*k+33)) hrest hphys

#print axioms eSix_before16
#print axioms eSix_boundary_first_return
#print axioms full_E_six_first_return
end BB6.CryptidE6FirstReturn
