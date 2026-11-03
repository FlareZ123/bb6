import Lean.Elab.Tactic.Omega
import BlankFifthExceptional

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000
namespace BB6.Agent25SixthRoot
open CryptidBoundary BB6.BoundaryPadding

def seed : DRegular.L := ⟨64*BB6.Agent25FifthRoot.t5+27,1,5⟩
def terminal4494 : DRegular.L :=
  (DRegular.run 4494 seed).getD ⟨9,0,0⟩
def t6 : Nat := (terminal4494.a-7)/9

theorem terminal4494_exact :
    DRegular.run 4494 seed = some ⟨9*t6+7,4,1⟩ := by decide

def sixthExceptionTime : Nat :=
  BB6.Agent25FifthRoot.fifthReentryTime + DRegular.accumulated 4494 seed

theorem sixthException_original :
    ObsEq (run sixthExceptionTime blank)
      (DRegularSource.sourceSection ⟨9*t6+7,4,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent25FifthRoot.fifthReentryTime
    4494 seed ⟨9*t6+7,4,1⟩
  · constructor
    · change 64*BB6.Agent25FifthRoot.t5+27 ≥ 2
      omega
    · left
      change 1 ≠ 0
      omega
  · exact terminal4494_exact
  · exact BB6.Agent25FifthRoot.fifthReentry_original

private theorem e_input :
    DRegularSource.sourceSection ⟨9*t6+7,4,1⟩ =
      init (List.replicate (3*(3*t6+1)+2) true ++
        false :: (pairs 3 ++ [true,true])) := by
  have hn : (9*t6+7)-2=3*(3*t6+1)+2 := by omega
  simp only [DRegularSource.sourceSection,init,hn,List.replicate_one]
  rw [List.append_assoc,BB6.Agent25BGeneral.oppairs_last]

def nextRawTime : Nat :=
  sixthExceptionTime + BB6.Agent32EAll.duration (3*t6+1) 3

/-- The genuine blank D orbit reaches the k≡1 (mod3), q4 exception
    beyond the five source-certified previous exceptional reentries.
    This then certifies the first F/0 section outside regular L. -/
theorem first_nonregular_original :
    ObsEq (run nextRawTime blank)
      (BB6.Agent32EAll.output (3*t6+1) 3 []) := by
  have hE : ObsEq
      (run (BB6.Agent32EAll.duration (3*t6+1) 3)
        (DRegularSource.sourceSection ⟨9*t6+7,4,1⟩))
      (BB6.Agent32EAll.output (3*t6+1) 3 []) := by
    rw [e_input]
    exact BB6.Agent32EAll.all_e_double_implicit_blank (3*t6+1) 3
  exact source_chain sixthExceptionTime
    (BB6.Agent32EAll.duration (3*t6+1) 3)
    blank (DRegularSource.sourceSection ⟨9*t6+7,4,1⟩)
    (BB6.Agent32EAll.output (3*t6+1) 3 [])
    sixthException_original hE

#print axioms terminal4494_exact
#print axioms sixthException_original
#print axioms first_nonregular_original
end BB6.Agent25SixthRoot
