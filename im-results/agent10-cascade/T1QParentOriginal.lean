import OriginalGate268
import T1QParentFatal

/-!
Conditional original-machine consequence of the source t=1 Q-parent theorem.
A root Q-parent match in a surviving fatal sector is an authentic halting
witness for the unmodified six-state blank machine. This is not an assertion
that such a match exists.
-/

namespace Agent10T1Fatal

open BusyBeaver
open BusyBeaver.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA
open CascadeResetInverse

/-- Any genuine blank-root t=1 Q-parent match whose fatal index is in the
surviving original-source sectors forces the unmodified TM to halt. -/
theorem original_halts_of_root_t1_q_parent (h k d a j : Nat)
    (hroot : CascadeSweep.ReachC (2,0) (h,0))
    (hg : ∀ i, i<k → 8*2^i≤h+i+5)
    (hhigh : h+k+5<8*2^k)
    (hnot : h+k+4≠4*2^k)
    (hpar : (h+k)%2=1)
    (hfactor : CascadeLevelDeficit.oddParameter h k=2*d)
    (hd : d%2=1)
    (ha : CascadeLevelDeficit.oddOffset h k=2*a)
    (hQ : 9*a+2*k+7-2^(k+2)=(2*k+7)*2^(j+1))
    (hlarge : 268≤k+2)
    (hsector : (k+2)%6=4 ∨ (k+2)%6=5) :
    IsHalt target := by
  have hfatal : CascadeSweep.ReachC (2,0)
      (fatalHeight (k+2),0) :=
    root_t1_q_parent_fatal h k d a j hroot hg hhigh hnot hpar
      hfactor hd ha hQ
  apply (Agent10Raw746.original_machine_halts_iff_surviving_268).2
  refine ⟨k+2,hlarge,hsector,?_⟩
  exact (rootReachBool_source_iff _).2 hfatal

#print axioms original_halts_of_root_t1_q_parent

end Agent10T1Fatal
