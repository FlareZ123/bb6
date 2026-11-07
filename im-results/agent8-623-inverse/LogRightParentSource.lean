import Agent8LogRightSectorsSource
import Agent8RootCorridorSource

/-!
Exact original-source #623 exclusion of four logarithmic right-tail
return sectors for any genuine blank-root halting daughter's parent.
The theorem is conditional and leaves the machine undecided.
-/

namespace BB6.Agent8LogRightParentSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

def rightLogBudget (a d k ell : Nat) : Prop :=
    (d%2=1 ∧ d+5≤a ∧ d+3<3^k ∧ a+k+ell≤4*d+19 ∧
       2*(a-d-5+k)+3≤3^ell) ∨
    (d%2=0 ∧ d+3≤a ∧ d+2<3^k ∧ a+k+ell≤4*d+10 ∧
       2*(a-d-2+k)+3≤3^ell) ∨
    (d%2=1 ∧ a<d+5 ∧ a-1<3^k ∧ d+4+k+ell≤4*a ∧
       2*(d+4-a+k)+3≤3^ell) ∨
    (d%2=0 ∧ a≤d ∧ a<3^k ∧ d+k+ell≤3*a+3 ∧
       2*(d+2-a+k)+3≤3^ell)

theorem two_step_terminal_excludes_right_log (a d aa dd : Nat)
    (ha : 0<a) (he : a%2=0)
    (hs : highLevelNext (.D a d)=some (.D aa dd))
    (hstop : highLevelNext (.D aa dd)=none) :
    ∀ k ell, ¬ rightLogBudget a d k ell := by
  intro k ell hbudget
  unfold rightLogBudget at hbudget
  rcases hbudget with h1|h2|h3|h4
  · rcases h1 with ⟨hd,hr,hb,hm,hp⟩
    obtain ⟨b,e,hn⟩ := BB6.Agent8LogRightSectorsSource.odd_left_of_diag_right_safe
      a d k ell aa dd ha he hd hr hb hm hp hs
    simp [hn] at hstop
  · rcases h2 with ⟨hd,hr,hb,hm,hp⟩
    obtain ⟨b,e,hn⟩ := BB6.Agent8LogRightSectorsSource.even_left_of_diag_right_safe
      a d k ell aa dd ha he hd hr hb hm hp hs
    simp [hn] at hstop
  · rcases h3 with ⟨hd,hr,hb,hm,hp⟩
    obtain ⟨b,e,hn⟩ := BB6.Agent8LogRightSectorsSource.odd_right_of_diag_right_safe
      a d k ell aa dd ha he hd hr hb hm hp hs
    simp [hn] at hstop
  · rcases h4 with ⟨hd,hr,hb,hm,hp⟩
    obtain ⟨b,e,hn⟩ := BB6.Agent8LogRightSectorsSource.even_right_of_diag_right_safe
      a d k ell aa dd ha he hd hr hb hm hp hs
    simp [hn] at hstop

theorem blank_terminal_excludes_right_log (n a d aa dd : Nat)
    (hseen : BB6.Agent49ParitySource.run n=some (.D a d))
    (hs : highLevelNext (.D a d)=some (.D aa dd))
    (hstop : highLevelNext (.D aa dd)=none) :
    0<a ∧ ∀ k ell, ¬ rightLogBudget a d k ell := by
  have hc := BB6.Agent8RootCorridorSource.blank_root_two_step_terminal_parent_corridor
    n a d aa dd hseen hs hstop
  have he := BB6.Agent49ParitySource.run_preserves_even n a d hseen
  exact ⟨hc.1, two_step_terminal_excludes_right_log a d aa dd hc.1 he hs hstop⟩

#print axioms two_step_terminal_excludes_right_log
#print axioms blank_terminal_excludes_right_log
end BB6.Agent8LogRightParentSource
