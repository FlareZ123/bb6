import Agent8QuadraticLogConeSource
import Agent8RootCorridorSource

/-!
Four fivefold, quadratic-log-budget source sectors are necessary exclusions
for the parent of any hypothetical terminal state of the actual blank
root #623 accelerator. No actual-machine halting/nonhalting conclusion.
-/

namespace BB6.Agent8QuadraticParentSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

def quadraticBudget (a d n ell : Nat) : Prop :=
   (d%2=1 ∧ d+3<3^n ∧ 5*d+27+n*(n+5)+ell≤a ∧
      6*d+35+2*(n*(n+5))≤3^ell) ∨
   (d%2=0 ∧ d+2<3^n ∧ 5*d+17+n*(n+5)+ell≤a ∧
      6*d+23+2*(n*(n+5))≤3^ell) ∨
   (d%2=1 ∧ a-1<3^n ∧ 5*a+n*(n+5)+ell≤d ∧
      6*a+7+2*(n*(n+5))≤3^ell) ∨
   (d%2=0 ∧ a<3^n ∧ 5*a+n*(n+5)+2*n+12+ell≤d ∧
      6*a+4*n+21+2*(n*(n+5))≤3^ell)

theorem terminal_excludes_quadratic (a d aa dd : Nat)
    (ha : 0<a) (he : a%2=0)
    (hs : highLevelNext (.D a d)=some (.D aa dd))
    (hstop : highLevelNext (.D aa dd)=none) :
    ∀ n ell, ¬ quadraticBudget a d n ell := by
  intro n ell hbudget
  unfold quadraticBudget at hbudget
  rcases hbudget with h1|h2|h3|h4
  · rcases h1 with ⟨hd,hb,hm,hp⟩
    obtain ⟨b,e,hn⟩ := BB6.Agent8QuadraticLogConeSource.odd_far_left_quadratic_two_step
      a d n ell aa dd ha hd hb hm hp hs
    simp [hn] at hstop
  · rcases h2 with ⟨hd,hb,hm,hp⟩
    obtain ⟨b,e,hn⟩ := BB6.Agent8QuadraticLogConeSource.even_far_left_quadratic_two_step
      a d n ell aa dd ha hd hb hm hp hs
    simp [hn] at hstop
  · rcases h3 with ⟨hd,hb,hm,hp⟩
    obtain ⟨b,e,hn⟩ := BB6.Agent8QuadraticLogConeSource.odd_far_right_quadratic_two_step
      a d n ell aa dd ha he hd hb hm hp hs
    simp [hn] at hstop
  · rcases h4 with ⟨hd,hb,hm,hp⟩
    obtain ⟨b,e,hn⟩ := BB6.Agent8QuadraticLogConeSource.even_far_right_quadratic_two_step
      a d n ell aa dd ha he hd hb hm hp hs
    simp [hn] at hstop

theorem blank_terminal_excludes_quadratic (m a d aa dd : Nat)
    (hseen : BB6.Agent49ParitySource.run m=some (.D a d))
    (hs : highLevelNext (.D a d)=some (.D aa dd))
    (hstop : highLevelNext (.D aa dd)=none) :
    0<a ∧ ∀ n ell, ¬ quadraticBudget a d n ell := by
  have hroot := BB6.Agent8RootCorridorSource.blank_root_two_step_terminal_parent_corridor
    m a d aa dd hseen hs hstop
  have he := BB6.Agent49ParitySource.run_preserves_even m a d hseen
  exact ⟨hroot.1, terminal_excludes_quadratic a d aa dd hroot.1 he hs hstop⟩

#print axioms terminal_excludes_quadratic
#print axioms blank_terminal_excludes_quadratic
end BB6.Agent8QuadraticParentSource
