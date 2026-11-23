import BB429NewResidue
import BB429SevenStrong
import BB429Even16
import Lean.Elab.Tactic.Omega

/-!
# Exact blank-root restriction on upper zero-reset boundary w=2u+2

Affects the all-F zero-two feeder from the branch-9 diagonal family.
Root predicates and all inverses refer to the unchanged genuine BB429 source.
-/

namespace BB429UpperBoundary

open BB429NewResidue

set_option maxHeartbeats 20000000
set_option maxRecDepth 30000

/-- Genuine root states in the 3(mod8),5(mod8) odd/odd cell would
    have a forbidden positive-even first predecessor. -/
private theorem no_root_three_five (a b : Nat)
    (hr : Reach a b) (ha : 13 ≤ a)
    (ha8 : a%8=3) (hb8 : b%8=5) : False := by
  rcases odd_back a b ha (by omega) hr with
    ⟨p,q,hp,hpa,hqb⟩ | ⟨p,q,hp,hpa,hqb,hb4⟩
  · obtain ⟨n,hn⟩ := hp
    have hh := BB429RootEven8.rooted_positive_even_eight
      n p q hn (by omega) (by omega)
    omega
  · omega

/-- Necessary first-counter classes for a source-root visit to the
    upper zero-reset boundary (u,2u+2) at sufficiently large u.
    This shrinks a previous seven-class mod16 overapproximation to four. -/
theorem rooted_upper_mod16 (u : Nat)
    (hr : Reach u (2*u+2)) (hu : 129 ≤ u) :
    u%16=0 ∨ u%16=5 ∨ u%16=8 ∨ u%16=13 := by
  have hEvenOrOdd : u%2=1 ∨ u%8=0 := by
    by_cases he : u%2=0
    · obtain ⟨n,hn⟩ := hr
      have hh := BB429Even16.rooted_even_sixteen
        n u (2*u+2) hn (by omega) he
      right
      omega
    · left
      omega
  have hnot3 : u%8≠3 := by
    intro h3
    have hh := reach_allowed u (2*u+2) hr
    unfold BB429Mod8.Allowed at hh
    omega
  have hnot7 : u%8≠7 := by
    intro h7
    obtain ⟨n,hn⟩ := hr
    have hh := BB429SevenStrong.rooted_seven_strong n u (2*u+2) hn h7
    omega
  have hnot1 : u%16≠1 := by
    intro h1
    obtain ⟨n,hn⟩ := hr
    have hh := BB429SevenStrong.rooted_one_strong n u (2*u+2) hn h1
    omega
  have hnot9 : u%16≠9 := by
    intro h9
    rcases odd_back u (2*u+2) (by omega) (by omega) hr with
      ⟨p,q,hp,hpu,hqu⟩ | ⟨p,q,hp,hpu,hqu,hq4⟩
    · exact no_root_three_five p q hp (by omega) (by omega) (by omega)
    · omega
  omega

#print axioms no_root_three_five
#print axioms rooted_upper_mod16

end BB429UpperBoundary
