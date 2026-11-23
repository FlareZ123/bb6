import BB429OddResetGate
import BB429Even16
import BB429RootOddRowsStrong
import Lean.Elab.Tactic.Omega

/-!
# Authentic BB429 near-halting odd-reset line: three necessary classes mod32

The earlier BB429OddResetGate.rooted_odd_reset_necessary_six leaves six
u mod32 classes. The all-time positive even mod16 theorem and two-step
odd/odd predecessor rows eliminate 7, 21, and 31 for all u>=129.

These are all-time genuine blank-root theorems about the unchanged
source-equivalent BB429.next, not a decision that #429 halts or diverges.
-/

namespace BB429OddResetImproved

open BB429NewResidue

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

/-- Every genuine odd/odd state in the residue (3 mod8,5 mod8)
    would have an impossible positive-even predecessor. -/
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

/-- A genuinely root-reachable state with u=1 mod8 cannot have
    w=5 mod8, using exact all-time one and nine root rows. -/
private theorem no_root_one_five (a b : Nat)
    (hr : Reach a b) (ha : 33 ≤ a)
    (ha8 : a%8=1) (hb8 : b%8=5) : False := by
  by_cases h1 : a%16=1
  · obtain ⟨n,hn⟩ := hr
    have hh := BB429SevenStrong.rooted_one_strong n a b hn h1
    omega
  · have h9 : a%16=9 := by omega
    exact BB429RootOddRowsStrong.rooted_not_9_5
      a b hr ha h9 hb8

/-- The 7 mod32 odd-reset input has an even parent with second
    coordinate 2 mod16 where the all-time even16 root row demands 10. -/
theorem rooted_odd_reset_not_seven (u w : Nat)
    (hr : Reach u w) (hu : 129 ≤ u)
    (hw : w+3=2*u) (h7 : u%32=7) : False := by
  rcases odd_back u w (by omega) (by omega) hr with
    ⟨p,q,hp,hpu,hqu⟩ | ⟨p,q,hp,hpu,hqu,hq4⟩
  · obtain ⟨n,hn⟩ := hp
    have hEven : p%2=0 := by omega
    have h4 : p%4=2 := by omega
    have h16 : q%16=2 := by omega
    have hh := BB429Even16.rooted_even_sixteen
      n p q hn (by omega) hEven
    have hq10 := hh.2 h4
    omega
  · omega

/-- The 21 mod32 odd-reset input forces a genuine odd/odd grandparent
    in the forbidden (3 mod8,5 mod8) root cell. -/
theorem rooted_odd_reset_not_twentyone (u w : Nat)
    (hr : Reach u w) (hu : 129 ≤ u)
    (hw : w+3=2*u) (h21 : u%32=21) : False := by
  rcases odd_back u w (by omega) (by omega) hr with
    ⟨p,q,hp,hpu,hqu⟩ | ⟨p,q,hp,hpu,hqu,hq4⟩
  · rcases odd_back p q (by omega) (by omega) hp with
      ⟨r,s,hrs,hrp,hsq⟩ | ⟨r,s,hrs,hrp,hsq,hs4⟩
    · exact no_root_three_five r s hrs
        (by omega) (by omega) (by omega)
    · omega
  · omega

/-- The 31 mod32 odd-reset input forces an even first parent, whose
    unique predecessor is in the impossible (1 mod8,5 mod8) cell. -/
theorem rooted_odd_reset_not_thirtyone (u w : Nat)
    (hr : Reach u w) (hu : 129 ≤ u)
    (hw : w+3=2*u) (h31 : u%32=31) : False := by
  rcases odd_back u w (by omega) (by omega) hr with
    ⟨p,q,hp,hpu,hqu⟩ | ⟨p,q,hp,hpu,hqu,hq4⟩
  · obtain ⟨r,s,hrs,hrp,hsq,hs4⟩ :=
      even_back p q (by omega) (by omega) hp
    exact no_root_one_five r s hrs
      (by omega) (by omega) (by omega)
  · omega

/-- Strong necessary modulo-32 classification of every genuine blank-root
    odd-reset input at first counter >=129. Exactly three residue classes
    survive as *necessary* possibilities; none is asserted reachable. -/
theorem rooted_odd_reset_necessary_three (u w : Nat)
    (hr : Reach u w) (hu : 129 ≤ u)
    (hw : w+3=2*u) :
    u%32=13 ∨ u%32=15 ∨ u%32=29 := by
  obtain ⟨n,hn⟩ := hr
  have h6 := BB429OddResetGate.rooted_odd_reset_necessary_six
    n u w hn hw
  have h7 : u%32≠7 := by
    intro h
    exact rooted_odd_reset_not_seven u w ⟨n,hn⟩ hu hw h
  have h21 : u%32≠21 := by
    intro h
    exact rooted_odd_reset_not_twentyone u w ⟨n,hn⟩ hu hw h
  have h31 : u%32≠31 := by
    intro h
    exact rooted_odd_reset_not_thirtyone u w ⟨n,hn⟩ hu hw h
  omega

#print axioms rooted_odd_reset_not_seven
#print axioms rooted_odd_reset_not_twentyone
#print axioms rooted_odd_reset_not_thirtyone
#print axioms rooted_odd_reset_necessary_three

end BB429OddResetImproved
