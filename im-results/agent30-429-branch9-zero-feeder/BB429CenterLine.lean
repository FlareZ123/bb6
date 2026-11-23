import BB429NewResidue
import BB429SevenStrong
import BB429Even16
import Lean.Elab.Tactic.Omega

/-!
# Genuine blank-root states on the central reset boundary w = 2u

This source-attached all-natural result filters the possible predecessor
of a zero-return with z = 4u+12. It is a necessary root condition,
not a full classification of all zero-return predecessors.
-/

namespace BB429CenterLine

open BB429NewResidue

set_option maxHeartbeats 25000000
set_option maxRecDepth 30000

/-- If the first coordinate is 3 mod8 and the second coordinate is also
    3 mod8, the exact odd source predecessor is positive even with the
    forbidden second-coordinate residue 6 mod8. -/
private theorem no_root_three_three (a b : Nat)
    (hr : Reach a b) (ha : 13 ≤ a)
    (ha8 : a%8=3) (hb8 : b%8=3) : False := by
  rcases odd_back a b ha (by omega) hr with
    ⟨p,q,hp,hpa,hqb⟩ | ⟨p,q,hp,hpa,hqb,hb4⟩
  · have hp0 : 0<p := by omega
    have hpe : p%2=0 := by omega
    obtain ⟨n,hn⟩ := hp
    have hh := BB429RootEven8.rooted_positive_even_eight n p q hn hp0 hpe
    omega
  · omega

/-- Existing all-time positive-even modulo-16 law, specialized to an
    incompatible 2(mod4),2(mod16) root row. -/
private theorem no_root_even_two_two (a b : Nat)
    (hr : Reach a b) (ha : 0<a)
    (ha4 : a%4=2) (hb16 : b%16=2) : False := by
  obtain ⟨n,hn⟩ := hr
  have hh := BB429Even16.rooted_even_sixteen n a b hn ha (by omega)
  have hb10 := hh.2 ha4
  omega

/-- An all-time necessary first-counter restriction for a genuine
    blank-root visit to the center reset line (u,2u), for u >= 129.
    The exceptional small u are deliberately not asserted. -/
theorem rooted_center_mod32 (u : Nat)
    (hr : Reach u (2*u)) (hu : 129 ≤ u) :
    u%32=13 ∨ u%32=17 ∨ u%32=25 ∨ u%32=29 := by
  have huOdd : u%2=1 := by
    by_cases he : u%2=0
    · obtain ⟨n,hn⟩ := hr
      have h8 := BB429RootEven8.rooted_positive_even_eight
        n u (2*u) hn (by omega) he
      omega
    · omega
  have hnot7 : u%8≠7 := by
    intro h7
    obtain ⟨n,hn⟩ := hr
    have hh := BB429SevenStrong.rooted_seven_strong n u (2*u) hn h7
    omega
  have hnot3 : u%8≠3 := by
    intro h3
    rcases odd_back u (2*u) (by omega) huOdd hr with
      ⟨p,q,hp,hpu,hqu⟩ | ⟨p,q,hp,hpu,hqu,hq4⟩
    · have hp0 : 0<p := by omega
      have hpe : p%2=0 := by omega
      obtain ⟨n,hn⟩ := hp
      have hh := BB429RootEven8.rooted_positive_even_eight n p q hn hp0 hpe
      omega
    · have hp0 : 0<p := by omega
      have hpe : p%2=0 := by omega
      obtain ⟨n,hn⟩ := hp
      have hh := BB429RootEven8.rooted_positive_even_eight n p q hn hp0 hpe
      omega
  have hnot5 : u%16≠5 := by
    intro h5
    rcases odd_back u (2*u) (by omega) huOdd hr with
      ⟨p,q,hp,hpu,hqu⟩ | ⟨p,q,hp,hpu,hqu,hq4⟩
    · have hall := reach_allowed p q hp
      unfold BB429Mod8.Allowed at hall
      omega
    · have hall := reach_allowed p q hp
      unfold BB429Mod8.Allowed at hall
      omega
  have hnot1 : u%32≠1 := by
    intro h1
    rcases odd_back u (2*u) (by omega) huOdd hr with
      ⟨p,q,hp,hpu,hqu⟩ | ⟨p,q,hp,hpu,hqu,hq4⟩
    · have hpOdd : p%2=1 := by omega
      rcases odd_back p q (by omega) hpOdd hp with
        ⟨r,s,hrs,hrp,hsq⟩ | ⟨r,s,hrs,hrp,hsq,hs4⟩
      · exact no_root_even_two_two r s hrs
          (by omega) (by omega) (by omega)
      · omega
    · exact no_root_three_three p q hp (by omega) (by omega) (by omega)
  have hnot9 : u%32≠9 := by
    intro h9
    rcases odd_back u (2*u) (by omega) huOdd hr with
      ⟨p,q,hp,hpu,hqu⟩ | ⟨p,q,hp,hpu,hqu,hq4⟩
    · exact no_root_three_three p q hp (by omega) (by omega) (by omega)
    · have hpOdd : p%2=1 := by omega
      rcases odd_back p q (by omega) hpOdd hp with
        ⟨r,s,hrs,hrp,hsq⟩ | ⟨r,s,hrs,hrp,hsq,hs4⟩
      · exact no_root_even_two_two r s hrs
          (by omega) (by omega) (by omega)
      · omega
  omega


/-- A center-line parent of the all-F low-nine zero feeder restricts its
    exponent index J to four residue classes modulo 128. This corollary
    deliberately requires the exact modular feeder equation as a hypothesis;
    it does not exclude other zero-return predecessor kinds. -/
theorem diagonal_zero_center_j_mod128 (J z u : Nat)
    (hr : Reach u (2*u)) (hu : 129 ≤ u)
    (hz : z=4*u+12)
    (hmod : (z+3*J)%128=36) :
    J%128=12 ∨ J%128=28 ∨ J%128=60 ∨ J%128=76 := by
  have hc := rooted_center_mod32 u hr hu
  omega

private theorem pow_mod128_zero (e : Nat) (he : 7 ≤ e) :
    (2:Nat)^e % 128 = 0 := by
  have heq : e=7+(e-7) := by omega
  rw [heq, Nat.pow_add, show (2:Nat)^7=128 by decide]
  omega

/-- The actual all-F zero-feeder power equation implies that same
    necessary J-residue list. In the diagonal subfamily N=n+J, the
    N>=5 side condition is automatic. -/
theorem diagonal_zero_center_power_j_mod128 (J N z u : Nat)
    (hr : Reach u (2*u)) (hu : 129 ≤ u)
    (hJ : 3 ≤ J) (hN : 5 ≤ N)
    (hz : z=4*u+12)
    (heq : z+48*2^J+3*J=12*2^(N+2)+36) :
    J%128=12 ∨ J%128=28 ∨ J%128=60 ∨ J%128=76 := by
  have hpN := pow_mod128_zero (N+2) (by omega)
  have hpJ := pow_mod128_zero (J+4) (by omega)
  have hmul : 48*2^J=3*2^(J+4) := by
    rw [show J+4=4+J by omega, Nat.pow_add,
        show (2:Nat)^4=16 by decide]
    omega
  have hpowJ : (48*2^J)%128=0 := by
    rw [hmul]
    omega
  have hmod : (z+3*J)%128=36 := by omega
  exact diagonal_zero_center_j_mod128 J z u hr hu hz hmod

#print axioms diagonal_zero_center_j_mod128
#print axioms diagonal_zero_center_power_j_mod128

#print axioms no_root_three_three
#print axioms no_root_even_two_two
#print axioms rooted_center_mod32

end BB429CenterLine
