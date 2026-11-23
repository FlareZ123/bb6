import BB429Branch9SideStrong
import BB429RootOddRowsStrong
import Lean.Elab.Tactic.Omega

/-!
# Branch-9 diagonal exceptional side parents: 117/128 forced inverse filter

The side-parent second coordinate is always odd, so its first inverse must
be F. In every residue surviving the one-step filter, the next inverse
is forced again (F when its first coordinate is odd, E when even).
The source all-time forbidden (3 mod8,5 mod8), (1 mod8,5 mod8), and
(5 mod32,1 mod8) cells leave only 11 possible k-residues mod128.

This is a finite-depth, all-natural, source-attached *necessary* filter,
not a proof that the other 11 classes are actually root reachable.
-/

namespace BB429Branch9SideDepth2

open BB429NewResidue

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

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

/-- Only 11 out of the 128 k classes can be genuine blank-root
    exceptional parents sufficiently far inside the branch-9 spine. -/
theorem side_parent_k_mod128_eleven (x y k : Nat)
    (hr : Reach x y) (hxlarge : 513 ≤ x)
    (hx128 : (x+8+3*k)%128=0)
    (hy128 : (y+6*k)%128=5) :
    k%128=9 ∨ k%128=11 ∨ k%128=25 ∨
    k%128=41 ∨ k%128=43 ∨ k%128=57 ∨
    k%128=75 ∨ k%128=89 ∨ k%128=105 ∨
    k%128=107 ∨ k%128=121 := by
  have hx32 : (x+8+3*k)%32=0 := by omega
  have hy32 : (y+6*k)%32=5 := by omega
  have h5 := BB429Branch9SideStrong.side_parent_k_mod32_five
    x y k hr (by omega) hx32 hy32
  have hxodd : x%2=1 := by omega
  rcases odd_back x y (by omega) hxodd hr with
    ⟨p,q,hp,hpx,hqy⟩ | ⟨p,q,hp,hpx,hqy,hq4⟩
  · by_cases hpodd : p%2=1
    · rcases odd_back p q (by omega) hpodd hp with
        ⟨r,s,hrs,hrp,hsq⟩ | ⟨r,s,hrs,hrp,hsq,hs4⟩
      · have hno35 : ¬(r%8=3 ∧ s%8=5) := by
          intro h
          exact no_root_three_five r s hrs (by omega) h.1 h.2
        have hno51 : ¬(r%32=5 ∧ s%8=1) := by
          intro h
          obtain ⟨n,hn⟩ := hrs
          have hfive := BB429SevenStrong.rooted_five_strong
            n r s hn h.1
          omega
        omega
      · omega
    · have hpeven : p%2=0 := by omega
      obtain ⟨r,s,hrs,hrp,hsq,hs4⟩ :=
        even_back p q (by omega) hpeven hp
      have hno15 : ¬(r%8=1 ∧ s%8=5) := by
        intro h
        exact no_root_one_five r s hrs (by omega) h.1 h.2
      omega
  · omega

private theorem pow_mod128_zero (e : Nat) (he : 7 ≤ e) :
    (2:Nat)^e % 128 = 0 := by
  have heq : e=7+(e-7) := by omega
  rw [heq, Nat.pow_add, show (2:Nat)^7=128 by decide]
  omega

/-- Full exact-power specialization to the diagonal side-parent
    coordinates for all natural N,J,t>=7 and sufficiently large x. -/
theorem diagonal_side_parent_k_mod128_eleven (x y N J t k : Nat)
    (hr : Reach x y) (hxlarge : 513 ≤ x)
    (hN : 7 ≤ N) (hJ : 7 ≤ J) (ht : 7 ≤ t)
    (hx : x+6*2^J+8+3*k=12*2^N+6*2^t)
    (hy : y+12*2^t+12*2^J+6*k=24*2^N+5) :
    k%128=9 ∨ k%128=11 ∨ k%128=25 ∨
    k%128=41 ∨ k%128=43 ∨ k%128=57 ∨
    k%128=75 ∨ k%128=89 ∨ k%128=105 ∨
    k%128=107 ∨ k%128=121 := by
  have hpN := pow_mod128_zero N hN
  have hpJ := pow_mod128_zero J hJ
  have hpT := pow_mod128_zero t ht
  apply side_parent_k_mod128_eleven x y k hr hxlarge
  · omega
  · omega

#print axioms side_parent_k_mod128_eleven
#print axioms diagonal_side_parent_k_mod128_eleven

end BB429Branch9SideDepth2
