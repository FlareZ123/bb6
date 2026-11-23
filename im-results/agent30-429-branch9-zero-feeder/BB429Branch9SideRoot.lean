import BB429NewResidue
import BB429SevenStrong
import Lean.Elab.Tactic.Omega

/-!
# Branch-9 diagonal: uniform root obstruction for exceptional S parents

The source map is unchanged BB429.next, with genuine blank-root reachability
BB429NewResidue.Reach. An interior side parent has X+8+3k = 0 (mod 32)
and Y+6k = 5 (mod 32). The theorem below rules out 25/32 k classes,
using no axiom other than transitive imported source results.
-/

namespace BB429Branch9SideRoot

open BB429NewResidue

set_option maxHeartbeats 20000000
set_option maxRecDepth 30000

/-- All-time blank-root obstruction on the affine side-parent residue line.
    This is a necessary condition, not positive reachability. -/
theorem side_parent_k_mod32 (x y k : Nat)
    (hr : Reach x y) (hxlarge : 33 ≤ x)
    (hx32 : (x + 8 + 3*k) % 32 = 0)
    (hy32 : (y + 6*k) % 32 = 5) :
    k%32=1 ∨ k%32=3 ∨ k%32=9 ∨ k%32=11 ∨
    k%32=19 ∨ k%32=25 ∨ k%32=27 := by
  have hyodd : y % 2 = 1 := by omega
  have hkodd : k % 2 = 1 := by
    by_contra h
    have hkeven : k % 2 = 0 := by omega
    have hxeven : x % 2 = 0 := by omega
    obtain ⟨n,hn⟩ := hr
    have h8 := BB429RootEven8.rooted_positive_even_eight
      n x y hn (by omega) hxeven
    omega
  have hnot5 : k % 8 ≠ 5 := by
    intro h5
    have hall := reach_allowed x y hr
    unfold BB429Mod8.Allowed at hall
    omega
  have hnot7 : k % 8 ≠ 7 := by
    intro h7
    have hxodd : x % 2 = 1 := by omega
    rcases odd_back x y (by omega) hxodd hr with
      ⟨p,q,hp,hpx,hqy⟩ | ⟨p,q,hp,hpx,hqy,hq4⟩
    · have hpeven : p % 2 = 0 := by omega
      have hppos : 0 < p := by omega
      obtain ⟨n,hn⟩ := hp
      have h8 := BB429RootEven8.rooted_positive_even_eight
        n p q hn hppos hpeven
      omega
    · omega
  have hnot17 : k % 32 ≠ 17 := by
    intro h17
    obtain ⟨n,hn⟩ := hr
    have h5 := BB429SevenStrong.rooted_five_strong
      n x y hn (by omega)
    omega
  omega

private theorem pow_mod32_zero (e : Nat) (he : 5 ≤ e) :
    (2:Nat)^e % 32 = 0 := by
  have heq : e = 5+(e-5) := by omega
  rw [heq, pow_add, show (2:Nat)^5 = 32 by decide]
  omega

/-- The symbolic S-parent exact equations imply the uniform modular
    obstruction whenever the displayed powers are at least 2^5.
    N=n+J and t=N-(4k+3) in the actual branch-9 diagonal family. -/
theorem diagonal_side_parent_k_mod32 (x y N J t k : Nat)
    (hr : Reach x y) (hxlarge : 33 ≤ x)
    (hN : 5 ≤ N) (hJ : 5 ≤ J) (ht : 5 ≤ t)
    (hx : x + 6*2^J + 8 + 3*k = 12*2^N + 6*2^t)
    (hy : y + 12*2^t + 12*2^J + 6*k = 24*2^N + 5) :
    k%32=1 ∨ k%32=3 ∨ k%32=9 ∨ k%32=11 ∨
    k%32=19 ∨ k%32=25 ∨ k%32=27 := by
  have hpN := pow_mod32_zero N hN
  have hpJ := pow_mod32_zero J hJ
  have hpT := pow_mod32_zero t ht
  apply side_parent_k_mod32 x y k hr hxlarge
  · omega
  · omega

#print axioms side_parent_k_mod32
#print axioms diagonal_side_parent_k_mod32

end BB429Branch9SideRoot
