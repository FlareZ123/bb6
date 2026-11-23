import BB429Branch9SideRoot
import BB429Even16
import Lean.Elab.Tactic.Omega

/-!
# A forced first inverse strengthens the BB429 branch-9 side restriction

Because every exceptional side parent has odd second coordinate, its only
large-first-coordinate predecessor is the F predecessor. When k=3 mod16
that predecessor is positive even with q=2 mod16 and p=2 mod4,
contradicting the true-blank even16 root invariant. This upgrades the
existing 25/32 filter to 27/32 excluded k residues, uniformly.

All theorems retain genuine blank-root Reach, not synthetic reachability.
-/

namespace BB429Branch9SideStrong

open BB429NewResidue

set_option maxHeartbeats 25000000
set_option maxRecDepth 30000

/-- Five necessary k-residue classes of a large authentic side parent
    on the diagonal affine line. -/
theorem side_parent_k_mod32_five (x y k : Nat)
    (hr : Reach x y) (hxlarge : 129 ≤ x)
    (hx32 : (x+8+3*k)%32=0)
    (hy32 : (y+6*k)%32=5) :
    k%32=1 ∨ k%32=9 ∨ k%32=11 ∨
    k%32=25 ∨ k%32=27 := by
  have h7 := BB429Branch9SideRoot.side_parent_k_mod32
    x y k hr (by omega) hx32 hy32
  have hnot3 : k%16≠3 := by
    intro h3
    have hxodd : x%2=1 := by omega
    rcases odd_back x y (by omega) hxodd hr with
      ⟨p,q,hp,hpx,hqy⟩ | ⟨p,q,hp,hpx,hqy,hq4⟩
    · obtain ⟨n,hn⟩ := hp
      have he : p%2=0 := by omega
      have h4 : p%4=2 := by omega
      have h16 : q%16=2 := by omega
      have hh := BB429Even16.rooted_even_sixteen
        n p q hn (by omega) he
      have hq10 := hh.2 h4
      omega
    · omega
  omega

private theorem pow_mod32_zero (e : Nat) (he : 5 ≤ e) :
    (2:Nat)^e % 32 = 0 := by
  have heq : e=5+(e-5) := by omega
  rw [heq, Nat.pow_add, show (2:Nat)^5=32 by decide]
  omega

/-- Uniform strong filter for every actual branch-9 side parent written
    in its exact power-of-two coordinates; J,t,N>=5. -/
theorem diagonal_side_parent_k_five (x y N J t k : Nat)
    (hr : Reach x y) (hxlarge : 129 ≤ x)
    (hN : 5 ≤ N) (hJ : 5 ≤ J) (ht : 5 ≤ t)
    (hx : x+6*2^J+8+3*k=12*2^N+6*2^t)
    (hy : y+12*2^t+12*2^J+6*k=24*2^N+5) :
    k%32=1 ∨ k%32=9 ∨ k%32=11 ∨
    k%32=25 ∨ k%32=27 := by
  have hpN := pow_mod32_zero N hN
  have hpJ := pow_mod32_zero J hJ
  have hpT := pow_mod32_zero t ht
  apply side_parent_k_mod32_five x y k hr hxlarge
  · omega
  · omega

#print axioms side_parent_k_mod32_five
#print axioms diagonal_side_parent_k_five

end BB429Branch9SideStrong
