import RayOddForkExtended

set_option maxHeartbeats 0

namespace CascadeTerminalHighBand
open CascadeResetInverse CascadeRayOddStrip CascadeSweep

/-- Canonical-ray high-c numerical inequalities, with the two dyadic
    powers already named p and s. The proof is entirely linear arithmetic
    and does not silently assume a bound on the odd 3-adic valuation. -/
theorem terminal_high_window (n p q s u : Nat)
    (hn : 257 ≤ n)
    (hsource : u + q + 1 = 4*p+n)
    (hbelow : q < 2*p)
    (hhigh : 7*p+4*s ≤ 4*q)
    (hs : n+5 ≤ s) :
    2*p < u ∧ 8*u+32 < 18*p := by
  omega

/-- Source-connected terminal-leaf exclusion in the high-c ray window.
    The narrow-gap ResetParent lemma checks every even image scale,
    t=0 odd band, and all t≥1 odd divisibility cases. -/
theorem terminal_high_no_parent
    (n p q s u h : Nat)
    (hn : 257 ≤ n)
    (hp : p = 2^n)
    (hsource : u + q + 1 = 4*p+n)
    (hbelow : q < 2*p)
    (hhigh : 7*p+4*s ≤ 4*q)
    (hs : n+5 ≤ s)
    (hmod : (2*u+5)%9 ≠ 0) :
    ¬ ResetParent h u := by
  have hgap := terminal_high_window n p q s u hn hsource hbelow hhigh hs
  have hpow : 2^(n+1) = 2*p := by
    rw [Nat.pow_succ, ←hp]
    omega
  have hlo : 2^(n+1) < u := by omega
  have hhi : 8*u+32 < 9*2^(n+1) := by omega
  intro hparent
  exact narrow_gap_no_reset_parent (n+1) u h (by omega)
    hlo hhi hmod hparent

/-- Authentic blank-root exclusion for a terminal state satisfying the
    explicit high-band geometry and the full valuation-independent leaf
    criterion. Other odd forks along the actual fatal target's ray remain
    outside this theorem. -/
theorem terminal_high_root_excluded
    (n p q s u : Nat)
    (hn : 257 ≤ n)
    (hp : p = 2^n)
    (hsource : u + q + 1 = 4*p+n)
    (hbelow : q < 2*p)
    (hhigh : 7*p+4*s ≤ 4*q)
    (hs : n+5 ≤ s)
    (hmod : (2*u+5)%9 ≠ 0) :
    ¬ ReachC (2,0) (u,0) := by
  have hgap := terminal_high_window n p q s u hn hsource hbelow hhigh hs
  have hne : u ≠ 2 := by omega
  intro hr
  have hc : ResetChain 2 u := (root_reset_chain_iff u).mp hr
  cases hc with
  | root => exact hne rfl
  | append hchain hparent =>
      exact (terminal_high_no_parent n p q s u _ hn hp hsource hbelow
        hhigh hs hmod) hparent

#print axioms terminal_high_window
#print axioms terminal_high_no_parent
#print axioms terminal_high_root_excluded
end CascadeTerminalHighBand
