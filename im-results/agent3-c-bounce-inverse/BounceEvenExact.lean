import EvenTargetForward
import BounceInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

private theorem invLiftK_even (K n : Nat) (hk : K%2=0) :
    (invLiftK K n)%2=0 := by
  induction n generalizing K with
  | zero => simpa [invLiftK] using hk
  | succ n ih =>
    simpa only [invLiftK] using ih (2*K+4) (by omega)

/-- All even-counter bounce outputs y>=5 are exactly characterized by
    one shared recursion depth and two affine/exponential equations.
    The inverse direction constructs a genuine arbitrarily deep path. -/
theorem bounce_even_output_sufficient (K c x y n : Nat)
    (hk : K%2=0) (hy : 5≤y)
    (hs : x+y+1=2^n*(2*K+8))
    (hc : c+(2*K+8)+3*n=x+2*y+2) :
    (bounce K c).2=some (x,y) := by
  have hpow : 2^(n+1)*(K+4)=x+y+1 := by
    calc
      2^(n+1)*(K+4)=2^n*2*(K+4) := by rw [Nat.pow_succ]
      _ = 2^n*(2*(K+4)) := by ac_rfl
      _ = 2^n*(2*K+8) := by congr 1 <;> omega
      _ = x+y+1 := hs.symm
  have hin : invLiftC K n y=c := by
    have hh := invLiftC_closed K n y
    rw [hpow] at hh
    omega
  rw [←hin]
  rw [bounce_inv_lift K n y hk hy]
  have hke := invLiftK_even K n hk
  have hz : 2*(invLiftK K n)+8=2^n*(2*K+8) := by
    have hsK := invLiftK_closed K n
    calc
      2*(invLiftK K n)+8 = 2*(2^n*(K+4)) := by omega
      _ = 2^n*(2*(K+4)) := by ac_rfl
      _ = 2^n*(2*K+8) := by congr 1 <;> omega
  have htail : y+1≤2*(invLiftK K n)+8 := by omega
  rw [bounce_inv_direct (invLiftK K n) y hke hy htail]
  have hx : 2*(invLiftK K n)+8-(y+1)=x := by omega
  simp [hx]

/-- An exact bidirectional symbolic solver for every successful even
    bounce with output y>=5, with no recursion-depth truncation. -/
theorem bounce_even_output_exact (K c x y : Nat)
    (hk : K%2=0) (hy : 5≤y) :
    (bounce K c).2=some (x,y) ↔
      ∃ n : Nat, x+y+1=2^n*(2*K+8) ∧
        c+(2*K+8)+3*n=x+2*y+2 := by
  constructor
  · exact bounce_even_output_invariants c K x y hk (by omega)
  · rintro ⟨n,hs,hc⟩
    exact bounce_even_output_sufficient K c x y n hk hy hs hc

#print axioms bounce_even_output_sufficient
#print axioms bounce_even_output_exact
end BB6.Agent46
