import NeedleCancelMod35
import Lean.Elab.Tactic.Omega

namespace CancellationValuationSieve
open NeedleCancelMod35

/-- Four residue classes modulo 20 of valuation positions can never occur
    on an incoming cancellation-feeder edge, for any positive feeder index. -/
theorem no_parent_mod5 (r t q : Nat) (hr : 1 ≤ r)
    (ht4 : t % 4 = 0) (ht5 : t % 5 ≠ 4) :
    sourceB r ≠ (2^(t+1)+3)*q + (3*2^t+t+3) := by
  have hpow : 2^t%5=1 := by
    have he : t=4*(t/4) := by omega
    rw [he, Nat.pow_mul, Nat.pow_mod, show (2:Nat)^4%5=1 by decide]
    simp
  have hps : 2^(t+1)%5=2 := by
    rw [Nat.pow_succ, Nat.mul_mod, hpow]
  have hd : (2^(t+1)+3)%5=0 := by omega
  have hc : (3*2^t+t+3)%5=(t+1)%5 := by omega
  have hb := B_mod5 r hr
  intro h
  have hm := congrArg (fun z:Nat => z%5) h
  rw [Nat.add_mod, Nat.mul_mod, hd, hc] at hm
  omega

/-- Twelve further valuation classes modulo 21 have no genuine incoming
    edges at any cancellation feeder, by its exact residue-three cycle. -/
theorem no_parent_mod7 (r t q : Nat) (hr : 1 ≤ r)
    (ht3 : t % 3 = 1) (ht7 : t % 7 ≤ 3) :
    sourceB r ≠ (2^(t+1)+3)*q + (3*2^t+t+3) := by
  have hpow : 2^t%7=2 := by
    have he : t=3*(t/3)+1 := by omega
    rw [he, Nat.pow_add, Nat.mul_mod]
    have hh : 2^(3*(t/3))%7=1 := by
      rw [Nat.pow_mul, Nat.pow_mod, show (2:Nat)^3%7=1 by decide]
      simp
    rw [hh]
  have hps : 2^(t+1)%7=4 := by
    rw [Nat.pow_succ, Nat.mul_mod, hpow]
  have hd : (2^(t+1)+3)%7=0 := by omega
  have hc : (3*2^t+t+3)%7=(t+2)%7 := by omega
  have hcases := sourceB_mod35_full r hr
  have hrest : r%3=0 ∨ r%3=1 ∨ r%3=2 := by omega
  have hb : sourceB r%7=0 ∨ sourceB r%7=1 ∨ sourceB r%7=6 := by
    rcases hrest with z|z|z
    · have h := hcases.1 z
      omega
    · have h := hcases.2.1 z
      omega
    · have h := hcases.2.2 z
      omega
  intro h
  have hm := congrArg (fun z:Nat => z%7) h
  rw [Nat.add_mod, Nat.mul_mod, hd, hc] at hm
  omega

#print axioms no_parent_mod5
#print axioms no_parent_mod7
end CancellationValuationSieve
