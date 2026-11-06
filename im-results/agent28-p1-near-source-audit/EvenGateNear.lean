import RootWallSharpMod4
import NearExceptionalBridge

namespace BB6.Agent28EvenGateNear
open BB6.Agent47P1 BB6.Agent1Quarter BB6.Agent1
open BB6.Agent23RootWall BB6.Agent50Near

private theorem two_n_le_two_pow (n : Nat) (hn : 4 ≤ n) : 2*n ≤ 2^n := by
  have h : ∀ k : Nat, 2*(k+4) ≤ 2^(k+4) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have hp : 2^((k+1)+4) = 2*2^(k+4) := by
        rw [show (k+1)+4=(k+4)+1 by omega, Nat.pow_succ]
        omega
      omega
  have hrep : (n-4)+4=n := by omega
  simpa only [hrep] using h (n-4)

private theorem oddcone_to_source_count
    (b0 d0 b d m : Nat) (h : OddCone b0 d0 b d m) :
    ∃ z, BB6.Agent50Density.CountCone b0 d0 b d m z := by
  induction h with
  | root => exact ⟨0,BB6.Agent50Density.CountCone.root⟩
  | parent b d m t k c hprev hb hb4 hd hi hk hc ih =>
    obtain ⟨z,hz⟩ := ih
    exact ⟨z+(if t=0 then 0 else 1),
      BB6.Agent50Density.CountCone.parent b d m z t k c hz hb hb4 hd hi hk hc⟩

/-- All original P1 critical positive-even source exits which are truly
    blank reachable require a near-exponent number of inverse resets,
    irrespective of whether their cost reaches the exponential sector. -/
theorem authentic_even_exit_needs_near_resets
    (n b d m t k c : Nat) (hn : 14 ≤ n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hb : 8≤b) (hmod : b%4=0) (hd : d%2=1)
    (hinv : inverseAt b d t = some (k,c))
    (hc : 2≤c) (hceven : c%2=0) (hk : 2≤k)
    (hr : Reach (2*k-4) (c+4)) :
    ∃ z, BB6.Agent50Density.CountCone (14*2^n-2*n-16) 3 b d m z ∧
      n ≤ (2*z+2)*BB6.Agent50Extended.L n := by
  have hsharp := authentic_critical_root_sharp_mod4
    n b d m t k c hn hcone hb hmod hd hinv hc hceven hk hr
  rcases hsharp with hlarge | ⟨_, hwall, _⟩
  · have hdoub := two_n_le_two_pow n (by omega)
    have hpower : 28*n ≤ 14*2^n := by
      calc
        28*n = 14*(2*n) := by omega
        _ ≤ 14*2^n := Nat.mul_le_mul_left 14 hdoub
    have hm : n ≤ m := by
      by_cases hmcase : n ≤ m
      · exact hmcase
      · have hsmall : m<n := by omega
        omega
    obtain ⟨z,hcnt⟩ := oddcone_to_source_count _ _ _ _ _ hcone
    let K : Nat := 7*2^n-n-3
    have hdom : n+4 ≤ 2^n := by omega
    have hK : K+n+3=7*2^n := by dsimp [K]; omega
    have hroot : (14*2^n-2*n-16)+10=2*K := by dsimp [K]; omega
    have hbound := source_countcone_near_n_reset_bound
      n K (14*2^n-2*n-16) b d m z hn hK hroot hcnt
      (by omega)
    exact ⟨z,hcnt,hbound⟩
  · exact source_critical_wall_reset_near n b d m hn hcone (by omega)

/-- The two authenticated P1 critical exit forms, exceptional d=5 and
    blank-reachable even inverse source, satisfy one reset-count bound. -/
theorem authentic_even_or_exceptional_needs_near_resets
    (n b d m : Nat) (hn : 14 ≤ n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hgate : d=5 ∨
      ∃ t k c, 8≤b ∧ b%4=0 ∧ d%2=1 ∧
        inverseAt b d t=some (k,c) ∧ 2≤c ∧ c%2=0 ∧
        2≤k ∧ Reach (2*k-4) (c+4)) :
    ∃ z, BB6.Agent50Density.CountCone (14*2^n-2*n-16) 3 b d m z ∧
      n ≤ (2*z+2)*BB6.Agent50Extended.L n := by
  rcases hgate with hd5 | ⟨t,k,c,hb,hb4,hd,hi,hc,he,hk,hr⟩
  · exact source_critical_exceptional_reset_near n b d m hn hcone hd5
  · exact authentic_even_exit_needs_near_resets
      n b d m t k c hn hcone hb hb4 hd hi hc he hk hr

#print axioms BB6.Agent28EvenGateNear.authentic_even_exit_needs_near_resets
#print axioms BB6.Agent28EvenGateNear.authentic_even_or_exceptional_needs_near_resets
end BB6.Agent28EvenGateNear
