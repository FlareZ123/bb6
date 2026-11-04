import SourceBridge
namespace BB6.Agent8Reset
open BB6.Agent28 BB6.Agent1Quarter

/-- A fixed-reset P1 inverse history has cumulative inverse cost below the
critical exponent whenever its exact dyadic defect budget is subexponential.
The source CountCone is the unchanged, genuine inverse cone. -/
theorem source_counted_cost_lt_exponent
    (n b d m z : Nat) (hn : 14 ≤ n)
    (hcone : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hSmall : budget (n+2) z < 2^n) :
    m < n := by
  let K : Nat := 7*2^n-n-3
  have hdom : n+4 ≤ 2^n := source_pow_beats_linear n (by omega)
  have hK : K+n+3 = 7*2^n := by dsimp [K]; omega
  have hroot : (14*2^n-2*n-16)+10 = 2*K := by dsimp [K]; omega
  obtain ⟨D,F,_,_,hpath,_⟩ :=
    source_count_path (14*2^n-2*n-16) K b d m z hroot hcone
  obtain ⟨hi⟩ := path_invariant K z D m F hpath n hK hSmall
  obtain ⟨C,N,hCpos,hCbound,hNpos,hNbound,hF,hRaw,hBudget⟩ := hi
  have hmul : (2:Nat)^m ≤ 2^m*N := by
    have h := Nat.mul_le_mul_left (2^m) hNpos
    simpa only [Nat.mul_one] using h
  have hpow : (2:Nat)^m < 2^n :=
    lt_of_le_of_lt (Nat.le_trans hmul hBudget) hSmall
  by_contra h
  have hnm : n ≤ m := by omega
  have hp : (2:Nat)^n ≤ 2^m := Nat.pow_le_pow_right (by decide) hnm
  omega

#print axioms BB6.Agent8Reset.source_counted_cost_lt_exponent
end BB6.Agent8Reset
