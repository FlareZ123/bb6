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
  have hdom_all : ∀ i : Nat, i+4+4 ≤ 2^(i+4) := by
    intro i
    induction i with
    | zero => decide
    | succ i ih =>
        have hidx : (i+1)+4=(i+4)+1 := by omega
        rw [hidx, Nat.pow_succ]
        omega
  have hidx : (n-4)+4=n := by omega
  have hdom : n+4 ≤ 2^n := by
    simpa only [hidx] using hdom_all (n-4)
  have hK : K+n+3 = 7*2^n := by dsimp [K]; omega
  have hroot : (14*2^n-2*n-16)+10 = 2*K := by dsimp [K]; omega
  obtain ⟨D,F,_,_,hpath,_⟩ :=
    source_count_path (14*2^n-2*n-16) K b d m z hroot hcone
  obtain ⟨hi⟩ := path_invariant K z D m F hpath n hK hSmall
  obtain ⟨C,N,hCpos,hCbound,hNpos,hNbound,hF,hRaw,hBudget⟩ := hi
  have hmul : (2:Nat)^m ≤ 2^m*N := by
    have h := Nat.mul_le_mul_left (2^m) hNpos
    simpa only [Nat.mul_one] using h
  have hpow : (2:Nat)^m < 2^n := by omega
  by_cases hmn : m < n
  · exact hmn
  · have hnle : n ≤ m := by omega
    have hp : (2:Nat)^n ≤ 2^m := Nat.pow_le_pow_right (by decide) hnle
    omega

#print axioms BB6.Agent8Reset.source_counted_cost_lt_exponent
end BB6.Agent8Reset
