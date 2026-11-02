import Std
namespace SheepEvenBound

/-- A verified exponential-versus-linear dominance bound persists at later exponents. -/
theorem growth (D K C n0 n : Nat) (hK : 1 ≤ K)
    (h0 : K*2^n0 > D*(n0+3)+C)
    (hp : 2^n0 > 2*D)
    (hn : n0 ≤ n) :
    K*2^n > D*(n+3)+C ∧ 2^n > 2*D := by
  have hall (q : Nat) :
      K*2^(n0+q) > D*(n0+q+3)+C ∧ 2^(n0+q)>2*D := by
    induction q with
    | zero => simpa using And.intro h0 hp
    | succ q ih =>
      have hpows : 2^(n0+(q+1))=2*2^(n0+q) := by
        have he : n0+(q+1)=(n0+q)+1 := by omega
        rw [he, Nat.pow_succ]
        omega
      have hpowsK : K*2^(n0+(q+1))=2*(K*2^(n0+q)) := by
        rw [hpows]
        calc
          K*(2*2^(n0+q)) = (K*2)*2^(n0+q) := by rw [Nat.mul_assoc]
          _=(2*K)*2^(n0+q) := by rw [Nat.mul_comm K 2]
          _=2*(K*2^(n0+q)) := by rw [Nat.mul_assoc]
      have hmult : 2^(n0+q) ≤ K*2^(n0+q) :=
        by simpa using Nat.mul_le_mul_right (2^(n0+q)) hK
      constructor
      · have hlin : D*(n0+(q+1)+3)=D*(n0+q+3)+D := by
          have he : n0+(q+1)+3=(n0+q+3)+1 := by omega
          rw [he, Nat.mul_add]
          simp
        rw [hpowsK,hlin]
        omega
      · rw [hpows]
        omega
  have hrep : n=n0+(n-n0) := by omega
  rw [hrep]
  exact hall (n-n0)

#print axioms growth
end SheepEvenBound
