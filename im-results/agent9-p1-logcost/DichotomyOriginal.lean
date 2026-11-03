import CostOriginal
import DichotomyArithmetic

namespace BB6.Agent9Dichotomy
open BB6.Agent47P1
open BB6.Agent1Quarter
open BB6.Agent45TwoRoot
open BB6.Agent1ShortCone
open BB6.Agent1Bottleneck

/-- Genuine blank-reachable even-right P1 inverse exits from either
authenticated q-sector feeder must be exponentially deep or meet a
specific depth-one affine wall. -/
theorem authentic_reachable_even_exponential_or_wall
    (q b d m t k c : Nat) (root : Bool)
    (hq : 1 ≤ q)
    (hcone : OddCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m)
    (hb : 8 ≤ b) (hb4 : b%4=0) (hdodd : d%2=1)
    (hi : inverseAt b d t = some (k,c))
    (hceven : c%2=0) (hk : 2 ≤ k)
    (hreach : BB6.Agent1.Reach (2*k-4) (c+4)) :
    8*2^(16*q) ≤ m ∨
      (t=1 ∧ (if root then b=4*m+64*q+12 else b=4*m+64*q+16)) := by
  let u := u2 q
  have hdom := pow16_dom q hq
  have hu : u+4*q+3=7*2^(16*q) := by dsimp [u,u2]; omega
  have hPgrowth : 256*q ≤ 2^(8*q) := growth q hq
  have hPpower : 2^(8*q) ≤ 2^(16*q) :=
    Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (by omega)
  have hP : 256*q ≤ 2^(16*q) := Nat.le_trans hPgrowth hPpower
  have hinverse := inverseAt_power b d t k c hi
  have hcost0 := inverseAt_exact_mass b d t k c (by omega) hb4 hdodd hi
  have hcost : 2*k+c+2*t+1=b+d := by omega
  have hxmod : (2*k-4)%2=0 := by omega
  have hcpositive : 0<c+4 := by omega
  have hce : (c+4)%2=0 := by omega
  obtain ⟨j,hpower0⟩ := BB6.Agent1.even_left_power_shape
    (2*k-4) (c+4) hreach hxmod hcpositive hce
  have hpower : 2*k+8 = 14*2^j := by omega
  cases root with
  | false =>
    have hcone' : OddCone (6*u-2) (2*u+5) b d m := by
      simpa [u] using hcone
    have hmass0 := odd_cone_mass (6*u-2) (2*u+5) b d m hcone'
    have hmass : b+d+2*m=8*u+3 := by omega
    have he : 3=3 ∨ 3=5 := Or.inl rfl
    have htbound := inverse_depth_le q u b d m t c 3 hu he hmass hinverse
    rcases even_terminal_exponential_or_wall
      q u 3 b d m t k c j hq he hu hmass hb4 hdodd hceven
      hinverse hcost hpower htbound hP with hlarge | ⟨hone,hwall⟩
    · exact Or.inl hlarge
    · right
      refine ⟨hone, ?_⟩
      simpa using (by rcases hwall with h | h <;> omega : b=4*m+64*q+16)
  | true =>
    have hcone' : OddCone (4*u-4) (4*u+9) b d m := by
      simpa [u] using hcone
    have hmass0 := odd_cone_mass (4*u-4) (4*u+9) b d m hcone'
    have hmass : b+d+2*m=8*u+5 := by omega
    have he : 5=3 ∨ 5=5 := Or.inr rfl
    have htbound := inverse_depth_le q u b d m t c 5 hu he hmass hinverse
    rcases even_terminal_exponential_or_wall
      q u 5 b d m t k c j hq he hu hmass hb4 hdodd hceven
      hinverse hcost hpower htbound hP with hlarge | ⟨hone,hwall⟩
    · exact Or.inl hlarge
    · right
      refine ⟨hone, ?_⟩
      simpa using (by rcases hwall with h | h <;> omega : b=4*m+64*q+12)

theorem authentic_low_cost_even_exact_shape
    (q b d m t k c : Nat) (root : Bool)
    (hq : 1 ≤ q)
    (hcone : OddCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m)
    (hb : 8 ≤ b) (hb4 : b%4=0) (hdodd : d%2=1)
    (hi : inverseAt b d t = some (k,c))
    (hceven : c%2=0) (hk : 2 ≤ k)
    (hreach : BB6.Agent1.Reach (2*k-4) (c+4))
    (hlow : m < 8*2^(16*q)) :
    t=1 ∧ 2*k+8=28*2^(16*q) ∧
      (if root then c+4+2*m+32*q+10=28*2^(16*q)
       else c+4+2*m+32*q+12=28*2^(16*q)) := by
  have hdich := authentic_reachable_even_exponential_or_wall
    q b d m t k c root hq hcone hb hb4 hdodd hi hceven hk hreach
  rcases hdich with hlarge | ⟨ht,hw⟩
  · omega
  have hpower := inverseAt_power b d t k c hi
  have hinverse1 : d+b/2+3=2*(c+3) := by
    simpa [ht] using hpower
  have hcost0 := inverseAt_exact_mass b d t k c (by omega) hb4 hdodd hi
  have hcost : 2*k+c+3=b+d := by omega
  let u := u2 q
  have hdom := pow16_dom q hq
  have hu : u+4*q+3=7*2^(16*q) := by dsimp [u,u2]; omega
  refine ⟨ht, ?_, ?_⟩
  cases root with
  | false =>
    have hcone' : OddCone (6*u-2) (2*u+5) b d m := by
      simpa [u] using hcone
    have hmass0 := odd_cone_mass (6*u-2) (2*u+5) b d m hcone'
    have hmass : b+d+2*m=8*u+3 := by omega
    simp only [Bool.false_eq_true, ↓reduceIte] at hw ⊢
    constructor <;> omega
  | true =>
    have hcone' : OddCone (4*u-4) (4*u+9) b d m := by
      simpa [u] using hcone
    have hmass0 := odd_cone_mass (4*u-4) (4*u+9) b d m hcone'
    have hmass : b+d+2*m=8*u+5 := by omega
    simp only [↓reduceIte] at hw ⊢
    constructor <;> omega

#print axioms authentic_low_cost_even_exact_shape

#print axioms authentic_reachable_even_exponential_or_wall
end BB6.Agent9Dichotomy
