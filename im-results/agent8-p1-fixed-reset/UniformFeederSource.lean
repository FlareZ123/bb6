import UnifiedFeederSource
import UniformAny
import ConcreteCorollaries

namespace BB6.Agent8Reset
open BB6.Agent28 BB6.Agent1Quarter BB6.Agent47P1

/-- Under an exact polynomial seed and adjacent-exponent check, a fixed
reset ceiling forbids both the exceptional c=1 and blank-reachable positive
even stopping feeders at every larger critical exponent. -/
theorem source_no_two_feeders_from_seed
    (k n0 n b d m z : Nat)
    (hn0 : 14≤n0) (hn : n0≤n) (hz : z≤k)
    (hcone : CountCone (14*2^n-2*n-16) 3 b d m z)
    (hseed : budget (n0+2) k*(3*budget (n0+2) k+3*n0+8)<7*2^n0)
    (hadj : (n0+3)^(2*4^k)≤2*(n0+2)^(2*4^k))
    (hgate : d=5 ∨
      ∃ t j c : Nat,
        8≤b ∧ b%4=0 ∧ inverseAt b d t = some (j,c) ∧
        2≤j ∧ 2≤c ∧ c%2=0 ∧
        BB6.Agent1.Reach (2*j-4) (c+4)) :
    False := by
  let small := budget (n+2) z
  let big := budget (n+2) k
  have hmono : small ≤ big := budget_mono_count (n+2) z k (by omega) hz
  have hterms : small*(3*small+3*n+8) ≤ big*(3*big+3*n+8) := by
    calc
      _ ≤ small*(3*big+3*n+8) := Nat.mul_le_mul_left small (by omega)
      _ ≤ big*(3*big+3*n+8) := Nat.mul_le_mul_right _ hmono
  have hbig := budget_all_larger_exponents k n0 n hn hseed hadj
  have hsmall : small*(3*small+3*n+8)<7*2^n := by
    change big*(3*big+3*n+8)<7*2^n at hbig
    omega
  exact source_counted_no_low_budget_feeder n b d m z (by omega)
    hcone hsmall hgate

/-- Every genuine critical history reaching either of the specified
two feeder types at exponent n>=1502 has four or more positive-depth resets. -/
theorem source_two_feeders_need_four_resets
    (n b d m : Nat) (hn : 1502≤n)
    (hcone : OddCone (14*2^n-2*n-16) 3 b d m)
    (hgate : d=5 ∨
      ∃ t j c : Nat,
        8≤b ∧ b%4=0 ∧ inverseAt b d t = some (j,c) ∧
        2≤j ∧ 2≤c ∧ c%2=0 ∧
        BB6.Agent1.Reach (2*j-4) (c+4)) :
    ∃ z, CountCone (14*2^n-2*n-16) 3 b d m z ∧ 4≤z := by
  obtain ⟨z,hz⟩ := odd_cone_has_count _ _ b d m hcone
  refine ⟨z,hz,?_⟩
  by_cases hfour : 4≤z
  · exact hfour
  · have hsmall : z≤3 := by omega
    have hseed : budget (1502+2) 3*(3*budget (1502+2) 3+3*1502+8)<
        7*2^1502 := by decide +kernel
    have hadj : (1502+3)^(2*4^3)≤2*(1502+2)^(2*4^3) := by decide +kernel
    exact False.elim (source_no_two_feeders_from_seed
      3 1502 n b d m z (by omega) hn hsmall hz hseed hadj hgate)

#print axioms BB6.Agent8Reset.source_no_two_feeders_from_seed
#print axioms BB6.Agent8Reset.source_two_feeders_need_four_resets
end BB6.Agent8Reset
