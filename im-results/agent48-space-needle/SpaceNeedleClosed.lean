import BusyBeaver.BB6.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
import Lean.Elab.Tactic.Omega

namespace BB6.Agent48.SpaceNeedle
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

def haltTower : Nat → Nat
  | 0 => 0
  | k+1 => 2*(haltTower k+1)

def oddTower (q : Nat) : Nat → Nat
  | 0 => 2*q+1
  | k+1 => 2*(oddTower q k+1)

/-- For any k, the collapsed even sweep reaches the halt on the exact
power-of-two family d+2=2^(k+1). -/
theorem scan_haltTower (k b : Nat) : scanEven (haltTower k) b = none := by
  induction k generalizing b with
  | zero => simp [haltTower,scanEven]
  | succ k ih =>
      change scanEven (2*(haltTower k+1)) b = none
      have he : 2*(haltTower k+1) ≠ 0 := by omega
      have hx : (2*(haltTower k+1))/2-1 = haltTower k := by omega
      rw [scanEven]
      simp only [Nat.mul_mod_right, ite_true, if_neg he]
      rw [hx]
      exact ih _

/-- Every odd-tail branch has a closed exact output after k halving steps. -/
theorem scan_oddTower (q k b : Nat) :
    scanEven (oddTower q k) b =
      some (.N (b+oddTower q k+k+3*(q+1))) := by
  induction k generalizing b with
  | zero =>
      cases q with
      | zero => simp [oddTower,scanEven]
      | succ q => simp [oddTower,scanEven]; omega
  | succ k ih =>
      have he : 2*(oddTower q k+1) ≠ 0 := by omega
      have hx : (2*(oddTower q k+1))/2-1 = oddTower q k := by omega
      change scanEven (2*(oddTower q k+1)) b =
        some (.N (b+(2*(oddTower q k+1))+(k+1)+3*(q+1)))
      rw [scanEven]
      simp only [Nat.mul_mod_right, ite_true, if_neg he]
      rw [hx,ih]
      have hd : 2*(oddTower q k+1)/2 = oddTower q k+1 := by omega
      rw [hd]
      simp only [Option.some.injEq, HighLevelState.N.injEq]
      omega

/-- Exact arithmetic size of each halting-tower counter. -/
theorem haltTower_power (k : Nat) : haltTower k+2 = 2^(k+1) := by
  induction k with
  | zero => decide
  | succ k ih =>
      change 2*(haltTower k+1)+2=2^(k+1+1)
      rw [Nat.pow_succ']
      omega

/-- Exact factorization of every nonhalting odd-tail counter. -/
theorem oddTower_factor (q k : Nat) :
    oddTower q k + 2 = 2^k * (2*q+3) := by
  induction k with
  | zero => simp [oddTower]
  | succ k ih =>
      change 2*(oddTower q k+1)+2=2^(k+1)*(2*q+3)
      rw [Nat.pow_succ']
      rw [Nat.mul_assoc]
      omega

/-- Every natural counter splits into a power-of-two halting tower or a
nonhalting odd-tail tower. This is a complete integer partition. -/
theorem classify_d (d : Nat) :
    (∃ k, d = haltTower k) ∨ (∃ q k, d = oddTower q k) := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
      by_cases hz : d = 0
      · left
        exact ⟨0, by simp [hz, haltTower]⟩
      by_cases he : d % 2 = 0
      · have hl : d/2-1 < d := by omega
        rcases ih (d/2-1) hl with ⟨k,hk⟩ | ⟨q,k,hq⟩
        · left
          refine ⟨k+1, ?_⟩
          simp only [haltTower]
          omega
        · right
          refine ⟨q,k+1, ?_⟩
          simp only [oddTower]
          omega
      · right
        refine ⟨d/2,0, ?_⟩
        simp only [oddTower]
        omega

/-- Complete finite symbolic decision of any single high-level scan: the
power-of-two tower halts; otherwise the positive drift is exactly given. -/
theorem scanEven_classification (d b : Nat) :
    (∃ k, d=haltTower k ∧ scanEven d b=none) ∨
    (∃ q k, d=oddTower q k ∧
       scanEven d b=some (.N (b+d+k+3*(q+1)))) := by
  rcases classify_d d with ⟨k,hk⟩ | ⟨q,k,hq⟩
  · left
    exact ⟨k,hk,by rw [hk]; exact scan_haltTower k b⟩
  · right
    exact ⟨q,k,hq,by rw [hq]; exact scan_oddTower q k b⟩

/-- A complete arithmetic characterization of the exact stopping set. -/
theorem scanEven_none_iff (d b : Nat) :
    scanEven d b = none ↔ ∃ k, d=haltTower k := by
  constructor
  · intro hn
    rcases classify_d d with ⟨k,hk⟩ | ⟨q,k,hq⟩
    · exact ⟨k,hk⟩
    · rw [hq, scan_oddTower] at hn
      contradiction
  · rintro ⟨k,hk⟩
    rw [hk]
    exact scan_haltTower k b

/-- A strict monotonicity property on every surviving high-level return. -/
theorem scanEven_strict (d b e : Nat)
    (h : scanEven d b = some (.N e)) : d < e := by
  rcases classify_d d with ⟨k,hk⟩ | ⟨q,k,hq⟩
  · rw [hk,scan_haltTower] at h
    contradiction
  · rw [hq,scan_oddTower] at h
    cases h
    omega

/-- The published single-counter high-level successor is strictly increasing
whenever it is defined, excluding every nontrivial directed cycle. -/
theorem highLevelNext_strict (d e : Nat)
    (h : highLevelNext (.N d) = some (.N e)) : d<e := by
  exact scanEven_strict d 0 e h

/-- All successful one-counter successors have an explicit inverse parameterization. -/
theorem highLevelNext_iff_oddTower (d e : Nat) :
    highLevelNext (.N d) = some (.N e) ↔
      ∃ q k, d = oddTower q k ∧ e = d+k+3*(q+1) := by
  constructor
  · intro hn
    rcases classify_d d with ⟨k,hk⟩ | ⟨q,k,hq⟩
    · rw [hk] at hn
      have hno := scan_haltTower k 0
      simp only [highLevelNext] at hn
      rw [hno] at hn
      contradiction
    · have he : e = d+k+3*(q+1) := by
        change scanEven d 0=some (.N e) at hn
        rw [hq,scan_oddTower] at hn
        simp only [Option.some.injEq, HighLevelState.N.injEq] at hn
        omega
      exact ⟨q,k,hq,he⟩
  · rintro ⟨q,k,rfl,rfl⟩
    simpa [highLevelNext] using scan_oddTower q k 0

/-- Powers of two modulo seven avoid the residue three. -/
theorem pow_two_mod_seven (k : Nat) :
    2^k % 7 = 1 ∨ 2^k % 7 = 2 ∨ 2^k % 7 = 4 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.pow_succ']
      have hm : (2 * 2^k)%7 = (2*((2^k)%7))%7 := by
        simp [Nat.mul_mod]
      rw [hm]
      rcases ih with h|h|h
      · rw [h]; decide
      · rw [h]; decide
      · rw [h]; decide

/-- No terminal tower can be entered from a state whose d+2 has exactly
one factor of two. This is a uniform infinite-source exclusion. -/
theorem no_one_halving_into_power (q k : Nat) :
    highLevelNext (.N (oddTower q 1)) ≠ some (.N (haltTower k)) := by
  intro h
  change scanEven (oddTower q 1) 0 = some (.N (haltTower k)) at h
  rw [scan_oddTower] at h
  have he : haltTower k = oddTower q 1 + 1 + 3*(q+1) := by
    simp only [Option.some.injEq, HighLevelState.N.injEq] at h
    omega
  have hodd : oddTower q 1 = 4*q+4 := by simp [oddTower]; omega
  have hp := haltTower_power k
  have hx : 2^(k+1)=7*q+10 := by omega
  have hm : 2^(k+1)%7 = 3 := by rw [hx]; omega
  rcases pow_two_mod_seven (k+1) with h1 | h2 | h3 <;> omega

/-- Exact Diophantine test for a one-step predecessor of any terminal tower.
The right side is suitable for modular inverse sieving. -/
theorem predecessor_power_identity (q v k : Nat) :
    highLevelNext (.N (oddTower q v)) = some (.N (haltTower k)) ↔
      2^(k+2)+3 = (2^(v+1)+3)*(2*q+3)+2*v := by
  change scanEven (oddTower q v) 0 = some (.N (haltTower k)) ↔ _
  rw [scan_oddTower]
  simp only [Option.some.injEq, HighLevelState.N.injEq, Nat.zero_add]
  have hodd := oddTower_factor q v
  have hhalt := haltTower_power k
  have hcoef : (2^(v+1)+3)*(2*q+3) =
      2*(2^v*(2*q+3))+3*(2*q+3) := by
    rw [Nat.pow_succ', Nat.add_mul, Nat.mul_assoc]
  have hp : 2^(k+2)=2*2^(k+1) := by rw [Nat.pow_succ']
  rw [hcoef, hp]
  omega

/-- A generic modular obstruction: any odd modulus relatively prime to two
which divides the candidate denominator, while forcing the valuation
correction to be three, rules out every predecessor of a terminal power. -/
theorem no_common_modulus_into_power (q v k m : Nat)
    (hgt : 1 < m) (hc : Nat.Coprime m 2)
    (hden : m ∣ 2^(v+1)+3)
    (hv : ∃ t, 2*v=3+m*t) :
    highLevelNext (.N (oddTower q v)) ≠ some (.N (haltTower k)) := by
  intro h
  have heq := (predecessor_power_identity q v k).mp h
  rcases hden with ⟨r, hr⟩
  rcases hv with ⟨t, ht⟩
  rw [hr, ht] at heq
  have hcalc : (m*r)*(2*q+3)+(3+m*t) = m*(r*(2*q+3)+t)+3 := by
    simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [hcalc] at heq
  have hpow : 2^(k+2)=m*(r*(2*q+3)+t) := by omega
  have hdiv : m ∣ 2^(k+2) := ⟨r*(2*q+3)+t, hpow⟩
  have hcopow : Nat.Coprime m (2^(k+2)) := hc.pow_right (k+2)
  have hmone : m=1 := hcopow.eq_one_of_dvd hdiv
  omega

/-- Powers of two modulo five never vanish. -/
theorem pow_two_mod5_cases (n : Nat) :
    2^n % 5 = 1 ∨ 2^n % 5 = 2 ∨ 2^n % 5 = 4 ∨ 2^n % 5 = 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.pow_succ']
      have hm : (2*2^n)%5 = (2*((2^n)%5))%5 := by simp [Nat.mul_mod]
      rw [hm]
      rcases ih with h|h|h|h
      · rw [h]; decide
      · rw [h]; decide
      · rw [h]; decide
      · rw [h]; decide

theorem pow_two_mod5_four_k_plus_one (k : Nat) :
  (2^(4*k+1))%5=2 := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [show 4*(k+1)+1=(4*k+1)+4 by omega, Nat.pow_add]
      have hmul : (2^(4*k+1)*2^4)%5 = ((2^(4*k+1))%5*(2^4%5))%5 := by
        exact Nat.mul_mod _ _ _
      rw [hmul,ih]
      all_goals decide

/-- An infinite arithmetic progression of 2-adic input valuations cannot
lead directly into any terminal power-of-two counter. -/
theorem no_20t_plus_4_halving_into_power (q k t : Nat) :
    highLevelNext (.N (oddTower q (20*t+4))) ≠
      some (.N (haltTower k)) := by
  intro h
  let v := 20*t+4
  have heq := (predecessor_power_identity q v k).mp h
  have hvexp : v+1 = 4*(5*t+1)+1 := by dsimp [v]; omega
  have hpow : (2^(v+1))%5=2 := by
    rw [hvexp]
    exact pow_two_mod5_four_k_plus_one (5*t+1)
  have hden : (2^(v+1)+3)%5=0 := by omega
  have hmul : ((2^(v+1)+3)*(2*q+3))%5=0 := by
    rw [Nat.mul_mod,hden]
    simp
  have hv : (2*v)%5=3 := by dsimp [v]; omega
  have hrem : (2^(k+2))%5=0 := by omega
  rcases pow_two_mod5_cases (k+2) with h1|h2|h3|h4 <;> omega

/-- The 3-step multiplicative period of the powers of two modulo seven. -/
theorem pow_two_mod7_three_k_plus_two (k : Nat) :
    2^(3*k+2)%7=4 := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [show 3*(k+1)+2=(3*k+2)+3 by omega, Nat.pow_add]
      have hmul : (2^(3*k+2)*2^3)%7 = ((2^(3*k+2))%7*(2^3%7))%7 := by
        exact Nat.mul_mod _ _ _
      rw [hmul,ih]
      all_goals decide

/-- A second infinite family of forbidden immediate predecessors of any
terminal power-of-two counter, from a 7-divisibility obstruction. -/
theorem no_21t_plus_19_halving_into_power (q k t : Nat) :
    highLevelNext (.N (oddTower q (21*t+19))) ≠
      some (.N (haltTower k)) := by
  intro h
  let v := 21*t+19
  have heq := (predecessor_power_identity q v k).mp h
  have hvexp : v+1 = 3*(7*t+6)+2 := by dsimp [v]; omega
  have hpow : (2^(v+1))%7=4 := by
    rw [hvexp]
    exact pow_two_mod7_three_k_plus_two (7*t+6)
  have hden : (2^(v+1)+3)%7=0 := by omega
  have hmul : ((2^(v+1)+3)*(2*q+3))%7=0 := by
    rw [Nat.mul_mod,hden]
    simp
  have hv : (2*v)%7=3 := by dsimp [v]; omega
  have hrem : (2^(k+2))%7=0 := by omega
  rcases pow_two_mod_seven (k+2) with h1|h2|h3 <;> omega

#print axioms scan_haltTower
#print axioms scan_oddTower
#print axioms haltTower_power
#print axioms oddTower_factor
#print axioms classify_d
#print axioms scanEven_classification
#print axioms scanEven_none_iff
#print axioms scanEven_strict
#print axioms no_common_modulus_into_power
#print axioms highLevelNext_strict
#print axioms highLevelNext_iff_oddTower
#print axioms pow_two_mod_seven
#print axioms no_one_halving_into_power
#print axioms predecessor_power_identity
#print axioms pow_two_mod5_cases
#print axioms pow_two_mod5_four_k_plus_one
#print axioms no_20t_plus_4_halving_into_power
#print axioms pow_two_mod7_three_k_plus_two
#print axioms no_21t_plus_19_halving_into_power
end BB6.Agent48.SpaceNeedle
