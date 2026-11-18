import Lean.Elab.Tactic.Omega

namespace Marker1TerminalArithmetic

def v2 : Nat → Nat
  | 0 => 0
  | n+1 => if (n+1) % 2 = 0 then 1 + v2 ((n+1) / 2) else 0
termination_by n => n
decreasing_by
  apply Nat.div_lt_self
  · omega
  · omega

def popCount : Nat → Nat
  | 0 => 0
  | n+1 => (n+1) % 2 + popCount ((n+1) / 2)
termination_by n => n
decreasing_by
  apply Nat.div_lt_self
  · omega
  · omega

def sumV2 : Nat → Nat
  | 0 => 0
  | n+1 => v2 (n+1) + sumV2 n

theorem v2_odd (n : Nat) (h : n % 2 ≠ 0) : v2 n = 0 := by
  cases n with
  | zero => omega
  | succ n => simp [v2, h]

theorem v2_even (n : Nat) (hn : 0 < n) (h : n % 2 = 0) :
    v2 n = 1 + v2 (n/2) := by
  cases n with
  | zero => omega
  | succ n => simp [v2, h]

theorem popCount_even (k : Nat) : popCount (2*k) = popCount k := by
  cases k with
  | zero => simp [popCount]
  | succ k =>
      have hidx : 2*(k+1) = (2*k+1)+1 := by omega
      have hmod : (2*k+2) % 2 = 0 := by omega
      have hdiv : (2*k+2) / 2 = k+1 := by omega
      rw [hidx]
      simp [popCount, hmod, hdiv]

theorem popCount_odd (k : Nat) : popCount (2*k+1) = 1 + popCount k := by
  have hidx : 2*k+1 = (2*k)+1 := by omega
  have hmod : (2*k+1) % 2 = 1 := by omega
  have hdiv : (2*k+1) / 2 = k := by omega
  rw [hidx]
  simp [popCount, hmod, hdiv]

theorem sumV2_even (k : Nat) : sumV2 (2*k) = k + sumV2 k := by
  induction k with
  | zero => simp [sumV2]
  | succ k ih =>
      have hodd : v2 (2*k+1) = 0 := v2_odd (2*k+1) (by omega)
      have heven : v2 (2*k+2) = 1 + v2 (k+1) := by
        have hdiv : (2*k+2)/2 = k+1 := by omega
        rw [v2_even (2*k+2) (by omega) (by omega), hdiv]
      calc
        sumV2 (2*(k+1)) = v2 (2*k+2) + sumV2 (2*k+1) := by
          have hidx : 2*(k+1) = (2*k+1)+1 := by omega
          rw [hidx, sumV2]
        _ = (1 + v2 (k+1)) + (v2 (2*k+1) + sumV2 (2*k)) := by
          rw [heven, sumV2]
        _ = (k+1) + sumV2 (k+1) := by
          rw [hodd, ih]
          simp [sumV2]
          omega

theorem sumV2_odd (k : Nat) : sumV2 (2*k+1) = sumV2 (2*k) := by
  simp [sumV2, v2_odd (2*k+1) (by omega)]

theorem sumV2_add_popCount (n : Nat) : sumV2 n + popCount n = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases hn0 : n = 0
      · subst n
        simp [sumV2, popCount]
      · rcases Nat.mod_two_eq_zero_or_one n with hEven | hOdd
        · let k := n/2
          have hn : n = 2*k := by dsimp [k]; omega
          have hk : k < n := by dsimp [k]; omega
          have hrec := ih k hk
          rw [hn]
          change sumV2 (2*k) + popCount (2*k) = 2*k
          rw [sumV2_even, popCount_even]
          omega
        · let k := n/2
          have hn : n = 2*k+1 := by dsimp [k]; omega
          have hk : k < n := by dsimp [k]; omega
          have hrec := ih k hk
          rw [hn]
          change sumV2 (2*k+1) + popCount (2*k+1) = 2*k+1
          rw [sumV2_odd, sumV2_even, popCount_odd]
          omega

theorem popCount_pow2_sub_one (b : Nat) : popCount (2^b-1) = b := by
  induction b with
  | zero => simp [popCount]
  | succ b ih =>
      have hpowBase : 2^(b+1) = 2*2^b := by
        rw [Nat.pow_succ]
        exact Nat.mul_comm (2^b) 2
      have hpow : 2^(b+1)-1 = 2*(2^b-1)+1 := by
        rw [hpowBase]
        have hp0 : 0 < 2^b := Nat.pow_pos (by decide)
        have hp : 1 ≤ 2^b := by omega
        omega
      rw [hpow]
      change popCount (2*(2^b-1)+1) = b+1
      rw [popCount_odd, ih]
      exact Nat.add_comm 1 b

theorem popCount_pow2_sub_two (b : Nat) : popCount (2^b-2) = b-1 := by
  cases b with
  | zero => simp [popCount]
  | succ b =>
      have hpowBase : 2^(b+1) = 2*2^b := by
        rw [Nat.pow_succ]
        exact Nat.mul_comm (2^b) 2
      have hpow : 2^(b+1)-2 = 2*(2^b-1) := by
        rw [hpowBase]
        have hp0 : 0 < 2^b := Nat.pow_pos (by decide)
        have hp : 1 ≤ 2^b := by omega
        omega
      rw [hpow]
      change popCount (2*(2^b-1)) = (b+1)-1
      rw [popCount_even, popCount_pow2_sub_one]
      omega

theorem popCount_shift_low_ones (x a : Nat) :
    popCount (x*2^a + (2^a-1)) = popCount x + a := by
  induction a with
  | zero => simp
  | succ a ih =>
      have hpow : 2^(a+1) = 2*2^a := by
        rw [Nat.pow_succ]
        exact Nat.mul_comm (2^a) 2
      have hmul : x*(2*2^a) = 2*(x*2^a) := by
        calc
          x*(2*2^a) = (x*2)*2^a := by rw [Nat.mul_assoc]
          _ = (2*x)*2^a := by rw [Nat.mul_comm x 2]
          _ = 2*(x*2^a) := by rw [← Nat.mul_assoc]
      have htail : 2*2^a-1 = 2*(2^a-1)+1 := by
        have hp0 : 0 < 2^a := Nat.pow_pos (by decide)
        have hp : 1 ≤ 2^a := by omega
        omega
      have hshape : x*2^(a+1)+(2^(a+1)-1) =
          2*(x*2^a+(2^a-1))+1 := by
        calc
          x*2^(a+1)+(2^(a+1)-1) = x*(2*2^a)+(2*2^a-1) := by rw [hpow]
          _ = 2*(x*2^a)+(2*(2^a-1)+1) := by rw [hmul,htail]
          _ = 2*(x*2^a+(2^a-1))+1 := by
            rw [Nat.mul_add]
            simp [Nat.add_assoc]
      rw [hshape]
      change popCount (2*(x*2^a+(2^a-1))+1) = popCount x+(a+1)
      rw [popCount_odd, ih]
      exact Nat.add_comm 1 (popCount x+a)

def M (A L : Nat) : Nat := 2^A * (2^(L+2)-1)

theorem pow2_ge_two (L : Nat) : 2 ≤ 2^(L+2) := by
  have hp0 : 0 < 2^L := Nat.pow_pos (by decide)
  have hp : 1 ≤ 2^L := by omega
  have hpow4 : 2^(L+2) = 2^L*4 := by
    simp [Nat.pow_add]
  have hmul : 4 ≤ 2^L*4 := by
    calc
      4 = 4*1 := by omega
      _ ≤ 4*2^L := Nat.mul_le_mul_left 4 hp
      _ = 2^L*4 := Nat.mul_comm 4 (2^L)
  rw [hpow4]
  have h24 : 2 ≤ 4 := by decide
  exact Nat.le_trans h24 hmul

theorem M_pos (A L : Nat) : 0 < M A L := by
  unfold M
  apply Nat.mul_pos
  · exact Nat.pow_pos (by decide)
  · have hpow := pow2_ge_two L
    have hgt : 1 < 2^(L+2) := by omega
    exact Nat.sub_pos_of_lt hgt

theorem M_sub_one_split (A L : Nat) :
    M A L - 1 = (2^(L+2)-2)*2^A + (2^A-1) := by
  unfold M
  have hp : 0 < 2^A := Nat.pow_pos (by decide)
  have hq : 2 ≤ 2^(L+2) := pow2_ge_two L
  calc
    2^A * (2^(L+2)-1) - 1 =
        (2^(L+2)-1)*2^A - 1 := by rw [Nat.mul_comm]
    _ = ((2^(L+2)-2)+1)*2^A - 1 := by congr 2 <;> omega
    _ = (2^(L+2)-2)*2^A + 1*2^A - 1 := by rw [Nat.add_mul]
    _ = (2^(L+2)-2)*2^A + (2^A-1) := by simp; omega

theorem popCount_M_sub_one (A L : Nat) : popCount (M A L - 1) = A+L+1 := by
  rw [M_sub_one_split, popCount_shift_low_ones, popCount_pow2_sub_two]
  omega

theorem sumV2_M_sub_one (A L : Nat) :
    sumV2 (M A L - 1) = M A L - A - L - 2 := by
  have h := sumV2_add_popCount (M A L - 1)
  rw [popCount_M_sub_one] at h
  omega

theorem marker1_runtime_formula (A L : Nat) :
    (10*(M A L)^2 + 73*M A L + 93 + 12*(A+L)) =
      (2*(5*M A L+7)^2 + 45*(5*M A L+7) + 60*(A+L) + 52) / 5 := by
  let m := M A L
  have hnum :
      2*(5*m+7)^2 + 45*(5*m+7) + 60*(A+L) + 52 =
        5*(10*m^2 + 73*m + 93 + 12*(A+L)) := by
    simp only [Nat.pow_two]
    have hmul_inner : m*(5*m) = 5*(m*m) := by
      calc
        m*(5*m) = (m*5)*m := by rw [Nat.mul_assoc]
        _ = (5*m)*m := by rw [Nat.mul_comm m 5]
        _ = 5*(m*m) := by rw [Nat.mul_assoc]
    have hmul : (5*m)*(5*m) = 25*(m*m) := by
      calc
        (5*m)*(5*m) = 5*(m*(5*m)) := by rw [Nat.mul_assoc]
        _ = 5*(5*(m*m)) := by rw [hmul_inner]
        _ = (5*5)*(m*m) := by rw [Nat.mul_assoc]
        _ = 25*(m*m) := by simp
    have hsq : (5*m+7)*(5*m+7) = 25*(m*m) + 70*m + 49 := by
      calc
        (5*m+7)*(5*m+7) = (5*m)*(5*m+7) + 7*(5*m+7) := by
          rw [Nat.add_mul]
        _ = (5*m)*(5*m) + (5*m)*7 + 7*(5*m) + 7*7 := by
          rw [Nat.mul_add, Nat.mul_add]
          exact (Nat.add_assoc ((5*m)*(5*m) + (5*m)*7) (7*(5*m)) (7*7)).symm
        _ = 25*(m*m) + 35*m + 35*m + 49 := by
          rw [hmul]
          have h1 : (5*m)*7 = 35*m := by omega
          have h2 : 7*(5*m) = 35*m := by omega
          have h3 : 7*7 = 49 := by decide
          rw [h1,h2,h3]
        _ = 25*(m*m) + 70*m + 49 := by omega
    rw [hsq]
    let q := m*m
    change 2*(25*q+70*m+49) + 45*(5*m+7) + 60*(A+L) + 52 =
      5*(10*q+73*m+93+12*(A+L))
    omega
  change 10*m^2 + 73*m + 93 + 12*(A+L) =
    (2*(5*m+7)^2 + 45*(5*m+7) + 60*(A+L) + 52) / 5
  calc
    10*m^2 + 73*m + 93 + 12*(A+L) =
        (5*(10*m^2 + 73*m + 93 + 12*(A+L))) / 5 := by omega
    _ = (2*(5*m+7)^2 + 45*(5*m+7) + 60*(A+L) + 52) / 5 := by rw [← hnum]


/-- The sum of the j-dependent part of the ordinary q4-cycle costs for
    j = 1,...,n. -/
def linearCycleSum : Nat → Nat
  | 0 => 0
  | n+1 => linearCycleSum n + 20*(n+2) + 46

theorem sq_succ (n : Nat) : (n+1)^2 = n^2 + 2*n + 1 := by
  simp only [Nat.pow_two]
  calc
    (n+1)*(n+1) = n*(n+1) + 1*(n+1) := by rw [Nat.add_mul]
    _ = n*n + n + n + 1 := by
      rw [Nat.mul_add, Nat.mul_add]
      simp [Nat.add_assoc]
    _ = n*n + 2*n + 1 := by omega

theorem linearCycleSum_closed (n : Nat) :
    linearCycleSum n = 10*n^2 + 76*n := by
  induction n with
  | zero => simp [linearCycleSum]
  | succ n ih =>
      rw [linearCycleSum, ih, sq_succ]
      omega

theorem linearCycleSum_sub_one (M : Nat) (hM : 0 < M) :
    linearCycleSum (M-1) = 10*M^2 + 56*M - 66 := by
  let n := M-1
  have hMn : M = n+1 := by dsimp [n]; omega
  calc
    linearCycleSum (M-1) = linearCycleSum n := by rfl
    _ = 10*n^2 + 76*n := linearCycleSum_closed n
    _ = 10*(n+1)^2 + 56*(n+1) - 66 := by
      rw [sq_succ]
      omega
    _ = 10*M^2 + 56*M - 66 := by rw [← hMn]

/-- Sum of all ordinary marker-1 even-L cycles, excluding the terminal cycle.
    The counter valuation is indexed in reverse, r=M-j. -/
def ordinaryCycleSum (A L : Nat) : Nat :=
  linearCycleSum (M A L - 1) + 12*sumV2 (M A L - 1)

theorem sumV2_M_sub_one_add (A L : Nat) :
    sumV2 (M A L - 1) + A + L + 2 = M A L := by
  have h := sumV2_add_popCount (M A L - 1)
  rw [popCount_M_sub_one] at h
  omega

theorem ordinaryCycleSum_add_inputs (A L : Nat) :
    ordinaryCycleSum A L + 12*(A+L) + 24 =
      10*(M A L)^2 + 68*M A L - 66 := by
  unfold ordinaryCycleSum
  rw [linearCycleSum_sub_one (M A L) (M_pos A L)]
  have hsum := sumV2_M_sub_one_add A L
  omega

def initialPrefixCost (A L : Nat) : Nat := 107 + 12*(A+L)

def finalCycleCost (A L : Nat) : Nat := 5*M A L + 12*(A+L) + 76

theorem marker1_total_from_cycles (A L : Nat) :
    initialPrefixCost A L + ordinaryCycleSum A L + finalCycleCost A L =
      10*(M A L)^2 + 73*M A L + 93 + 12*(A+L) := by
  have hnorm := ordinaryCycleSum_add_inputs A L
  unfold initialPrefixCost finalCycleCost
  omega

end Marker1TerminalArithmetic
