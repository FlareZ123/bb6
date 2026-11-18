import S4WeightFormula
import S4Octet

namespace S4TerminalGate

open S4Power
open S4Octet

/-- The weighted-drain shadow uses exactly the source gate's weight. -/
theorem W_eq_power (L : List Nat) :
    S4WeightFormula.W L = S4Power.W L := by
  induction L with
  | nil => rfl
  | cons b S ih => simp [S4WeightFormula.W, S4Power.W, ih]

/-- The weighted-drain shadow uses exactly the source gate's H recursion. -/
theorem H_eq_power (a : Nat) (L : List Nat) :
    S4WeightFormula.H a L = S4Power.H a L := by
  induction L generalizing a with
  | nil =>
      induction a using Nat.strong_induction_on with
      | h a ih =>
          by_cases he : a % 2 = 0
          · by_cases hz : a = 0
            · simp [S4WeightFormula.H, S4Power.H, he, hz]
            · simp [S4WeightFormula.H, S4Power.H, he, hz]
          · by_cases hs : a ≤ 1
            · simp [S4WeightFormula.H, S4Power.H, he, hs]
            · have hlt : a / 2 < a := by omega
              simp [S4WeightFormula.H, S4Power.H, he, hs, ih (a / 2) hlt]
  | cons b S ih =>
      by_cases he : a % 2 = 0
      · simp [S4WeightFormula.H, S4Power.H, he]
      · simp [S4WeightFormula.H, S4Power.H, he, ih]

/-- The weighted first-moment identity, now stated for the actual source H/W. -/
theorem H_weight_formula_ge_len_power
    (L : List Nat) (a : Nat) (U : List Nat)
    (h : S4Power.H a L = some U)
    (hLen : L.length ≤ S4WeightFormula.v2 (a + 1 + 2 * S4Power.W L)) :
    2 * S4Power.W U + 2 * S4WeightFormula.Mfull L =
      (S4WeightFormula.v2 (a + 1 + 2 * S4Power.W L) + 3) *
        (a + 1 + 2 * S4Power.W L) +
        3 * 2 ^ S4WeightFormula.v2 (a + 1 + 2 * S4Power.W L) := by
  have hLocal : S4WeightFormula.H a L = some U := by
    rw [H_eq_power]
    exact h
  have hLenLocal := hLen
  rw [← W_eq_power L] at hLenLocal
  have hFormula :=
    S4WeightFormula.H_weight_formula_ge_len L a U hLocal hLenLocal
  simpa [W_eq_power] using hFormula

/-- Every successful H output has at least one more digit than its input list. -/
theorem H_length_ge_succ (a : Nat) (L : List Nat) (U : List Nat)
    (h : S4Power.H a L = some U) :
    L.length + 1 ≤ U.length := by
  induction L generalizing a U with
  | nil =>
      by_cases he : a % 2 = 0
      · have hz : a ≠ 0 := by
          intro hz
          subst a
          simp [S4Power.H] at h
        simp [S4Power.H, he, hz] at h
        subst U
        simp
      · by_cases hs : a ≤ 1
        · simp [S4Power.H, he, hs] at h
        · have hrec :
              (S4Power.H (a / 2) []).map (a / 2 :: ·) = some U := by
              simpa [S4Power.H, he, hs] using h
          obtain ⟨V, hV, hVU⟩ := Option.map_eq_some_iff.mp hrec
          subst U
          simp
  | cons b S ih =>
      by_cases he : a % 2 = 0
      · simp [S4Power.H, he] at h
        subst U
        simp
      · have hrec :
            (S4Power.H (b + a / 2 + 1) S).map (a / 2 :: ·) = some U := by
            simpa [S4Power.H, he] using h
        obtain ⟨V, hV, hVU⟩ := Option.map_eq_some_iff.mp hrec
        subst U
        have hlen := ih (b + a / 2 + 1) V hV
        simp at hlen ⊢
        omega

/-- A successful source G gate never shortens its stack. -/
theorem G_length_ge (c : Nat) (T U : List Nat)
    (h : S4Octet.G c T = some U) :
    T.length ≤ U.length := by
  cases T with
  | nil => simp
  | cons b S =>
      change S4Power.H (b + c) S = some U at h
      have hlen := H_length_ge_succ (b + c) S U h
      simpa using hlen

/-- The source weight dominates the all-ones binary word of the same length. -/
theorem W_lower_bound (T : List Nat) :
    2 ^ T.length ≤ S4Power.W T + 1 := by
  induction T with
  | nil => simp [S4Power.W]
  | cons b S ih =>
      calc
        2 ^ (S.length + 1) = 2 ^ S.length * 2 := by rw [Nat.pow_succ]
        _ ≤ (S4Power.W S + 1) * 2 :=
          Nat.mul_le_mul_right 2 ih
        _ ≤ S4Power.W (b :: S) + 1 := by
          simp [S4Power.W]
          omega

/-- If a power of two is at least 64, it is divisible by 64. -/
theorem pow2_dvd64_of_ge (m : Nat) (h : 64 ≤ 2 ^ m) :
    64 ∣ 2 ^ m := by
  by_cases hm : 6 ≤ m
  · refine ⟨2 ^ (m - 6), ?_⟩
    have hmEq : m = 6 + (m - 6) := by omega
    rw [hmEq, Nat.pow_add]
    norm_num
  · have hm' : m ≤ 5 := by omega
    interval_cases m <;> norm_num at h

/-- A power-of-two gate on a stack of at least six digits is divisible by 64. -/
theorem pow2_dvd64_of_stack
    (T : List Nat) (c : Nat) (hc : 1 ≤ c)
    (hPow : S4Power.Pow2 (S4Power.W T + c))
    (hLen : 6 ≤ T.length) :
    64 ∣ S4Power.W T + c := by
  rcases hPow with ⟨m, hm⟩
  have hpow : 64 ≤ 2 ^ T.length := by
    have hdecomp : T.length = 6 + (T.length - 6) := by omega
    rw [hdecomp, Nat.pow_add]
    norm_num
    have hpos : 1 ≤ 2 ^ (T.length - 6) := by positivity
    omega
  have hW := W_lower_bound T
  have hge : 64 ≤ S4Power.W T + c := by omega
  rw [hm]
  exact pow2_dvd64_of_ge m hge

/-- Two consecutive successful drains cannot end in a power-of-two gate
    unless the suffix first-moment has the displayed residue. -/
theorem two_gate_moment_mod32
    (a k cNext : Nat) (L U : List Nat)
    (hk : 6 ≤ k)
    (hLen : L.length ≤ k)
    (hVal : S4WeightFormula.v2 (a + 1 + 2 * S4Power.W L) = k)
    (hDiv : 2 ^ k ∣ a + 1 + 2 * S4Power.W L)
    (hFirst : S4Power.H a L = some U)
    (hNextDiv : 64 ∣ S4Power.W U + cNext) :
    S4WeightFormula.Mfull L % 32 = cNext % 32 := by
  have hFormula := H_weight_formula_ge_len_power L a U hFirst hLen
  rw [hVal] at hFormula
  have hPow64 : 64 ∣ 2 ^ k := by
    obtain ⟨q, hq⟩ := hDiv
    have hbase : 64 ∣ 2 ^ k := by
      refine ⟨2 ^ (k - 6), ?_⟩
      have hkEq : k = 6 + (k - 6) := by omega
      rw [hkEq, Nat.pow_add]
      norm_num
    exact hbase
  have hX64 : 64 ∣ a + 1 + 2 * S4Power.W L :=
    Nat.dvd_trans hPow64 hDiv
  rcases hX64 with ⟨x, hx⟩
  rcases hPow64 with ⟨p, hp⟩
  have hRhs64 :
      64 ∣ (k + 3) * (a + 1 + 2 * S4Power.W L) + 3 * 2 ^ k := by
    refine ⟨(k + 3) * x + 3 * p, ?_⟩
    rw [hx, hp]
    ring
  rcases hRhs64 with ⟨r, hr⟩
  have hSum64 : 64 ∣ 2 * S4Power.W U + 2 * S4WeightFormula.Mfull L := by
    rw [hFormula]
    exact hRhs64
  have hSum32 : 32 ∣ S4Power.W U + S4WeightFormula.Mfull L := by
    rcases hSum64 with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    omega
  rcases hSum32 with ⟨x', hx'⟩
  rcases hNextDiv with ⟨y', hy'⟩
  have hNext32 : S4Power.W U + cNext = 32 * (2 * y') := by
    omega
  have hResidue :
      S4WeightFormula.Mfull L + 32 * (2 * y') =
        cNext + 32 * x' := by
    omega
  omega

end S4TerminalGate
