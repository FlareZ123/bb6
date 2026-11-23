import Lean

namespace BB6SyncThresholds

theorem perturbation_constant_iff
    (A M lo hi : Int)
    (hM : 0 < M) (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hwidth : hi - lo < M) :
    (∀ d : Int, lo ≤ d → d ≤ hi → (A + d) / M = A / M) ↔
      -lo ≤ A % M ∧ A % M ≤ M - 1 - hi := by
  have hr0 : 0 ≤ A % M := Int.emod_nonneg A (by omega)
  have hrM : A % M < M := Int.emod_lt_of_pos A hM
  have hd0 : M * (A / M) + A % M = A := by
    calc
      M * (A / M) + A % M = (A / M) * M + A % M := by rw [Int.mul_comm M (A / M)]
      _ = A := Int.ediv_mul_add_emod A M
  have hloM : -lo < M := by omega
  have hhiM : hi < M := by omega
  constructor
  · intro h
    constructor
    · by_cases hgood : -lo ≤ A % M
      · exact hgood
      · have hrlt : A % M < -lo := by omega
        have rlo : 0 ≤ A % M + lo + M := by omega
        have rhi : A % M + lo + M < M := by omega
        have eqn : (A % M + lo + M) + M * (A / M - 1) = A + lo := by
          rw [Int.mul_sub]
          omega
        have uq := (Int.ediv_emod_unique hM).2 ⟨eqn, rlo, rhi⟩
        have hx : (A + lo) / M = A / M := h lo (by omega) (by omega)
        have huq : (A + lo) / M = A / M - 1 := uq.1
        omega
    · by_cases hgood : A % M ≤ M - 1 - hi
      · exact hgood
      · have hrgt : M - 1 - hi < A % M := by omega
        have rlo : 0 ≤ A % M + hi - M := by omega
        have rhi : A % M + hi - M < M := by omega
        have eqn : (A % M + hi - M) + M * (A / M + 1) = A + hi := by
          rw [Int.mul_add]
          omega
        have uq := (Int.ediv_emod_unique hM).2 ⟨eqn, rlo, rhi⟩
        have hx : (A + hi) / M = A / M := h hi (by omega) (by omega)
        have huq : (A + hi) / M = A / M + 1 := uq.1
        omega
  · rintro ⟨hl, hu⟩ d hdlo hdhi
    have low : 0 ≤ A % M + d := by omega
    have high : A % M + d < M := by omega
    have eqn : (A % M + d) + M * (A / M) = A + d := by
      omega
    exact ((Int.ediv_emod_unique hM).2 ⟨eqn, low, high⟩).1

theorem left_a_threshold (A M : Int) (hM : 7 ≤ M) :
    (∀ d : Int, -4 ≤ d → d ≤ 2 → (A + d) / M = A / M) ↔
      4 ≤ A % M ∧ A % M ≤ M - 3 := by
  have h := perturbation_constant_iff A M (-4) 2 (by omega) (by omega) (by omega) (by omega)
  constructor
  · intro hp
    have q := h.mp hp
    exact ⟨q.1, by omega⟩
  · intro q
    apply h.mpr
    exact ⟨q.1, by omega⟩

theorem left_b_threshold (A M : Int) (hM : 7 ≤ M) :
    (∀ d : Int, -2 ≤ d → d ≤ 4 → (A + d) / M = A / M) ↔
      2 ≤ A % M ∧ A % M ≤ M - 5 := by
  have h := perturbation_constant_iff A M (-2) 4 (by omega) (by omega) (by omega) (by omega)
  constructor
  · intro hp
    have q := h.mp hp
    exact ⟨q.1, by omega⟩
  · intro q
    apply h.mpr
    exact ⟨q.1, by omega⟩

theorem right_a_negative_threshold (A M : Int) (hM : 10 ≤ M) :
    (∀ d : Int, -8 ≤ d → d ≤ 1 → (A + d) / M = A / M) ↔
      8 ≤ A % M ∧ A % M ≤ M - 2 := by
  have h := perturbation_constant_iff A M (-8) 1 (by omega) (by omega) (by omega) (by omega)
  constructor
  · intro hp
    have q := h.mp hp
    exact ⟨q.1, by omega⟩
  · intro q
    apply h.mpr
    exact ⟨q.1, by omega⟩

theorem right_b_threshold (A M : Int) (hM : 9 ≤ M) :
    (∀ d : Int, -2 ≤ d → d ≤ 6 → (A + d) / M = A / M) ↔
      2 ≤ A % M ∧ A % M ≤ M - 7 := by
  have h := perturbation_constant_iff A M (-2) 6 (by omega) (by omega) (by omega) (by omega)
  constructor
  · intro hp
    have q := h.mp hp
    exact ⟨q.1, by omega⟩
  · intro q
    apply h.mpr
    exact ⟨q.1, by omega⟩

end BB6SyncThresholds
