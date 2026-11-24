import MarginCert
namespace BB6.Agent28CarryBudget
open BB6.Agent43CarryCert
theorem step_bounds (Q j p c : Nat) (h : c ∈ step Q j [p]) :
    p ≤ 2*c ∧ 2*c ≤ p+(Q-j) := by
  simp only [step, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append] at h
  rcases h with h | h
  · by_cases he : p%2=0
    · simp [he] at h
      subst c
      omega
    · simp [he] at h
  · by_cases he : (p+(Q-j))%2=0
    · simp [he] at h
      subst c
      omega
    · simp [he] at h
theorem predecessor (Q m c : Nat) (hc : c ∈ states Q 0 [1] (m+1)) :
    ∃ p ∈ states Q 0 [1] m, c ∈ step Q m [p] := by
  rw [states_add] at hc
  simp only [Nat.zero_add, states, step, List.mem_flatMap] at hc
  obtain ⟨p,hp,he⟩ := hc
  exact ⟨p,hp,by simpa [step] using he⟩
/-- Upper envelope on every full carry, regardless of parity choices. -/
theorem carry_upper (Q m c : Nat) (hm : m≤Q+1)
    (hc : c ∈ states Q 0 [1] m) :
    2^m*(c+m)+Q+1 ≤ 2^m*(Q+2) := by
  induction m generalizing c with
  | zero =>
      simp [states] at hc
      subst c
      simp <;> omega
  | succ m ih =>
      obtain ⟨p,hp,hstep⟩ := predecessor Q m c hc
      have hprev := ih p (by omega) hp
      have hb := (step_bounds Q m p c hstep).2
      have hlin : 2*(c+(m+1)) ≤ (p+m)+(Q+2) := by omega
      have hmul := Nat.mul_le_mul_left (2^m) hlin
      rw [Nat.mul_add (2^m) (p+m) (Q+2)] at hmul
      have he : 2^m*(2*(c+(m+1)))=2^(m+1)*(c+(m+1)) := by
        rw [Nat.pow_succ, Nat.mul_assoc]
      rw [he] at hmul
      have hsum : 2^(m+1)*(Q+2)=2^m*(Q+2)+2^m*(Q+2) := by
        rw [Nat.pow_succ, Nat.mul_assoc]
        simp only [Nat.two_mul, Nat.mul_add]
        omega
      omega
theorem carry_lower (Q m c : Nat) (hm : 0<m)
    (hc : c ∈ states Q 0 [1] m) : Q+1≤2^m*c := by
  induction m generalizing c with
  | zero => omega
  | succ m ih =>
      obtain ⟨p,hp,hstep⟩ := predecessor Q m c hc
      by_cases hz : m=0
      · subst m
        simp [states] at hp
        subst p
        simp only [step, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, Nat.sub_zero] at hstep
        simp at hstep
        by_cases he : (1+Q)%2=0
        · simp [he] at hstep
          subst c
          simp
          omega
        · simp [he] at hstep
      · have hprev := ih p (by omega) hp
        have hb := (step_bounds Q m p c hstep).1
        have hmul := Nat.mul_le_mul_left (2^m) hb
        rw [Nat.pow_succ, Nat.mul_assoc]
        omega
theorem good_of_budget (Q L K m c : Nat) (hK : K≤Q+1)
    (hL : 3≤L) (hm : m<K) (hbudget : 2^(K-1)*L≤Q+1)
    (hc : c ∈ states Q 0 [1] m) :
    c≠2 ∧ c+L+m≤Q+2 := by
  have hpow := Nat.pow_le_pow_right (show 0<2 by decide) (show m≤K-1 by omega)
  have hprod := Nat.mul_le_mul_right L hpow
  have hsmall : 2^m*L≤Q+1 := by omega
  have hu := carry_upper Q m c (by omega) hc
  have hmul : 2^m*(c+m+L)≤2^m*(Q+2) := by
    rw [Nat.mul_add]
    omega
  have hmargin := Nat.le_of_mul_le_mul_left hmul (Nat.two_pow_pos m)
  refine ⟨?_,by omega⟩
  intro he
  by_cases hz : m=0
  · subst m
    simp [states] at hc
    omega
  · have hl := carry_lower Q m c (by omega) hc
    have hthree := Nat.mul_le_mul_left (2^m) hL
    rw [he] at hl
    have hp := Nat.two_pow_pos m
    simp only [Nat.mul_succ, Nat.mul_zero, Nat.zero_add] at hthree hl
    omega
theorem margin_of_early_empty (Q L K : Nat) (hK : K≤Q+1)
    (hL : 3≤L) (hbudget : 2^(K-1)*L≤Q+1)
    (hempty : states Q 0 [1] K=[]) :
    MarginSafe Q L 0 [1] K [] := by
  refine ⟨hempty,?_⟩
  intro i hi c hc
  simpa using good_of_budget Q L K i c hK hL hi hbudget hc
#print axioms carry_upper
#print axioms carry_lower
#print axioms good_of_budget
#print axioms margin_of_early_empty
end BB6.Agent28CarryBudget
