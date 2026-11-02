module
public import Agent18BReduction

@[expose] public section

namespace BB6.Parity
open BReduction

/-- The two-counter return map satisfies an exact base-2/base-3 balance law. -/
theorem F_balance (s : Nat × Nat) :
    2*(F s).2+3*(F s).1 = 3*s.2+4+8*s.1 := by
  rcases s with ⟨p,d⟩
  simp only [F, Prod.fst, Prod.snd]
  omega

theorem F_order (s t : Nat × Nat)
    (hp : s.1=t.1) (hq : (F s).1=(F t).1) (hd : s.2≤t.2) :
    (F s).2 ≤ (F t).2 := by
  have ha := F_balance s
  have hb := F_balance t
  omega

theorem F_gap (s t : Nat × Nat)
    (hp : s.1=t.1) (hq : (F s).1=(F t).1) (hd : s.2≤t.2) :
    2*((F t).2-(F s).2) = 3*(t.2-s.2) := by
  have ha := F_balance s
  have hb := F_balance t
  have hle := F_order s t hp hq hd
  omega

/-- Parity-agreeing itineraries of length k require congruent initial payloads modulo 2^k. -/
theorem coding_divisible (k : Nat) (s t : Nat × Nat)
    (horder : s.2 ≤ t.2)
    (hpar : ∀ j : Nat, j ≤ k → (iterF j s).1 = (iterF j t).1) :
    2^k ∣ (t.2 - s.2) := by
  induction k generalizing s t with
  | zero => simp
  | succ k ih =>
    have hp0 : s.1=t.1 := by simpa [iterF] using hpar 0 (by omega)
    have hp1 : (F s).1=(F t).1 := by simpa [iterF] using hpar 1 (by omega)
    have hle := F_order s t hp0 hp1 horder
    have hshift : ∀ j : Nat, j ≤ k →
        (iterF j (F s)).1 = (iterF j (F t)).1 := by
      intro j hj
      simpa only [iterF] using hpar (j+1) (by omega)
    obtain ⟨w,hw⟩ := ih (F s) (F t) hle hshift
    have hgap := F_gap s t hp0 hp1 horder
    have heq : 3*(t.2-s.2) = 2^(k+1)*w := by
      calc
        3*(t.2-s.2) = 2*((F t).2-(F s).2) := hgap.symm
        _ = 2*(2^k*w) := by rw [hw]
        _ = 2^(k+1)*w := by simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have hdiv : 2^(k+1) ∣ 3*(t.2-s.2) := ⟨w, heq⟩
    have hcop : Nat.Coprime (2^(k+1)) 3 :=
      Nat.Coprime.pow_left (k+1) (by decide : Nat.Coprime 2 3)
    exact hcop.dvd_of_dvd_mul_left hdiv

theorem pow_two_gt (n : Nat) : n < 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

/-- An infinite identical parity itinerary determines its initial payload uniquely. -/
theorem infinite_coding_unique (s t : Nat × Nat)
    (hp : ∀ j : Nat, (iterF j s).1 = (iterF j t).1) :
    s.2 = t.2 := by
  rcases Nat.le_total s.2 t.2 with hle | hle
  · by_cases heq : s.2=t.2
    · exact heq
    · exfalso
      have hgap : 0 < t.2-s.2 := by omega
      have hdiv := coding_divisible (t.2-s.2+1) s t hle (by intro j hj; exact hp j)
      have hbig := pow_two_gt (t.2-s.2+1)
      have hsmall : (2^(t.2-s.2+1)) ≤ t.2-s.2 := Nat.le_of_dvd hgap hdiv
      omega
  · by_cases heq : s.2=t.2
    · exact heq
    · exfalso
      have hgap : 0 < s.2-t.2 := by omega
      have hdiv := coding_divisible (s.2-t.2+1) t s hle (by intro j hj; exact (hp j).symm)
      have hbig := pow_two_gt (s.2-t.2+1)
      have hsmall : (2^(s.2-t.2+1)) ≤ s.2-t.2 := Nat.le_of_dvd hgap hdiv
      omega

/-- Any fixed prefix and subsequent block may be composed in either time direction. -/
theorem iterF_add (m n : Nat) (s : Nat × Nat) :
    iterF (m+n) s = iterF n (iterF m s) := by
  induction m generalizing s with
  | zero => simp [iterF]
  | succ m ih =>
    have h : m+1+n = (m+n)+1 := by omega
    rw [h]
    change iterF (m+n) (F s) = iterF n (iterF m (F s))
    exact ih (F s)

/-- The infinite parity bitstream of any finite starting section state is aperiodic. -/
theorem no_eventual_parity_period (s : Nat × Nat) (n P : Nat) (hp : 0 < P) :
    ¬ (∀ j : Nat,
      (iterF (n+j) s).1 = (iterF (n+P+j) s).1) := by
  intro h
  let t := iterF n s
  let u := iterF (n+P) s
  have heq : t.2 = u.2 := infinite_coding_unique t u (by
    intro j
    have ht : iterF j t = iterF (n+j) s := (iterF_add n j s).symm
    have hu : iterF j u = iterF (n+P+j) s := (iterF_add (n+P) j s).symm
    rw [ht,hu]
    exact h j)
  have hu : u = iterF P t := iterF_add n P s
  have hgrowth := iterF_growth P t.1 t.2
  rw [← hu] at hgrowth
  omega

#print axioms no_eventual_parity_period
#print axioms coding_divisible
#print axioms infinite_coding_unique
end BB6.Parity
