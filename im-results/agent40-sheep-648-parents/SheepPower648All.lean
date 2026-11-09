import SheepPower648Rows
set_option linter.unusedSimpArgs false
namespace SheepPower648

/-- All genuine generic even-section power predecessors within the valuation range
    lie in exactly three arithmetic source-parameter branches. -/
theorem all_generic_gates (h a t v : Nat)
    (hh : h ≤ 5) (ha : 1 ≤ a)
    (hzero : h=0 → a=1)
    (hpos : 0<h → a ≤ 2*h+2)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(648*t+h+1)+3*3^h) :
    (h=3 ∧ a=6 ∧ t%7=6) ∨
    (h=5 ∧ a=2 ∧ t%9=1) ∨
    (h=5 ∧ a=4 ∧ t%15=14) := by
  rcases (show h=0 ∨ h=1 ∨ h=2 ∨ h=3 ∨ h=4 ∨ h=5 from by omega) with h0|h1|h2|h3|h4|h5
  · subst h
    have : a=1 := hzero rfl
    subst a
    exfalso
    apply no_h0_a1 t v
    have hexp : 648*t+0+1 = 1+648*t := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega
  · subst h
    rcases (show a=1 ∨ a=2 ∨ a=3 ∨ a=4 from by omega) with a1|a2|a3|a4
    · subst a
      exfalso
      apply no_h1_a1 t v
      have hexp : 648*t+1+1 = 2+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h1_a2 t v
      have hexp : 648*t+1+1 = 2+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h1_a3 t v
      have hexp : 648*t+1+1 = 2+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h1_a4 t v
      have hexp : 648*t+1+1 = 2+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
  · subst h
    rcases (show a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 from by omega) with a1|a2|a3|a4|a5|a6
    · subst a
      exfalso
      apply no_h2_a1 t v
      have hexp : 648*t+2+1 = 3+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h2_a2 t v
      have hexp : 648*t+2+1 = 3+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h2_a3 t v
      have hexp : 648*t+2+1 = 3+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h2_a4 t v
      have hexp : 648*t+2+1 = 3+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h2_a5 t v
      have hexp : 648*t+2+1 = 3+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h2_a6 t v
      have hexp : 648*t+2+1 = 3+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
  · subst h
    rcases (show a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 from by omega) with a1|a2|a3|a4|a5|a6|a7|a8
    · subst a
      exfalso
      apply no_h3_a1 t v
      have hexp : 648*t+3+1 = 4+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h3_a2 t v
      have hexp : 648*t+3+1 = 4+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h3_a3 t v
      have hexp : 648*t+3+1 = 4+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h3_a4 t v
      have hexp : 648*t+3+1 = 4+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h3_a5 t v
      have hexp : 648*t+3+1 = 4+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      have hgate : t%7=6 := by
        apply only_h3_a6 t v
        have hexp : 648*t+3+1 = 4+648*t := by omega
        rw [hexp] at heq
        simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
        omega
      omega
    · subst a
      exfalso
      apply no_h3_a7 t v
      have hexp : 648*t+3+1 = 4+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h3_a8 t v
      have hexp : 648*t+3+1 = 4+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
  · subst h
    rcases (show a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 from by omega) with a1|a2|a3|a4|a5|a6|a7|a8|a9|a10
    · subst a
      exfalso
      apply no_h4_a1 t v
      have hexp : 648*t+4+1 = 5+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h4_a2 t v
      have hexp : 648*t+4+1 = 5+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h4_a3 t v
      have hexp : 648*t+4+1 = 5+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h4_a4 t v
      have hexp : 648*t+4+1 = 5+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h4_a5 t v
      have hexp : 648*t+4+1 = 5+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h4_a6 t v
      have hexp : 648*t+4+1 = 5+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h4_a7 t v
      have hexp : 648*t+4+1 = 5+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h4_a8 t v
      have hexp : 648*t+4+1 = 5+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h4_a9 t v
      have hexp : 648*t+4+1 = 5+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h4_a10 t v
      have hexp : 648*t+4+1 = 5+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
  · subst h
    rcases (show a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 ∨ a=11 ∨ a=12 from by omega) with a1|a2|a3|a4|a5|a6|a7|a8|a9|a10|a11|a12
    · subst a
      exfalso
      apply no_h5_a1 t v
      have hexp : 648*t+5+1 = 6+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      have hgate : t%9=1 := by
        apply only_h5_a2 t v
        have hexp : 648*t+5+1 = 6+648*t := by omega
        rw [hexp] at heq
        simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
        omega
      omega
    · subst a
      exfalso
      apply no_h5_a3 t v
      have hexp : 648*t+5+1 = 6+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      have hgate : t%15=14 := by
        apply only_h5_a4 t v
        have hexp : 648*t+5+1 = 6+648*t := by omega
        rw [hexp] at heq
        simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
        omega
      omega
    · subst a
      exfalso
      apply no_h5_a5 t v
      have hexp : 648*t+5+1 = 6+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h5_a6 t v
      have hexp : 648*t+5+1 = 6+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h5_a7 t v
      have hexp : 648*t+5+1 = 6+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h5_a8 t v
      have hexp : 648*t+5+1 = 6+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h5_a9 t v
      have hexp : 648*t+5+1 = 6+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h5_a10 t v
      have hexp : 648*t+5+1 = 6+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h5_a11 t v
      have hexp : 648*t+5+1 = 6+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      exfalso
      apply no_h5_a12 t v
      have hexp : 648*t+5+1 = 6+648*t := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega

#print axioms all_generic_gates
end SheepPower648
