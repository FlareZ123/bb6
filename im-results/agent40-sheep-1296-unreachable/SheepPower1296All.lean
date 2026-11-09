import SheepPower1296Rows
namespace SheepPower1296

/-- All generic Sheep power-gate equations in the source-valuation range are impossible. -/
theorem no_generic_candidate (h a k v : Nat)
    (hh : h ≤ 5) (ha : 1 ≤ a)
    (hzero : h=0 → a=1)
    (hpos : 0<h → a ≤ 2*h+2)
    (heq : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)
      = 2^(1296+340200*k+h+1)+3*3^h) : False := by
  rcases (show h=0 ∨ h=1 ∨ h=2 ∨ h=3 ∨ h=4 ∨ h=5 from by omega) with h0|h1|h2|h3|h4|h5
  · subst h
    have : a=1 := hzero rfl
    subst a
    apply no_h0_a1 k v
    have hexp : 1296+340200*k+0+1 = 1297+340200*k := by omega
    rw [hexp] at heq
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
    omega
  · subst h
    rcases (show a=1 ∨ a=2 ∨ a=3 ∨ a=4 from by omega) with a1|a2|a3|a4
    · subst a
      apply no_h1_a1 k v
      have hexp : 1296+340200*k+1+1 = 1298+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h1_a2 k v
      have hexp : 1296+340200*k+1+1 = 1298+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h1_a3 k v
      have hexp : 1296+340200*k+1+1 = 1298+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h1_a4 k v
      have hexp : 1296+340200*k+1+1 = 1298+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
  · subst h
    rcases (show a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 from by omega) with a1|a2|a3|a4|a5|a6
    · subst a
      apply no_h2_a1 k v
      have hexp : 1296+340200*k+2+1 = 1299+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h2_a2 k v
      have hexp : 1296+340200*k+2+1 = 1299+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h2_a3 k v
      have hexp : 1296+340200*k+2+1 = 1299+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h2_a4 k v
      have hexp : 1296+340200*k+2+1 = 1299+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h2_a5 k v
      have hexp : 1296+340200*k+2+1 = 1299+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h2_a6 k v
      have hexp : 1296+340200*k+2+1 = 1299+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
  · subst h
    rcases (show a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 from by omega) with a1|a2|a3|a4|a5|a6|a7|a8
    · subst a
      apply no_h3_a1 k v
      have hexp : 1296+340200*k+3+1 = 1300+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h3_a2 k v
      have hexp : 1296+340200*k+3+1 = 1300+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h3_a3 k v
      have hexp : 1296+340200*k+3+1 = 1300+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h3_a4 k v
      have hexp : 1296+340200*k+3+1 = 1300+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h3_a5 k v
      have hexp : 1296+340200*k+3+1 = 1300+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h3_a6 k v
      have hexp : 1296+340200*k+3+1 = 1300+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h3_a7 k v
      have hexp : 1296+340200*k+3+1 = 1300+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h3_a8 k v
      have hexp : 1296+340200*k+3+1 = 1300+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
  · subst h
    rcases (show a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 from by omega) with a1|a2|a3|a4|a5|a6|a7|a8|a9|a10
    · subst a
      apply no_h4_a1 k v
      have hexp : 1296+340200*k+4+1 = 1301+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h4_a2 k v
      have hexp : 1296+340200*k+4+1 = 1301+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h4_a3 k v
      have hexp : 1296+340200*k+4+1 = 1301+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h4_a4 k v
      have hexp : 1296+340200*k+4+1 = 1301+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h4_a5 k v
      have hexp : 1296+340200*k+4+1 = 1301+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h4_a6 k v
      have hexp : 1296+340200*k+4+1 = 1301+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h4_a7 k v
      have hexp : 1296+340200*k+4+1 = 1301+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h4_a8 k v
      have hexp : 1296+340200*k+4+1 = 1301+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h4_a9 k v
      have hexp : 1296+340200*k+4+1 = 1301+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h4_a10 k v
      have hexp : 1296+340200*k+4+1 = 1301+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
  · subst h
    rcases (show a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 ∨ a=11 ∨ a=12 from by omega) with a1|a2|a3|a4|a5|a6|a7|a8|a9|a10|a11|a12
    · subst a
      apply no_h5_a1 k v
      have hexp : 1296+340200*k+5+1 = 1302+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h5_a2 k v
      have hexp : 1296+340200*k+5+1 = 1302+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h5_a3 k v
      have hexp : 1296+340200*k+5+1 = 1302+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h5_a4 k v
      have hexp : 1296+340200*k+5+1 = 1302+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h5_a5 k v
      have hexp : 1296+340200*k+5+1 = 1302+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h5_a6 k v
      have hexp : 1296+340200*k+5+1 = 1302+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h5_a7 k v
      have hexp : 1296+340200*k+5+1 = 1302+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h5_a8 k v
      have hexp : 1296+340200*k+5+1 = 1302+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h5_a9 k v
      have hexp : 1296+340200*k+5+1 = 1302+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h5_a10 k v
      have hexp : 1296+340200*k+5+1 = 1302+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h5_a11 k v
      have hexp : 1296+340200*k+5+1 = 1302+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega
    · subst a
      apply no_h5_a12 k v
      have hexp : 1296+340200*k+5+1 = 1302+340200*k := by omega
      rw [hexp] at heq
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.one_mul, Nat.mul_one] at heq
      omega

/-- The target power has exact 3-adic valuation five in its predecessor gate. -/
theorem target_mod729 (k : Nat) :
    2^(1296+340200*k)%729=487 := by
  rw [pow_mod_period 729 340200 1296 k (by decide) (by rw [←Nat.powMod_def]; decide)]
  rw [←Nat.powMod_def]
  decide

#print axioms no_generic_candidate
#print axioms target_mod729
end SheepPower1296
