import SheepOddGap

namespace BB6.Agent17Valuation

def U (h : Nat) : Nat := 3^h*(4*h+3)+2^(h+1)

theorem u_small (h : Nat) : U h < 2^(2*h+3) := by
  induction h with
  | zero => decide
  | succ h ih =>
    by_cases hs : h<3
    · have hc : h=0 ∨ h=1 ∨ h=2 := by omega
      rcases hc with hc | hc | hc
      · subst h; decide
      · subst h; decide
      · subst h; decide
    · have hlow : 3≤h := by omega
      have hcoeff : 3*(4*(h+1)+3) ≤ 4*(4*h+3) := by omega
      have hmul := Nat.mul_le_mul_left (3^h) hcoeff
      have hscaled : (3^h*3)*(4*(h+1)+3) ≤ 4*(3^h*(4*h+3)) := by
        calc
         (3^h*3)*(4*(h+1)+3) = 3^h*(3*(4*(h+1)+3)) := by ac_rfl
         _ ≤ 3^h*(4*(4*h+3)) := hmul
         _ = 4*(3^h*(4*h+3)) := by ac_rfl
      have hpos : 0<2^(h+1) := Nat.pow_pos (by decide)
      have hpow2 : 2^((h+1)+1)=2^(h+1)*2 := by rw [Nat.pow_succ]
      have hpow3 : 3^(h+1)=3^h*3 := by rw [Nat.pow_succ]
      have hpowbig : 2^(2*(h+1)+3)=4*2^(2*h+3) := by
        have he : 2*(h+1)+3=(2*h+3)+2 := by omega
        rw [he,Nat.pow_add]
        change 2^(2*h+3)*4 = 4*2^(2*h+3)
        ac_rfl
      have ih4 := Nat.mul_lt_mul_of_pos_left ih (by decide : 0<4)
      dsimp [U] at ih ⊢
      rw [hpow3,hpow2,hpowbig]
      omega


def K (h a : Nat) : Nat := 3^h*(2*a-3)+2^(h+1)

/-- Above twice the hidden odd-block exponent plus three, the relevant
    odd remainder lies strictly inside the power-of-two gap. -/
theorem k_small (h n : Nat) :
    K h (2*h+3+n) < 2^(2*h+3+n) := by
  induction n with
  | zero =>
    have hc : 2*(2*h+3)-3=4*h+3 := by omega
    simpa only [Nat.add_zero, K, hc, U] using u_small h
  | succ n ih =>
    let a := 2*h+3+n
    have ha : 3 ≤ a := by dsimp [a]; omega
    have hcoef : 2*(a+1)-3=(2*a-3)+2 := by omega
    have hstep : K h (a+1)=K h a+2*3^h := by
      dsimp [K]
      rw [hcoef,Nat.mul_add]
      omega
    have hcoeff : 2≤2*a-3 := by omega
    have hmult := Nat.mul_le_mul_left (3^h) hcoeff
    have hpos : 0 < 2^h := Nat.pow_pos (by decide)
    have hlarge : 2*3^h ≤ K h a := by dsimp [K]; omega
    have hpow : 2^(a+1)=2*2^a := by rw [Nat.pow_succ]; omega
    have hab : K h a < 2^a := by simpa only [a] using ih
    have hsum : K h a+2*3^h < 2*2^a := by omega
    change K h (a+1)<2^(a+1)
    rw [hstep,hpow]
    exact hsum


theorem k_small_ge (h a : Nat) (ha : 2*h+3 ≤ a) : K h a < 2^a := by
  let n := a-(2*h+3)
  have hn : a=2*h+3+n := by dsimp [n]; omega
  rw [hn]
  exact k_small h n

theorem k_odd (h a : Nat) (ha : 3 ≤ a) : K h a%2=1 := by
  have h3 : (3^h)%2=1 := by
    calc
      (3^h)%2 = ((3%2)^h)%2 := Nat.pow_mod 3 h 2
      _ = 1 := by simp
  have hc : (2*a-3)%2=1 := by omega
  have htwo : 2^(h+1)%2=0 := by
    apply Nat.mod_eq_zero_of_dvd
    refine ⟨2^h,?_⟩
    rw [Nat.pow_succ]
    omega
  dsimp [K]
  rw [Nat.add_mod,Nat.mul_mod]
  rw [h3,hc,htwo]

theorem k_gt_one (h a : Nat) (ha : 3 ≤ a) : 1<K h a := by
  have hc : 3 ≤ 2*a-3 := by omega
  have h3 : 0<3^h := Nat.pow_pos (by decide)
  have hmult := Nat.mul_le_mul_left (3^h) hc
  have hbase := Nat.le_mul_of_pos_left 3 h3
  have hpos2 : 0<2^(h+1) := Nat.pow_pos (by decide)
  dsimp [K]
  omega

/-- A universal all-exponent high-valuation obstruction, independent of target
    exponent or other finite congruences. -/
theorem no_high_valuation_power (a h n v : Nat)
    (ha : 2*h+3 ≤ a)
    (heq : (2^(a+1)+1)*(3^h*v)+K h a=2^n) : False := by
  have ha3 : 3 ≤ a := by omega
  have hK : 1<K h a := k_gt_one h a ha3
  have hodd : K h a%2=1 := k_odd h a ha3
  have hhigh : K h a<2^a := k_small_ge h a ha
  have hKi : (1:Int)<(K h a:Int) := by exact_mod_cast hK
  have hOddi : (K h a:Int)%2=1 := by exact_mod_cast hodd
  have hHighi : (K h a:Int)<(2:Int)^a := by exact_mod_cast hhigh
  have hgap := (SheepOddGap.no_power_signed_small_odd a (K h a:Int)
    hKi hOddi hHighi n).1
  have hcast : ((2:Int)^(a+1)+1)*(3^h*v:Int)+(K h a:Int)=(2:Int)^n := by
    exact_mod_cast heq
  have hdiv : ((2:Int)^(a+1)+1) ∣ (2:Int)^n-(K h a:Int) := by
    refine ⟨(3^h*v:Int),?_⟩
    omega
  exact hgap hdiv

/-- For an even Sheep generic source with 2-adic valuation a and hidden odd
    return block h, a power-of-two first-even target requires a<2h+3. -/
theorem no_high_valuation_even_power (j h a v w : Nat)
    (ha : 2*h+3 ≤ a)
    (hy : 2^j = 1+3^h*w)
    (hz : 2*(1+2^h*w)+1=(2^(a+1)+1)*v+2*a) : False := by
  have hcoef : 2*a=(2*a-3)+3 := by omega
  have hpow : 2^(j+h+1)=2^j*(2*2^h) := by
    have he : j+h+1=j+(h+1) := by omega
    rw [he,Nat.pow_add,Nat.pow_succ]
    ac_rfl
  have heq : (2^(a+1)+1)*(3^h*v)+K h a=2^(j+h+1) := by
    rw [hpow,hy]
    dsimp [K]
    rw [hcoef] at hz
    grind
  exact no_high_valuation_power a h (j+h+1) v ha heq

#print axioms no_high_valuation_power
#print axioms no_high_valuation_even_power

#print axioms k_small

#print axioms u_small
end BB6.Agent17Valuation
