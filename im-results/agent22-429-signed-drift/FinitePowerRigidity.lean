import Std

/-! Arithmetic draft: compile with pinned Lean 4.36.0-rc2 before reporting kernel acceptance.
The theorem handles q=n+2 repeated affine-rank macro transfers. -/
namespace PeriodicPower

private def dd (u : Nat → Nat) (i : Nat) : Int :=
  (u (i+2):Int)-2*(u (i+1):Int)+(u i:Int)

private theorem small_divisible_zero (M B : Nat)
    (hbig : 2*B<M) (z : Int)
    (habs : z.natAbs≤2*B) (hdiv : (M:Int) ∣ z) : z=0 := by
  obtain ⟨k,hk⟩ := hdiv
  have heq : z.natAbs=M*k.natAbs := by
    rw [hk,Int.natAbs_mul,Int.natAbs_natCast]
  by_cases hz : k=0
  · simpa [hz] using hk
  · have hp : 1≤k.natAbs := by
      have h := Int.natAbs_pos.mpr hz
      omega
    have hm : M≤M*k.natAbs := by simpa using Nat.mul_le_mul_left M hp
    omega

theorem second_diff_power (M n : Nat) (p c : Int) (u : Nat → Nat)
    (h : ∀ i : Nat, i≤n+1 →
      (M:Int)*(u (i+1):Int)=(u i:Int)+(i:Int)*p+c) :
    dd u 0 = (M:Int)^n * dd u n := by
  have hstep (i : Nat) (hi : i<n) :
      (M:Int)*dd u (i+1)=dd u i := by
    have h0 := h i (by omega)
    have h1 := h (i+1) (by omega)
    have h2 := h (i+2) (by omega)
    have hh1 : (M:Int)*(u (i+2):Int) =
        (u (i+1):Int)+((i+1:Nat):Int)*p+c := by
      simpa [Nat.add_assoc] using h1
    have hh2 : (M:Int)*(u (i+3):Int) =
        (u (i+2):Int)+((i+2:Nat):Int)*p+c := by
      simpa [Nat.add_assoc] using h2
    dsimp [dd]
    grind
  have hpow (k : Nat) (hk : k≤n) :
      dd u 0=(M:Int)^k * dd u k := by
    induction k with
    | zero => simp
    | succ k ih =>
      have prev := ih (by omega)
      have step := hstep k (by omega)
      calc
        dd u 0=(M:Int)^k * dd u k := prev
        _ = (M:Int)^k *((M:Int)*dd u (k+1)) := by rw [step]
        _ = (M:Int)^(k+1)*dd u (k+1) := by simp only [pow_succ,mul_assoc]
  exact hpow n (le_refl n)

theorem power_forces_affine (M B n : Nat) (p c : Int)
    (u : Nat → Nat)
    (hbig : 2*B<M^n)
    (ha : u 0≤B) (hb : u 1≤B) (hc : u 2≤B)
    (h : ∀ i : Nat, i≤n+1 →
      (M:Int)*(u (i+1):Int)=(u i:Int)+(i:Int)*p+c) :
    (u 0:Int)+(u 2:Int)=2*(u 1:Int) ∧
    ((M:Int)-1)*((u 1:Int)-(u 0:Int))=p := by
  have hp := second_diff_power M n p c u h
  have hr : -2*(B:Int)≤dd u 0 ∧ dd u 0≤2*(B:Int) := by
    dsimp [dd]
    omega
  have habs : (dd u 0).natAbs≤2*B := by
    obtain x|x := Int.natAbs_eq (dd u 0)
    · omega
    · omega
  have hdvd : ((M^n:Nat):Int) ∣ dd u 0 := by
    refine ⟨dd u n,?_⟩
    simpa using hp
  have hz := small_divisible_zero (M^n) B hbig (dd u 0) habs hdvd
  have hd : (u 2:Int)-(u 1:Int)=(u 1:Int)-(u 0:Int) := by
    dsimp [dd] at hz
    omega
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have hh0 : (M:Int)*(u 1:Int)=(u 0:Int)+c := by simpa using h0
  have hh1 : (M:Int)*(u 2:Int)=(u 1:Int)+p+c := by simpa using h1
  have hdiff : (M:Int)*((u 2:Int)-(u 1:Int)) =
      ((u 1:Int)-(u 0:Int))+p := by
    calc
      (M:Int)*((u 2:Int)-(u 1:Int)) =
          (M:Int)*(u 2:Int)-(M:Int)*(u 1:Int) := by simp only [mul_sub]
      _ = ((u 1:Int)+p+c)-((u 0:Int)+c) := by rw [hh1,hh0]
      _ = ((u 1:Int)-(u 0:Int))+p := by omega
  constructor
  · omega
  · rw [hd] at hdiff
    calc
      ((M:Int)-1)*((u 1:Int)-(u 0:Int)) =
          (M:Int)*((u 1:Int)-(u 0:Int))-
          ((u 1:Int)-(u 0:Int)) := by simp only [sub_mul,one_mul]
      _ = p := by omega

#print axioms second_diff_power
#print axioms power_forces_affine
end PeriodicPower
