import Std

namespace SheepOddGap

private theorem no_small_multiple (M t : Int)
    (hM : 0<M) (ht : 0<t) (hlt : t<M) (hd : M ∣ t) : False := by
  obtain ⟨z,hz⟩ := hd
  by_cases hz0 : z ≤ 0
  · have hm : M*z≤0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hz0
    omega
  · have hz1 : 1 ≤ z := by omega
    have hm := Int.mul_le_mul_of_nonneg_left hz1 (show 0≤M by omega)
    omega

/-- For odd K strictly between 1 and 2^a, no power of two can be congruent
to either +K or -K modulo 2^(a+1)+1. This is a signed, all-exponent
purely algebraic congruence gap theorem. -/
theorem no_power_signed_small_odd (a : Nat) (K : Int)
    (hK : 1<K) (hodd : K%2=1) (hhigh : K < (2:Int)^a) :
    ∀ n : Nat,
      (¬ ((2:Int)^(a+1)+1) ∣ (2:Int)^n-K) ∧
      (¬ ((2:Int)^(a+1)+1) ∣ (2:Int)^n+K) := by
  let M : Int := (2:Int)^(a+1)+1
  have htwo : (2:Int)^(a+1)=2*(2:Int)^a := by
    rw [Int.pow_succ]
    omega
  have hpos : 0<(2:Int)^a := Int.pow_pos (by decide)
  have hM : 0<M := by dsimp [M]; omega
  have hKlt : 0<K ∧ K<M := by dsimp [M]; omega
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n ≤ a
    · have hpowNat : (2:Nat)^n ≤ 2^a :=
        Nat.pow_le_pow_right (by decide) hn
      have hpow : (2:Int)^n ≤ (2:Int)^a := by
        exact_mod_cast hpowNat
      have hnpos : 0<(2:Int)^n := Int.pow_pos (by decide)
      have hpSmall : (2:Int)^n < M := by dsimp [M]; omega
      have hsum : 0<(2:Int)^n+K ∧ (2:Int)^n+K<M := by
        dsimp [M]
        omega
      have hneq : (2:Int)^n ≠ K := by
        cases n with
        | zero => simp at *; omega
        | succ t =>
          have heven : (2:Int)^(t+1)%2=0 := by
            rw [Int.pow_succ,Int.mul_emod]
            simp
          intro heq
          rw [heq] at heven
          omega
      constructor
      · intro hd
        by_cases hs : K < (2:Int)^n
        · have hdif : 0 < (2:Int)^n-K ∧ (2:Int)^n-K<M := by omega
          exact no_small_multiple M ((2:Int)^n-K) hM hdif.1 hdif.2 hd
        · have hs' : (2:Int)^n<K := by omega
          have hdif : 0<K-(2:Int)^n ∧ K-(2:Int)^n<M := by omega
          have hdneg : M ∣ K-(2:Int)^n := by
            have hv := (Int.dvd_neg).2 hd
            have he : -((2:Int)^n-K)=K-(2:Int)^n := by omega
            rw [he] at hv
            exact hv
          exact no_small_multiple M (K-(2:Int)^n) hM hdif.1 hdif.2 hdneg
      · intro hd
        exact no_small_multiple M ((2:Int)^n+K) hM hsum.1 hsum.2 hd
    · have hnge : a+1≤n := by omega
      let t : Nat := n-(a+1)
      have ht : t<n := by dsimp [t]; omega
      have hnrep : n=(a+1)+t := by dsimp [t]; omega
      have hpow : (2:Int)^n=(2:Int)^(a+1)*(2:Int)^t := by
        rw [hnrep,Int.pow_add]
      have hsum : M ∣ (2:Int)^n+(2:Int)^t := by
        refine ⟨(2:Int)^t,?_⟩
        rw [hpow]
        dsimp [M]
        simp only [Int.add_mul,Int.one_mul]
      obtain ⟨hminus,hplus⟩ := ih t ht
      constructor
      · intro hd
        have hq : M ∣ ((2:Int)^n+(2:Int)^t)-((2:Int)^n-K) :=
          Int.dvd_sub hsum hd
        have heq : ((2:Int)^n+(2:Int)^t)-((2:Int)^n-K) =
            (2:Int)^t+K := by omega
        rw [heq] at hq
        exact hplus hq
      · intro hd
        have hq : M ∣ ((2:Int)^n+(2:Int)^t)-((2:Int)^n+K) :=
          Int.dvd_sub hsum hd
        have heq : ((2:Int)^n+(2:Int)^t)-((2:Int)^n+K) =
            (2:Int)^t-K := by omega
        rw [heq] at hq
        exact hminus hq

#print axioms no_power_signed_small_odd
end SheepOddGap
