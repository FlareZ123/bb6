import DyadicGap
import TwoRunModel

namespace BB6.Agent43TwoRun

private theorem source_small_D (n : Nat) (hn : 14≤n) :
    14*n+92 < 2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn14 : 14≤n
    · have hh := ih hn14
      have ht : 14*(n+1)+92 < 2^n*2 := by omega
      simpa [Nat.succ_eq_add_one,Nat.pow_succ] using ht
    · have hn13 : n=13 := by omega
      subst n
      decide

/-- A true depth-two prefix from the critical scalar root forces its
entire 8^s factor into the *small linear remainder* 14n+92. -/
theorem root_two_prefix_divisor
    (n s : Nat) (Wpre Bpre : Int) (hn : 14≤n)
    (h : TwoRun ((2:Int)^n)
      (14*(2:Int)^n+2*(n:Int)+4) ((n:Int)+6)
      s Wpre Bpre) :
    3*s≤n ∧ (8:Nat)^s ∣ (14*n+92) := by
  let P : Int := (2:Int)^n
  let D : Nat := 14*n+92
  have hsmall := source_small_D n hn
  have henergy := run_energy P (14*P+2*(n:Int)+4) ((n:Int)+6)
    Wpre Bpre s h
  have hroot : I P (14*P+2*(n:Int)+4) ((n:Int)+6) =
      98*P-(D:Int) := by
    unfold I D
    omega
  rw [hroot] at henergy
  have hP : (P:Int) = (↑((2:Nat)^n):Int) := by rfl
  have hpositive : 0 < 98*P-(D:Int) := by
    have hp0 : 0<(2:Nat)^n := Nat.pow_pos (by decide)
    have hcast : (D:Int) < P := by
      simpa only [hP] using (show (↑D:Int) < ↑((2:Nat)^n) from Int.ofNat_lt.mpr hsmall)
    omega
  have hqpos : 0 < (8:Int)^s := Int.pow_pos (by decide)
  have hipos : 0 < I P Wpre Bpre := by
    by_cases he : 0<I P Wpre Bpre
    · exact he
    · have hnot : I P Wpre Bpre≤0 := by omega
      have hprod := Int.mul_nonpos_of_nonneg_of_nonpos (by omega : 0≤(8:Int)^s) hnot
      omega
  let i : Nat := (I P Wpre Bpre).toNat
  have hicast : (↑i:Int)=I P Wpre Bpre :=
    Int.toNat_of_nonneg (by omega)
  have hNatInt : (↑(98*(2:Nat)^n):Int) =
      ↑(i*(8:Nat)^s + D) := by
    have htest : 98*P=(8:Int)^s*(↑i:Int)+(↑D:Int) := by
      have hh : 98*P=(8:Int)^s*I P Wpre Bpre+(↑D:Int) := by omega
      simpa only [←hicast] using hh
    calc
      (↑(98*(2:Nat)^n):Int) = 98*P := by simp only [hP, Int.natCast_mul, Int.natCast_pow]; rfl
      _ = (8:Int)^s*(↑i:Int)+(↑D:Int) := htest
      _ = ↑(i*(8:Nat)^s + D) := by
        simp only [Int.natCast_mul, Int.natCast_pow, Int.natCast_add]
        ac_rfl
  have hNat : 98*(2:Nat)^n = i*(8:Nat)^s + D :=
    Int.ofNat_inj.mp hNatInt
  obtain ⟨hs,hqle⟩ :=
    dyadic_remainder n s i 98 D (by dsimp [D]; omega) hsmall
      (by simpa [Nat.mul_comm] using hNat)
  have hpow : (8:Nat)^s=2^(3*s) := by
    simpa only [show (8:Nat)=2^3 by decide] using (Nat.pow_mul 2 3 s).symm
  have hqdiv : (8:Nat)^s ∣ 2^n := by
    rw [hpow]
    exact Nat.pow_dvd_pow 2 hs
  have hqdiv98 : (8:Nat)^s ∣ 98*2^n := by
    obtain ⟨x,hx⟩ := hqdiv
    exact ⟨98*x, by rw [hx]; ac_rfl⟩
  have hqdivterm : (8:Nat)^s ∣ i*(8:Nat)^s := Nat.dvd_mul_left _ _
  have hdiff : 98*2^n - i*8^s=D := by omega
  have hqdivD := Nat.dvd_sub hqdiv98 hqdivterm
  rw [hdiff] at hqdivD
  exact ⟨hs,hqdivD⟩

#print axioms BB6.Agent43TwoRun.root_two_prefix_divisor
end BB6.Agent43TwoRun