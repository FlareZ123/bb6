import P1TwoSector

namespace BB6.Agent45TwoValuation
open BB6.Agent45TwoRoot

private theorem big16 (r : Nat) :
    24*(r+1)+32 < 2^(16*(r+1)) := by
  induction r with
  | zero => decide
  | succ r ih =>
      have hp : 2^(16*(r+1+1))=65536*2^(16*(r+1)) := by
        have he : 16*(r+1+1)=16*(r+1)+16 := by omega
        rw [he,Nat.pow_add, show (2:Nat)^16=65536 by decide]
        omega
      rw [show r+1+1=r+2 by omega, show 16*(r+2)=16*(r+1+1) by omega, hp]
      omega

private theorem pow16_big (q : Nat) (hq : 1≤q) :
    8*(3*q+1) < 2^(16*q) := by
  cases q with
  | zero => omega
  | succ r =>
      have hb:=big16 r
      omega

private theorem l1_mass_identity (q : Nat) (hq : 1≤q) :
    6*u2 q+10 + 8*(3*q+1)=42*2^(16*q) := by
  have hb:=pow16_big q hq
  simp only [u2]
  omega

private theorem l1_shift_div_iff_small (q t : Nat) (hq : 1≤q)
    (ht : t+3 ≤ 16*q) :
    (2^(t+3) ∣ 6*u2 q+10) ↔ (2^t ∣ 3*q+1) := by
  have hG := l1_mass_identity q hq
  have hdiv : 2^(t+3) ∣ 42*2^(16*q) := by
    obtain ⟨z,hz⟩ := Nat.pow_dvd_pow 2 ht
    refine ⟨42*z, ?_⟩
    rw [hz]
    ac_rfl
  have hpow : 2^(t+3)=8*2^t := by
    have he : t+3=3+t := by omega
    rw [he,Nat.pow_add]
  have hcancel : (2^(t+3) ∣ 8*(3*q+1)) ↔ (2^t ∣ 3*q+1) := by
    rw [hpow]
    exact Nat.mul_dvd_mul_iff_left (by decide : 0<8)
  have hsub1 : 42*2^(16*q) - (6*u2 q+10) = 8*(3*q+1) := by omega
  have hsub2 : 42*2^(16*q) - 8*(3*q+1) = 6*u2 q+10 := by omega
  constructor
  · intro hv
    exact hcancel.mp (hsub1 ▸ Nat.dvd_sub hdiv hv)
  · intro hv
    exact hsub2 ▸ Nat.dvd_sub hdiv (hcancel.mpr hv)

private theorem l1_not_pow16 (q : Nat) (hq : 1≤q) :
    ¬ (2^(16*q) ∣ 6*u2 q+10) := by
  intro hv
  have hG := l1_mass_identity q hq
  have hdiv : 2^(16*q) ∣ 42*2^(16*q) := by
    refine ⟨42,?_⟩
    ac_rfl
  have hh : 42*2^(16*q)-(6*u2 q+10)=8*(3*q+1) := by omega
  have hm : 2^(16*q) ∣ 8*(3*q+1) := by
    rw [←hh]
    exact Nat.dvd_sub hdiv hv
  have hp := pow16_big q hq
  have hle : 2^(16*q) ≤ 8*(3*q+1) :=
    Nat.le_of_dvd (by omega) hm
  omega

private theorem l1_no_big_rhs (q t : Nat) (hq : 1≤q)
    (ht : 16*q < t+3) :
    ¬ (2^t ∣ 3*q+1) := by
  intro hv
  have hp := pow16_big q hq
  have he : 2^(16*q)=4*2^(16*q-2) := by
    have e : 16*q=(16*q-2)+2 := by omega
    calc
      2^(16*q) = 2^((16*q-2)+2) := congrArg (fun n : Nat => 2^n) e
      _ = 2^(16*q-2)*4 := by rw [Nat.pow_add]
      _ = 4*2^(16*q-2) := by omega
  have hm : 3*q+1 < 2^(16*q-2) := by omega
  have hdiv : 2^(16*q-2) ∣ 2^t :=
    Nat.pow_dvd_pow 2 (by omega)
  have hsmall : 2^(16*q-2) ∣ 3*q+1 := Nat.dvd_trans hdiv hv
  have hg := Nat.le_of_dvd (by omega : 0<3*q+1) hsmall
  omega

/-- Exact 2-adic shift on the *middle-branch* feeder for every n=16q+2.
    Compare Agent33's homogeneous upper depth anchored at B(n): this identity
    instead controls arbitrary upper depth at the second feeder. -/
theorem l1_all_powers (q t : Nat) (hq : 1≤q) :
    (2^(t+3) ∣ 6*u2 q+10) ↔ (2^t ∣ 3*q+1) := by
  by_cases ht : t+3 ≤16*q
  · exact l1_shift_div_iff_small q t hq ht
  have hn : 16*q < t+3 := by omega
  have hnotLeft : ¬(2^(t+3) ∣ 6*u2 q+10) := by
    intro h
    have hdiv : 2^(16*q) ∣ 2^(t+3) :=
      Nat.pow_dvd_pow 2 (by omega)
    exact l1_not_pow16 q hq (Nat.dvd_trans hdiv h)
  have hnotRight := l1_no_big_rhs q t hq hn
  simp [hnotLeft,hnotRight]

/-- Every power of two dividing 3q+1 yields that many *genuine* upper
    inverse pairs through the other live critical feeder, followed by
    the exact non-upper middle pair. The start is synthetic, not blank. -/
theorem mixed_depth_exists (q t : Nat) (hq : 1≤q)
    (hpower : 2^t ∣ 3*q+1) :
    ∃ s : Nat × Nat,
      BB6.Agent45Deep2.PairPath (t+2) s (8*u2 q+4,3) := by
  let pow := 2^(t+3)
  let m := 3*q+1
  let D := 6*u2 q+10
  have hdiv : pow ∣ D := (l1_all_powers q t hq).mpr hpower
  obtain ⟨z,hz⟩ := hdiv
  have hp := pow16_big q hq
  have hm := l1_mass_identity q hq
  have hpow : pow=8*2^t := by
    simp only [pow]
    have he : t+3=3+t := by omega
    rw [he,Nat.pow_add]
  have hsmall : pow ≤ 8*m := by
    have hs : 2^t ≤ m := Nat.le_of_dvd (by omega) hpower
    dsimp only [m]
    rw [hpow]
    omega
  have h4 : 4*pow ≤ D := by
    dsimp only [D,m] at *
    omega
  have hpowpos : 0<pow := Nat.pow_pos (by decide)
  have hz4 : 4≤z := by
    have hh : pow*4 ≤ pow*z := by
      rw [←hz]
      simpa only [Nat.mul_comm] using h4
    exact Nat.le_of_mul_le_mul_left hh hpowpos
  let seed := 4*z-12
  have hs : seed%4=0 ∧ seed+12=4*z := by
    dsimp only [seed]
    omega
  have halign : BB6.Agent45Deep2.upper seed (t+1)=6*u2 q-2 := by
    have hsize:=BB6.Agent45Deep2.upper_size seed (t+1)
    have ht2 : 2^(t+1)=2*2^t := by rw [Nat.pow_succ]; omega
    have hsz : BB6.Agent45Deep2.upper seed (t+1)+12=D := by
      calc
        BB6.Agent45Deep2.upper seed (t+1)+12 = 2^(t+1)*(seed+12) := hsize
        _ = 2^(t+1)*4*z := by rw [hs.2]; simp only [Nat.mul_assoc]
        _ = pow*z := by
          rw [hpow,ht2]
          calc
            (2*2^t)*4*z = (2*4)*(2^t*z) := by ac_rfl
            _ = (8*2^t)*z := by simp [Nat.mul_assoc]
        _ = D := hz.symm
    dsimp only [D] at hsz
    omega
  obtain ⟨s,hchain⟩ := BB6.Agent45Deep2.upper_chain
    seed (t+1) (2*u2 q+5) hs.1
  have hchain' : BB6.Agent45Deep2.PairPath (t+1) s
      (6*u2 q-2,2*u2 q+5) := by
    rw [halign] at hchain
    exact hchain
  have hpair := BB6.Agent45Deep2.middle_pair (u2 q) (by
    have hpowbig:=pow16_big q hq
    dsimp [u2]
    omega)
  refine ⟨s,?_⟩
  exact BB6.Agent45Deep2.PairPath.extend hchain' hpair.1 hpair.2

#print axioms mixed_depth_exists

#print axioms l1_all_powers
end BB6.Agent45TwoValuation
