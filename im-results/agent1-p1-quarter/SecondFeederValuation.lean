import P1TwoSector
import QuarterGap
namespace BB6.Agent1Quarter
open BB6.Agent45TwoRoot

private theorem feeder_shift_identity (q : Nat) (hq : 1≤q) :
    5*u2 q+7 + 4*(5*q+2) = 35*2^(16*q) := by
  have hp:=pow16_dom q hq
  simp only [u2]
  omega

private theorem feeder_shift_small (q t:Nat) (hq:1≤q)
    (ht:t+2≤16*q) :
    (2^(t+2) ∣ 5*u2 q+7) ↔ (2^t ∣ 5*q+2) := by
  have hi:=feeder_shift_identity q hq
  have hd : 2^(t+2) ∣ 35*2^(16*q) := by
    obtain ⟨z,hz⟩ := Nat.pow_dvd_pow 2 ht
    refine ⟨35*z,?_⟩
    rw [hz]
    ac_rfl
  have hp : 2^(t+2)=4*2^t := by
    have hh:t+2=2+t:=by omega
    rw [hh,Nat.pow_add]
  have hc : (2^(t+2) ∣ 4*(5*q+2)) ↔ (2^t ∣ 5*q+2) := by
    rw [hp]
    exact Nat.mul_dvd_mul_iff_left (by decide : 0<4)
  have hsub1 : 35*2^(16*q) -(5*u2 q+7)=4*(5*q+2) := by omega
  have hsub2 : 35*2^(16*q) -4*(5*q+2)=5*u2 q+7 := by omega
  constructor
  · intro h
    exact hc.mp (hsub1 ▸ Nat.dvd_sub hd h)
  · intro h
    exact hsub2 ▸ Nat.dvd_sub hd (hc.mpr h)

private theorem feeder_shift_not_big (q:Nat) (hq:1≤q) :
    ¬ (2^(16*q) ∣ 5*u2 q+7) := by
  intro hv
  have hi:=feeder_shift_identity q hq
  have hd : 2^(16*q) ∣ 35*2^(16*q) := by
    refine ⟨35,?_⟩
    ac_rfl
  have hsub : 35*2^(16*q)-(5*u2 q+7)=4*(5*q+2) := by omega
  have hm : 2^(16*q) ∣ 4*(5*q+2) := by
    rw [←hsub]
    exact Nat.dvd_sub hd hv
  have hp:=pow16_dom q hq
  have hbound:4*(5*q+2)<2^(16*q) := by omega
  have hle : 2^(16*q) ≤ 4*(5*q+2) :=
    Nat.le_of_dvd (by omega) hm
  omega

/-- All-index 2-adic valuation of Agent45's L1 G-inverse shifted output s,
    complementary to their l1_all_powers for the L1 left-coordinate +12. -/
theorem second_feeder_shift_all_powers (q t:Nat) (hq:1≤q) :
    (2^(t+2) ∣ 5*u2 q+7) ↔ (2^t ∣ 5*q+2) := by
  by_cases ht : t+2 ≤ 16*q
  · exact feeder_shift_small q t hq ht
  have hn : 16*q < t+2 := by omega
  have hnotleft : ¬ (2^(t+2) ∣ 5*u2 q+7) := by
    intro h
    have hd : 2^(16*q) ∣ 2^(t+2) :=
      Nat.pow_dvd_pow 2 (by omega)
    exact feeder_shift_not_big q hq (Nat.dvd_trans hd h)
  have hnotright : ¬ (2^t ∣ 5*q+2) := by
    intro h
    have hp:=pow16_dom q hq
    have hc : 2^(16*q)=4*2^(16*q-2) := by
      have he:16*q=(16*q-2)+2:=by omega
      calc
        2^(16*q)=2^((16*q-2)+2) := congrArg (fun n:Nat => 2^n) he
        _=4*2^(16*q-2):=by rw [Nat.pow_add]; omega
    have hsmall:5*q+2 < 2^(16*q-2):=by omega
    have hd : 2^(16*q-2) ∣ 2^t := Nat.pow_dvd_pow 2 (by omega)
    have hdiv : 2^(16*q-2) ∣ 5*q+2 := Nat.dvd_trans hd h
    have hge : 2^(16*q-2) ≤ 5*q+2 :=
      Nat.le_of_dvd (by omega) hdiv
    omega
  simp [hnotleft,hnotright]

#print axioms second_feeder_shift_all_powers
end BB6.Agent1Quarter
