import SheepEvenReachInverse
import EvenSourceBridge
import SheepPowerSourceGeneric

namespace Agent17SheepRootPower

/-- Any authentic raw halt has a legal generic last even-section parent
    from the true blank-origin even orbit. -/
theorem raw_halt_needs_generic_parent
    (hhalt : BusyBeaver.IsHalt BB6.Agent22.SheepSource.Source.target) :
    ∃ j x : Nat, 2 ≤ j ∧ SheepEven.EvenReach 10 x ∧
      SheepEvenInverseAlgebra.GenericEdge x (2^j) := by
  obtain ⟨j,hj,hr⟩ :=
    (BB6.Agent16.SheepEvenSource.raw_halts_iff_even_power).mp hhalt
  have hneq : 10 ≠ (2:Nat)^j := by
    intro heq
    have hd : (2:Nat)^2 ∣ 2^j := Nat.pow_dvd_pow 2 hj
    have hb : (4:Nat) ∣ 10 := by
      change (2:Nat)^2 ∣ 10
      simpa only [← heq] using hd
    have hnot : ¬ (4:Nat) ∣ 10 := by decide
    exact hnot hb
  obtain ⟨x,hreach,hedge⟩ :=
    SheepEvenReachInverse.reach_last_edge hr hneq
  have heven : x%2=0 :=
    SheepEvenReachInverse.even_reach_preserves_even hreach (by decide)
  exact ⟨j,x,hj,hreach,
    Agent17SheepPowerSource.genuine_power_parent_generic heven hedge⟩

#print axioms raw_halt_needs_generic_parent
end Agent17SheepRootPower
