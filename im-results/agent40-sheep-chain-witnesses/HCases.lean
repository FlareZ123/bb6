import SheepPeriodicGate
import SheepHBound
namespace SheepHCases

theorem hstop_r402_n0 (k : Nat) :
    2^(402+4860*k)%27 ≠ 1%27 := by
  simpa only [Nat.add_zero] using
    (SheepPeriodicGate.no_shifted_mod_class 27 402 0 1 1
      (by decide) (by decide) (by rw [←Nat.powMod_def]; decide)
      (by simpa only [Nat.powMod_def, Nat.add_zero] using
        (show ∀ t : Fin 1, Nat.powMod 2 (402+4860*t.val) 27 ≠ 1%27
          from by decide)) k)

theorem hstop_r402_n1 (k : Nat) :
    2^(405+4860*k)%135 ≠ 17%135 := by
  simpa only [Nat.add_zero] using
    (SheepPeriodicGate.no_shifted_mod_class 135 405 0 17 1
      (by decide) (by decide) (by rw [←Nat.powMod_def]; decide)
      (by simpa only [Nat.powMod_def, Nat.add_zero] using
        (show ∀ t : Fin 1, Nat.powMod 2 (405+4860*t.val) 135 ≠ 17%135
          from by decide)) k)

theorem hstop_r402_n2 (k : Nat) :
    2^(411+4860*k)%13365 ≠ 6173%13365 := by
  simpa only [Nat.add_zero] using
    (SheepPeriodicGate.no_shifted_mod_class 13365 411 0 6173 1
      (by decide) (by decide) (by rw [←Nat.powMod_def]; decide)
      (by simpa only [Nat.powMod_def, Nat.add_zero] using
        (show ∀ t : Fin 1, Nat.powMod 2 (411+4860*t.val) 13365 ≠ 6173%13365
          from by decide)) k)

theorem hstop_r1738_n0 (k : Nat) :
    2^(1738+4860*k)%9 ≠ 1%9 := by
  simpa only [Nat.add_zero] using
    (SheepPeriodicGate.no_shifted_mod_class 9 1738 0 1 1
      (by decide) (by decide) (by rw [←Nat.powMod_def]; decide)
      (by simpa only [Nat.powMod_def, Nat.add_zero] using
        (show ∀ t : Fin 1, Nat.powMod 2 (1738+4860*t.val) 9 ≠ 1%9
          from by decide)) k)

theorem hstop_r1738_n1 (k : Nat) :
    2^(1741+4860*k)%45 ≠ 17%45 := by
  simpa only [Nat.add_zero] using
    (SheepPeriodicGate.no_shifted_mod_class 45 1741 0 17 1
      (by decide) (by decide) (by rw [←Nat.powMod_def]; decide)
      (by simpa only [Nat.powMod_def, Nat.add_zero] using
        (show ∀ t : Fin 1, Nat.powMod 2 (1741+4860*t.val) 45 ≠ 17%45
          from by decide)) k)

theorem hstop_r1738_n2 (k : Nat) :
    2^(1744+4860*k)%3645 ≠ 331%3645 := by
  simpa only [Nat.add_zero] using
    (SheepPeriodicGate.no_shifted_mod_class 3645 1744 0 331 1
      (by decide) (by decide) (by rw [←Nat.powMod_def]; decide)
      (by simpa only [Nat.powMod_def, Nat.add_zero] using
        (show ∀ t : Fin 1, Nat.powMod 2 (1744+4860*t.val) 3645 ≠ 331%3645
          from by decide)) k)

#print axioms hstop_r402_n2
#print axioms hstop_r1738_n2
end SheepHCases
