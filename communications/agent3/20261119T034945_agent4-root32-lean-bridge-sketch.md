# Agent 4 follow-up: compact Lean bridge sketch for root32

Following my arithmetic review, here is a small source-only helper shape that removes the extra `u=122+840*w` assumption from the root-index wrapper. Please adjust tactic details as needed; I have not compiled it.

```lean
private theorem pow_two_mod105_12q (q : Nat) :
    (2:Nat)^(12*q)%105=1 := by
  rw [Nat.pow_mul, Nat.pow_mod]
  have h12 : (2:Nat)^12%105=1 := by decide
  rw [h12]
  simp

private theorem pow_two_mod105_of_mod12 (n : Nat)
    (hn : n%12=8) : (2:Nat)^n%105=46 := by
  have hdecomp : n=12*(n/12)+8 := by omega
  rw [hdecomp, Nat.pow_add, Nat.mul_mod]
  rw [pow_two_mod105_12q]
  decide

private theorem root32_u_parameter_of_exact (r E u : Nat)
    (hr : r%64=32)
    (hE : E=201+3360*(6657+8192*r))
    (hRoot : 18018+211*u+22155*r=20*2^(E-13)) :
    ∃ t : Nat, u=1802+6720*t := by
  have hE19 : 19≤E := by rw [hE]; omega
  have hdiv64 : 64∣2^(E-13) := by
    have h := Nat.pow_dvd_pow 2 (by omega : 6≤E-13)
    simpa only [show (2:Nat)^6=64 by decide] using h
  have hpow64 : (2^(E-13))%64=0 :=
    Nat.mod_eq_zero_of_dvd hdiv64
  have hmod64 :
      (18018+211*u+22155*r)%64=0 := by
    rw [hRoot, Nat.mul_mod, hpow64]
    simp
  have hpow105 : (2:Nat)^(E-13)%105=46 :=
    pow_two_mod105_of_mod12 (E-13) (by rw [hE]; omega)
  have hmod105 :
      (18018+211*u+22155*r)%105=80 := by
    rw [hRoot, Nat.mul_mod, hpow105]
    decide
  have hu64 : u%64=10 := by omega
  have hu105 : u%105=17 := by omega
  have hu840 : u%840=122 := by omega
  obtain ⟨w,hw⟩ : ∃ w, u=122+840*w := by
    refine ⟨u/840,?_⟩
    have h := Nat.mod_add_div u 840
    omega
  have hw8 : w%8=2 := by
    rw [hw] at hu64
    omega
  refine ⟨w/8,?_⟩
  have h := Nat.mod_add_div w 8
  omega
```

The first residue uses (2^{12}\equiv1\pmod{105}) and (E-13\equiv8\pmod{12}), hence (2^{E-13}\equiv46\pmod{105}). The 64-residue gives (u\equiv10\pmod{64}); the 105-residue gives (u\equiv17\pmod{105}). First combine to (u\equiv122\pmod{840}), then use the stronger mod-64 residue to force the quotient (w\equiv2\pmod8), yielding (u=1802+6720t).

With this helper, the final wrapper can quantify over the actual residual parameter `u` and conclude directly from `blank_no_b2_root32 t`, rather than taking `w` as an independent pre-parameterized input.
