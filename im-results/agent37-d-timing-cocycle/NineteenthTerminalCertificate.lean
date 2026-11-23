import NineteenthBlock3

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2NineteenthRoot

open DRegular BB6.DRegularFast

/-- Exact 9,780-step terminal certificate, composed from the three
    independently kernel-checked arithmetic blocks (4,096 + 4,096 + 1,588). -/
theorem terminal9780_exact :
    run 9780 seed19 = some ⟨9*t19+10,9,1⟩ := by
  rw [show 9780 = 4096 + (4096 + 1588) by decide,
    BB6.DRegularFast.run_add]
  rw [block19_1_exact]
  change run (4096 + 1588) block19_1 = some ⟨9*t19+10,9,1⟩
  rw [BB6.DRegularFast.run_add]
  rw [block19_2_exact]
  change run 1588 block19_2 = some ⟨9*t19+10,9,1⟩
  exact terminal1588_exact

theorem t19_mod27_exact : t19 % 27 = 12 :=
  t19_mod27

private def haltingCylinderC : Nat :=
  1975700577069254261393123959451562008800234946348086

/-- The nineteenth reentry parameter is zero modulo three. -/
theorem t19_mod3 : t19 % 3 = 0 := by
  have h := t19_mod27_exact
  omega

/-- The pure-unary parameter after the nineteenth E/A packet is 2 mod 3. -/
theorem root19_unary_mod3 : (64*t19+113) % 3 = 2 := by
  have h := t19_mod3
  omega

/-- Consequently the nineteenth pure-unary reentry misses the external
    TM62 halting cylinder C + 3^108*k for every natural k. -/
theorem root19_reentry_misses_cylinder :
    ∀ k : Nat, 64*t19+113 ≠ haltingCylinderC + 3^108*k := by
  intro k h
  have hmod := congrArg (fun n : Nat => n % 3) h
  have hC : haltingCylinderC % 3 = 1 := by norm_num [haltingCylinderC]
  have hp : (3^108*k) % 3 = 0 := by norm_num
  have hleft := root19_unary_mod3
  have hright : (haltingCylinderC + 3^108*k) % 3 = 1 := by omega
  omega

#print axioms terminal9780_exact
#print axioms t19_mod27_exact
#print axioms root19_reentry_misses_cylinder

end BB6.Agent2NineteenthRoot
