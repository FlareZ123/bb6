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

/-- The 9,780-step result is a composition of the already audited
    `block19_1_exact`, `block19_2_exact`, and `terminal1588_exact`,
    together with this generic concatenation lemma.  The predecessor
    audit log carries the component axiom profiles; audit the only new
    logical dependency here rather than re-expanding the large composite. -/
#print axioms BB6.DRegularFast.run_add

end BB6.Agent2NineteenthRoot
