import NineteenthBlock3
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2NineteenthRoot

open DRegular

theorem run_concat {m n : Nat} {s u t : L}
    (h1 : run m s = some u) (h2 : run n u = some t) :
    run (m+n) s = some t := by
  rw [BB6.DRegularFast.run_add m n s, h1]
  simpa using h2

theorem first8192_exact :
    run 8192 seed19 = some block19_2 := by
  have h := run_concat block19_1_exact block19_2_exact
  simpa using h

/-- Exact 9,780-section DRegular endpoint, assembled from three
    independently compiled arithmetic checkpoints. -/
theorem terminal9780_exact :
    run 9780 seed19 = some ⟨9*t19+10,9,1⟩ := by
  have hfirst := first8192_exact
  have hlen : 9780 = 8192+1588 := by omega
  calc
    run 9780 seed19 = run (8192+1588) seed19 :=
      congrArg (fun n => run n seed19) hlen
    _ = (run 8192 seed19).bind (run 1588) :=
      BB6.DRegularFast.run_add 8192 1588 seed19
    _ = (some block19_2).bind (run 1588) := by rw [hfirst]
    _ = run 1588 block19_2 := rfl
    _ = some ⟨9*t19+10,9,1⟩ := terminal1588_exact

theorem t19_mod27_exact : t19 % 27 = 12 :=
  t19_mod27

#print axioms terminal9780_exact
#print axioms t19_mod27_exact

end BB6.Agent2NineteenthRoot
