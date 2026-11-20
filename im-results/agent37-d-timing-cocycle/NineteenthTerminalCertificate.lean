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
  exact run_concat block19_1_exact block19_2_exact

/-- Exact 9,780-section DRegular endpoint, assembled from three
    independently compiled arithmetic checkpoints. -/
theorem terminal9780_exact :
    run 9780 seed19 = some ⟨9*t19+10,9,1⟩ := by
  /- Compose through the two 4,096-section checkpoints.  This avoids
     instantiating run_add with an 8,192-step induction. -/
  have htail :
      run (4096+1588) block19_1 = some ⟨9*t19+10,9,1⟩ :=
    run_concat block19_2_exact terminal1588_exact
  have hlen : 9780 = 4096+(4096+1588) := by omega
  calc
    run 9780 seed19 = run (4096+(4096+1588)) seed19 :=
      congrArg (fun n => run n seed19) hlen
    _ = (run 4096 seed19).bind (run (4096+1588)) :=
      BB6.DRegularFast.run_add 4096 (4096+1588) seed19
    _ = (some block19_1).bind (run (4096+1588)) := by rw [block19_1_exact]
    _ = run (4096+1588) block19_1 := rfl
    _ = some ⟨9*t19+10,9,1⟩ := htail

theorem t19_mod27_exact : t19 % 27 = 12 :=
  t19_mod27

#print axioms terminal9780_exact
#print axioms t19_mod27_exact

end BB6.Agent2NineteenthRoot
