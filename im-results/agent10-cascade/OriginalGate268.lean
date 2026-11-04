import OriginalAlgorithmicGate
import FastCone257
import FastCone262
import FastCone263

namespace Agent10Raw746
open BusyBeaver
open BusyBeaver.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA
open CascadeResetInverse

/-- Kernel-certifying the first three surviving-index reverse cones makes
    the original raw six-state blank-machine halting gate strictly sharper. -/
private theorem excluded257 :
    rootReachBool (4*2^257-257-4) ≠ true := by
  intro h
  have he : 4*2^257-257-4 =
    926336713898529563388567880069503262826159877325124512315660672063305037119227 := by decide
  rw [he] at h
  exact blank_excludes_fatal_257 ((rootReachBool_source_iff _).mp h)

private theorem excluded262 :
    rootReachBool (4*2^262-262-4) ≠ true := by
  intro h
  have he : 4*2^262-262-4 =
    29642774844752946028434172162224104410437116074403984394101141506025761187823350 := by decide
  rw [he] at h
  exact blank_excludes_fatal_262 ((rootReachBool_source_iff _).mp h)

private theorem excluded263 :
    rootReachBool (4*2^263-263-4) ≠ true := by
  intro h
  have he : 4*2^263-263-4 =
    59285549689505892056868344324448208820874232148807968788202283012051522375646965 := by decide
  rw [he] at h
  exact blank_excludes_fatal_263 ((rootReachBool_source_iff _).mp h)

/-- Genuine original six-state blank Turing machine: only fatal indices at
    least 268 remain after complete source-reset reverse-cone exclusions.
    This is an infinite existential and proves no global halting verdict. -/
theorem original_machine_halts_iff_surviving_268 :
    IsHalt target ↔
      ∃ n, 268≤n ∧ (n%6=4 ∨ n%6=5) ∧
        rootReachBool (4*2^n-n-4)=true := by
  rw [original_machine_halts_iff_algorithmic_gate]
  constructor
  · rintro ⟨n,hn,hm,hr⟩
    by_cases hbig : 268≤n
    · exact ⟨n,hbig,hm,hr⟩
    · have hcases : n=257 ∨ n=262 ∨ n=263 := by omega
      rcases hcases with rfl | rfl | rfl
      · exact False.elim (excluded257 hr)
      · exact False.elim (excluded262 hr)
      · exact False.elim (excluded263 hr)
  · rintro ⟨n,hn,hm,hr⟩
    exact ⟨n,by omega,hm,hr⟩

#print axioms original_machine_halts_iff_surviving_268
end Agent10Raw746
