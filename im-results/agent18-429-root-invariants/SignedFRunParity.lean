import Mathlib

namespace BB429SignedFRunParity

/-- A finite run of standalone F-blocks in the compressed signed system. -/
inductive FRun : Nat → Nat → Nat → Nat → Nat → Nat → Prop where
  | zero (u d : Nat) : FRun 0 u d u d
  | step {m u d um dm : Nat} (hu : u % 2 = 0)
      (tail : FRun m (u / 2) (d + 3 * u + 3) um dm) :
      FRun (m + 1) u d um dm

/-- The exact telescoping identity for a run of F-blocks. -/
theorem fRun_rank {m u d um dm : Nat} (h : FRun m u d um dm) :
    dm + 6 * um = d + 6 * u + 3 * m := by
  induction h with
  | zero u d => simp
  | step hu tail ih =>
      have hdiv : u = 2 * (u / 2) := by omega
      omega

/-- The compressed EF block. -/
def ef (v d : Nat) : Nat × Nat :=
  (v + (d + 8) / 8, d / 4 + 4)

/-- The compressed SF block. -/
def sf (v d : Nat) : Nat × Nat :=
  (v + (d + 20) / 8, d / 4 - 1)

/-- Exact affine relation after an EF block. -/
theorem ef_output_relation {v d : Nat} (h8 : d % 8 = 0) :
    (ef v d).2 + 2 * v = 2 * (ef v d).1 + 2 := by
  simp [ef]
  omega

/-- Exact affine relation after an SF block. -/
theorem sf_output_relation {v d : Nat} (h8 : d % 8 = 4) :
    (sf v d).2 + 2 * v + 6 = 2 * (sf v d).1 := by
  simp [sf]
  omega

/-- Initial branch-29 signed state after the forced F has D=2u+18.
    If an F-run from it is followed by EF or SF, its length has the
    corresponding even residue classes modulo 8. -/
theorem initial_run_residues {m u d um dm : Nat}
    (hrel : d = 2 * u + 18)
    (hrun : FRun m u d um dm)
    (hnext :
      (um % 2 = 1 ∧ dm % 8 = 0) ∨
      (um % 2 = 0 ∧ dm % 8 = 4)) :
    (um % 2 = 1 ∧ dm % 8 = 0 ∧ (m % 8 = 0 ∨ m % 8 = 4)) ∨
    (um % 2 = 0 ∧ dm % 8 = 4 ∧ (m % 8 = 2 ∨ m % 8 = 6)) := by
  have hsum := fRun_rank hrun
  rcases hnext with ⟨hu, hd⟩ | ⟨hu, hd⟩
  · left
    exact ⟨hu, hd, by omega⟩
  · right
    exact ⟨hu, hd, by omega⟩

/-- After EF, an F-run followed by EF has length 2 or 6 modulo 8;
    one followed by SF has length 0 or 4 modulo 8. -/
theorem after_ef_run_residues {m u d v um dm : Nat}
    (hrel : d + 2 * v = 2 * u + 2)
    (hv : v % 2 = 1)
    (hrun : FRun m u d um dm)
    (hnext :
      (um % 2 = 1 ∧ dm % 8 = 0) ∨
      (um % 2 = 0 ∧ dm % 8 = 4)) :
    (um % 2 = 1 ∧ dm % 8 = 0 ∧ (m % 8 = 2 ∨ m % 8 = 6)) ∨
    (um % 2 = 0 ∧ dm % 8 = 4 ∧ (m % 8 = 0 ∨ m % 8 = 4)) := by
  have hsum := fRun_rank hrun
  rcases hnext with ⟨hu, hd⟩ | ⟨hu, hd⟩
  · left
    exact ⟨hu, hd, by omega⟩
  · right
    exact ⟨hu, hd, by omega⟩

/-- After SF, an F-run followed by EF has length 0 or 4 modulo 8;
    one followed by SF has length 2 or 6 modulo 8. -/
theorem after_sf_run_residues {m u d v um dm : Nat}
    (hrel : d + 2 * v + 6 = 2 * u)
    (hv : v % 2 = 0)
    (hrun : FRun m u d um dm)
    (hnext :
      (um % 2 = 1 ∧ dm % 8 = 0) ∨
      (um % 2 = 0 ∧ dm % 8 = 4)) :
    (um % 2 = 1 ∧ dm % 8 = 0 ∧ (m % 8 = 0 ∨ m % 8 = 4)) ∨
    (um % 2 = 0 ∧ dm % 8 = 4 ∧ (m % 8 = 2 ∨ m % 8 = 6)) := by
  have hsum := fRun_rank hrun
  rcases hnext with ⟨hu, hd⟩ | ⟨hu, hd⟩
  · left
    exact ⟨hu, hd, by omega⟩
  · right
    exact ⟨hu, hd, by omega⟩

/-- Every F-run from the initial line that is followed by a pair has even length. -/
theorem initial_run_even {m u d um dm : Nat}
    (hrel : d = 2 * u + 18)
    (hrun : FRun m u d um dm)
    (hnext :
      (um % 2 = 1 ∧ dm % 8 = 0) ∨
      (um % 2 = 0 ∧ dm % 8 = 4)) :
    m % 2 = 0 := by
  have h := initial_run_residues hrel hrun hnext
  rcases h with ⟨_, _, hm⟩ | ⟨_, _, hm⟩ <;> omega

/-- Every F-run after EF that is followed by a pair has even length. -/
theorem after_ef_run_even {m u d v um dm : Nat}
    (hrel : d + 2 * v = 2 * u + 2)
    (hv : v % 2 = 1)
    (hrun : FRun m u d um dm)
    (hnext :
      (um % 2 = 1 ∧ dm % 8 = 0) ∨
      (um % 2 = 0 ∧ dm % 8 = 4)) :
    m % 2 = 0 := by
  have h := after_ef_run_residues hrel hv hrun hnext
  rcases h with ⟨_, _, hm⟩ | ⟨_, _, hm⟩ <;> omega

/-- Every F-run after SF that is followed by a pair has even length. -/
theorem after_sf_run_even {m u d v um dm : Nat}
    (hrel : d + 2 * v + 6 = 2 * u)
    (hv : v % 2 = 0)
    (hrun : FRun m u d um dm)
    (hnext :
      (um % 2 = 1 ∧ dm % 8 = 0) ∨
      (um % 2 = 0 ∧ dm % 8 = 4)) :
    m % 2 = 0 := by
  have h := after_sf_run_residues hrel hv hrun hnext
  rcases h with ⟨_, _, hm⟩ | ⟨_, _, hm⟩ <;> omega

#print axioms fRun_rank
#print axioms ef_output_relation
#print axioms sf_output_relation
#print axioms initial_run_residues
#print axioms after_ef_run_residues
#print axioms after_sf_run_residues
#print axioms initial_run_even
#print axioms after_ef_run_even
#print axioms after_sf_run_even

end BB429SignedFRunParity
