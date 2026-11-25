import SignedFRunParity

namespace BB429SignedBranch13_15

open BB429SignedFRunParity

/-- The branch-13 family after its forced first signed F block. -/
def branch13U (k : Nat) : Nat := 48 * k + 24
def branch13D (k : Nat) : Nat := 96 * k + 66

/-- The branch-15 family after its forced first signed F block. -/
def branch15U (k : Nat) : Nat := 48 * k + 39
def branch15D (k : Nat) : Nat := 96 * k + 96

/-- Branch 13 has no paired block at the initial state or after one F. -/
theorem branch13_no_pair_at_start (k : Nat) :
    ¬ (((branch13U k) % 2 = 1 ∧ (branch13D k) % 8 = 0) ∨
       ((branch13U k) % 2 = 0 ∧ (branch13D k) % 8 = 4)) := by
  simp [branch13U, branch13D]
  omega

theorem branch13_no_pair_after_one_F (k : Nat) :
    ¬ (((24 * k + 12) % 2 = 1 ∧ (240 * k + 141) % 8 = 0) ∨
       ((24 * k + 12) % 2 = 0 ∧ (240 * k + 141) % 8 = 4)) := by
  omega

/-- The exact two-F prefix from branch 13, ending at the first SF guard. -/
theorem branch13_two_F_run (k : Nat) :
    FRun 2 (branch13U k) (branch13D k) (12 * k + 6) (312 * k + 180) := by
  have hdiv1 : (24 * k + 12) / 2 = 12 * k + 6 := by omega
  have hstepD : 240 * k + 141 + 3 * (24 * k + 12) + 3 =
      312 * k + 180 := by omega
  have hrun1 :
      FRun 1 (24 * k + 12) (240 * k + 141)
        (12 * k + 6) (312 * k + 180) := by
    refine FRun.step ?_ ?_
    · omega
    · rw [hdiv1, hstepD]
      exact FRun.zero _ _
  have hdiv0 : branch13U k / 2 = 24 * k + 12 := by
    simp [branch13U]
    omega
  have hstep0D :
      branch13D k + 3 * branch13U k + 3 = 240 * k + 141 := by
    simp [branch13U, branch13D]
    omega
  have hrun1' :
      FRun 1 (branch13U k / 2)
        (branch13D k + 3 * branch13U k + 3)
        (12 * k + 6) (312 * k + 180) := by
    rw [hdiv0, hstep0D]
    exact hrun1
  have hUeven : (branch13U k) % 2 = 0 := by
    change (48 * k + 24) % 2 = 0
    omega
  exact FRun.step hUeven hrun1'

/-- The first available pair on branch 13 is SF after exactly two F blocks. -/
theorem branch13_first_SF (k : Nat) :
    (12 * k + 6) % 2 = 0 ∧
    (312 * k + 180) % 8 = 4 ∧
    sf (12 * k + 6) (312 * k + 180) =
      (51 * k + 31, 78 * k + 44) := by
  constructor
  · omega
  constructor
  · omega
  · simp [sf]
    omega

/-- The next immediate branch choices after branch 13's first SF. -/
theorem branch13_post_SF_guards (k : Nat) :
    ((k % 4 = 0) →
      (51 * k + 31) % 2 = 1 ∧ (78 * k + 44) % 8 = 4) ∧
    ((k % 4 = 2) →
      (51 * k + 31) % 2 = 1 ∧ (78 * k + 44) % 8 = 0) ∧
    ((k % 2 = 1) →
      (51 * k + 31) % 2 = 0 ∧
        ((78 * k + 44) % 8 = 2 ∨ (78 * k + 44) % 8 = 6)) := by
  constructor
  · intro h
    omega
  constructor
  · intro h
    omega
  · intro h
    omega

/-- Branch 15 begins with the forced EF block. -/
theorem branch15_first_E (k : Nat) :
    (branch15U k) % 2 = 1 ∧
    (branch15D k) % 8 = 0 ∧
    ef (branch15U k) (branch15D k) =
      (60 * k + 52, 24 * k + 28) := by
  constructor
  · change (48 * k + 39) % 2 = 1
    omega
  constructor
  · change (96 * k + 96) % 8 = 0
    omega
  · change ef (48 * k + 39) (96 * k + 96) =
      (60 * k + 52, 24 * k + 28)
    simp [ef]
    omega

/-- After branch 15's forced EF, an immediate SF is also available. -/
theorem branch15_optional_SF (k : Nat) :
    (60 * k + 52) % 2 = 0 ∧
    (24 * k + 28) % 8 = 4 ∧
    sf (60 * k + 52) (24 * k + 28) =
      (63 * k + 58, 6 * k + 6) := by
  constructor
  · omega
  constructor
  · omega
  · simp [sf]
    omega

/-- The next immediate branch choices after branch 15 takes EF then SF. -/
theorem branch15_post_ES_guards (k : Nat) :
    ((k % 4 = 1) →
      (63 * k + 58) % 2 = 1 ∧ (6 * k + 6) % 8 = 4) ∧
    ((k % 4 = 3) →
      (63 * k + 58) % 2 = 1 ∧ (6 * k + 6) % 8 = 0) ∧
    ((k % 2 = 0) →
      (63 * k + 58) % 2 = 0 ∧
        ((6 * k + 6) % 8 = 2 ∨ (6 * k + 6) % 8 = 6)) := by
  constructor
  · intro h
    omega
  constructor
  · intro h
    omega
  · intro h
    omega

/-- The power of two consumed by an F-run, viewed in the integer ring. -/
def pow2I (m : Nat) : Int := (2 : Int) ^ m

/-- Defect coordinate D - 8(2^m u - u), written without distributive rewriting. -/
def defect (m : Nat) (d u : Int) : Int :=
  d - (8 * (pow2I m * u) - 8 * u)

/--
The exact endpoint defect identities for EF followed by an F-run.
Writing q=2^m, the endpoint defect is 2(w-v)+2+3m, while the
input defect is 8(qw-qv)-8.
-/
theorem ef_macro_defect_components {m v d um dm : Nat}
    (h8 : d % 8 = 0)
    (hrun : FRun m (ef v d).1 (ef v d).2 um dm) :
    (defect m (dm : Int) (um : Int) =
        2 * ((um : Int) - (v : Int)) + 2 + 3 * (m : Int)) ∧
    (defect m (d : Int) (v : Int) =
        8 * (pow2I m * (um : Int)) -
          8 * (pow2I m * (v : Int)) - 8) := by
  have hsumN := fRun_rank hrun
  have hpowN := fRun_power hrun
  have hrelN := ef_output_relation (v := v) h8
  have hcoordN : 8 * (ef v d).1 = 8 * v + d + 8 := by
    simp [ef]
    omega
  have hsumI :
      (dm : Int) + 6 * (um : Int) =
        (ef v d).2 + 6 * (ef v d).1 + 3 * (m : Int) := by
    exact_mod_cast hsumN
  have hpowI :
      (ef v d).1 = pow2I m * (um : Int) := by
    change (ef v d).1 = (2 : Int) ^ m * (um : Int)
    exact_mod_cast hpowN
  have hrelI :
      (ef v d).2 + 2 * (v : Int) =
        2 * (ef v d).1 + 2 := by
    exact_mod_cast hrelN
  have hcoordI' :
      (8 : Int) * (ef v d).1 =
        8 * (v : Int) + (d : Int) + 8 := by
    exact_mod_cast hcoordN
  have hcoordI :
      (d : Int) =
        8 * (ef v d).1 - 8 * (v : Int) - 8 := by
    omega
  have hsumPair :
      (dm : Int) + 6 * (um : Int) + 2 * (v : Int) =
        8 * (ef v d).1 + 2 + 3 * (m : Int) := by
    omega
  have hsumPair' :
      (dm : Int) + 6 * (um : Int) + 2 * (v : Int) =
        8 * (pow2I m * (um : Int)) + 2 + 3 * (m : Int) := by
    rw [hpowI] at hsumPair
    exact hsumPair
  have hcoordI' :
      (d : Int) =
        8 * (pow2I m * (um : Int)) - 8 * (v : Int) - 8 := by
    rw [hpowI] at hcoordI
    exact hcoordI
  constructor
  · change (dm : Int) -
      (8 * (pow2I m * (um : Int)) - 8 * (um : Int)) =
        2 * ((um : Int) - (v : Int)) + 2 + 3 * (m : Int)
    omega
  · change (d : Int) -
      (8 * (pow2I m * (v : Int)) - 8 * (v : Int)) =
        8 * (pow2I m * (um : Int)) -
          8 * (pow2I m * (v : Int)) - 8
    rw [hcoordI']
    omega

/--
The exact endpoint defect identities for SF followed by an F-run.
The pair type changes the affine constants but not the defect slope.
-/
theorem sf_macro_defect_components {m v d um dm : Nat}
    (h8 : d % 8 = 4)
    (hrun : FRun m (sf v d).1 (sf v d).2 um dm) :
    (defect m (dm : Int) (um : Int) =
        2 * ((um : Int) - (v : Int)) - 6 + 3 * (m : Int)) ∧
    (defect m (d : Int) (v : Int) =
        8 * (pow2I m * (um : Int)) -
          8 * (pow2I m * (v : Int)) - 20) := by
  have hsumN := fRun_rank hrun
  have hpowN := fRun_power hrun
  have hrelN := sf_output_relation (v := v) h8
  have hcoordN : 8 * (sf v d).1 = 8 * v + d + 20 := by
    simp [sf]
    omega
  have hsumI :
      (dm : Int) + 6 * (um : Int) =
        (sf v d).2 + 6 * (sf v d).1 + 3 * (m : Int) := by
    exact_mod_cast hsumN
  have hpowI :
      (sf v d).1 = pow2I m * (um : Int) := by
    change (sf v d).1 = (2 : Int) ^ m * (um : Int)
    exact_mod_cast hpowN
  have hrelI :
      (sf v d).2 + 2 * (v : Int) + 6 =
        2 * (sf v d).1 := by
    exact_mod_cast hrelN
  have hcoordI' :
      (8 : Int) * (sf v d).1 =
        8 * (v : Int) + (d : Int) + 20 := by
    exact_mod_cast hcoordN
  have hcoordI :
      (d : Int) =
        8 * (sf v d).1 - 8 * (v : Int) - 20 := by
    omega
  have hsumPair :
      (dm : Int) + 6 * (um : Int) + 2 * (v : Int) + 6 =
        8 * (sf v d).1 + 3 * (m : Int) := by
    omega
  have hsumPair' :
      (dm : Int) + 6 * (um : Int) + 2 * (v : Int) + 6 =
        8 * (pow2I m * (um : Int)) + 3 * (m : Int) := by
    rw [hpowI] at hsumPair
    exact hsumPair
  have hcoordI' :
      (d : Int) =
        8 * (pow2I m * (um : Int)) - 8 * (v : Int) - 20 := by
    rw [hpowI] at hcoordI
    exact hcoordI
  constructor
  · change (dm : Int) -
      (8 * (pow2I m * (um : Int)) - 8 * (um : Int)) =
        2 * ((um : Int) - (v : Int)) - 6 + 3 * (m : Int)
    omega
  · change (d : Int) -
      (8 * (pow2I m * (v : Int)) - 8 * (v : Int)) =
        8 * (pow2I m * (um : Int)) -
          8 * (pow2I m * (v : Int)) - 20
    rw [hcoordI']
    omega

#print axioms branch13_two_F_run
#print axioms branch13_first_SF
#print axioms branch15_first_E
#print axioms branch15_optional_SF

end BB429SignedBranch13_15
