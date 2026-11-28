import Raw56LE17557Base

namespace BB6.Agent1Raw56.LE17557LocalSweeps
open BB6Coverage
open BB6Coverage.Agent31Pump
open BB6.Agent1Raw56.LE17557Base

theorem B1_one (L R : List Bool) :
    run0 p 1 ⟨1, true :: L, true :: R⟩ =
      some ⟨1, true :: true :: L, R⟩ := by
  simp [run0, step0, p, move0]

theorem C1_one (L R : List Bool) :
    run0 p 1 ⟨2, true :: L, true :: R⟩ =
      some ⟨2, true :: false :: L, R⟩ := by
  simp [run0, step0, p, move0]

theorem A1_left_one (L R : List Bool) :
    run0 p 1 ⟨0, true :: true :: L, R⟩ =
      some ⟨0, true :: L, true :: R⟩ := by
  simp [run0, step0, p, move0]

theorem D0_left_zero (L R : List Bool) :
    run0 p 1 ⟨3, false :: false :: L, R⟩ =
      some ⟨3, false :: L, true :: R⟩ := by
  simp [run0, step0, p, move0]

theorem E1_left_one (L R : List Bool) :
    run0 p 1 ⟨4, true :: true :: L, R⟩ =
      some ⟨4, true :: L, false :: R⟩ := by
  simp [run0, step0, p, move0]

/-- B sweeps right across an arbitrary run of ones, preserving them. -/
theorem B_sweep_ones (n : Nat) (L R : List Bool) :
    run0 p n ⟨1, true :: L, rep [true] n ++ R⟩ =
      some ⟨1, true :: rep [true] n ++ L, R⟩ := by
  have one : ∀ L R,
      run0 p 1 ⟨1, [true] ++ L, [true] ++ R⟩ =
        some ⟨1, [true] ++ [true] ++ L, R⟩ := by
    intro L R
    simpa using B1_one L R
  simpa [List.append_assoc] using
    sweepR p 1 [true] [] [true] [true] 1 one n L R

/-- C sweeps right across ones while erasing each crossed cell. -/
theorem C_sweep_ones (n : Nat) (L R : List Bool) :
    run0 p n ⟨2, true :: L, rep [true] n ++ R⟩ =
      some ⟨2, true :: rep [false] n ++ L, R⟩ := by
  have one : ∀ L R,
      run0 p 1 ⟨2, [true] ++ L, [true] ++ R⟩ =
        some ⟨2, [true] ++ [false] ++ L, R⟩ := by
    intro L R
    simpa using C1_one L R
  simpa [List.append_assoc] using
    sweepR p 2 [true] [] [true] [false] 1 one n L R

/-- A sweeps left across ones without changing them. -/
theorem A_sweep_left_ones (n : Nat) (L R : List Bool) :
    run0 p n ⟨0, true :: rep [true] n ++ L, R⟩ =
      some ⟨0, true :: L, rep [true] n ++ R⟩ := by
  have one : ∀ L R,
      run0 p 1 ⟨0, [true] ++ [true] ++ L, R⟩ =
        some ⟨0, [true] ++ L, [true] ++ R⟩ := by
    intro L R
    simpa using A1_left_one L R
  simpa [List.append_assoc] using
    sweepL p 0 [true] [] [true] [true] 1 one n L R

/-- D sweeps left across zeros, writing ones behind it. -/
theorem D_sweep_left_zeros (n : Nat) (L R : List Bool) :
    run0 p n ⟨3, false :: rep [false] n ++ L, R⟩ =
      some ⟨3, false :: L, rep [true] n ++ R⟩ := by
  have one : ∀ L R,
      run0 p 1 ⟨3, [false] ++ [false] ++ L, R⟩ =
        some ⟨3, [false] ++ L, [true] ++ R⟩ := by
    intro L R
    simpa using D0_left_zero L R
  simpa [List.append_assoc] using
    sweepL p 3 [false] [] [false] [true] 1 one n L R

/-- E sweeps left across ones, writing zeros behind it. -/
theorem E_sweep_left_ones (n : Nat) (L R : List Bool) :
    run0 p n ⟨4, true :: rep [true] n ++ L, R⟩ =
      some ⟨4, true :: L, rep [false] n ++ R⟩ := by
  have one : ∀ L R,
      run0 p 1 ⟨4, [true] ++ [true] ++ L, R⟩ =
        some ⟨4, [true] ++ L, [false] ++ R⟩ := by
    intro L R
    simpa using E1_left_one L R
  simpa [List.append_assoc] using
    sweepL p 4 [true] [] [true] [false] 1 one n L R

#print axioms B_sweep_ones
#print axioms C_sweep_ones
#print axioms A_sweep_left_ones
#print axioms D_sweep_left_zeros
#print axioms E_sweep_left_ones

end BB6.Agent1Raw56.LE17557LocalSweeps
