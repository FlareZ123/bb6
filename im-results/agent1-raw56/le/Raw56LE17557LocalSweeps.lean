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

theorem B_turn_to_C (L R : List Bool) :
    run0 p 2 ⟨1, true :: L, false :: true :: R⟩ =
      some ⟨2, true :: true :: true :: L, R⟩ := by
  rfl

/-- Fixed tail of an I-return: finish the erased B block, observe a 1 in D,
    and return through E0/F0 to A on the preceding erased zero. -/
theorem C_I_turn_to_A (L R : List Bool) :
    run0 p 5 ⟨2, true :: L, false :: true :: R⟩ =
      some ⟨0, L, false :: true :: true :: R⟩ := by
  rfl

/-- Exact first I-return used inside every A triad.  Parameters are shifted so
    the scanned right runs have lengths a+1, b+5, c+1 and z+2. -/
theorem I_return (a b c z : Nat) (L R : List Bool) :
    run0 p (a+b+12)
      ⟨0, false :: L,
        rep [true] (a+1) ++ [false] ++
        rep [true] (b+5) ++ [false] ++
        rep [true] (c+1) ++ rep [false] (z+2) ++ R⟩ =
      some
      ⟨0,
        rep [false] (b+4) ++ rep [true] (a+3) ++ L,
        [false] ++ rep [true] (c+2) ++ rep [false] (z+2) ++ R⟩ := by
  let tail : List Bool :=
    [false] ++ rep [true] (b+5) ++ [false] ++
      rep [true] (c+1) ++ rep [false] (z+2) ++ R
  let afterB : List Bool :=
    [false] ++ rep [true] (c+1) ++ rep [false] (z+2) ++ R
  have h1 :
      run0 p 1
        ⟨0, false :: L, rep [true] (a+1) ++ tail⟩ =
      some ⟨1, true :: true :: L, rep [true] a ++ tail⟩ := by
    simp [tail, rep, run0, step0, p, move0, List.append_assoc]
  have h2 := B_sweep_ones a (true :: L) tail
  have h3 :
      run0 p 2
        ⟨1, true :: rep [true] a ++ true :: L,
          [false] ++ rep [true] (b+5) ++ afterB⟩ =
      some
        ⟨2, true :: true :: true :: rep [true] a ++ true :: L,
          rep [true] (b+4) ++ afterB⟩ := by
    have ht := B_turn_to_C (rep [true] a ++ true :: L)
      (rep [true] (b+4) ++ afterB)
    simpa [rep, List.append_assoc] using ht
  have h4 := C_sweep_ones (b+4)
    (true :: true :: rep [true] a ++ true :: L) afterB
  have h5 :
      run0 p 5
        ⟨2,
          true :: rep [false] (b+4) ++
            true :: true :: rep [true] a ++ true :: L,
          [false] ++ rep [true] (c+1) ++ rep [false] (z+2) ++ R⟩ =
      some
        ⟨0,
          rep [false] (b+4) ++ rep [true] (a+3) ++ L,
          [false] ++ rep [true] (c+2) ++ rep [false] (z+2) ++ R⟩ := by
    have ht := C_I_turn_to_A
      (rep [false] (b+4) ++ true :: true :: rep [true] a ++ true :: L)
      (rep [true] c ++ rep [false] (z+2) ++ R)
    simpa [rep, List.append_assoc] using ht
  have h12 := join0 h1 h2
  have h123 := join0 h12 h3
  have h1234 := join0 h123 h4
  have h := join0 h1234 h5
  simpa [tail, afterB, rep, List.append_assoc] using h

#print axioms B_turn_to_C
#print axioms C_I_turn_to_A
#print axioms I_return
#print axioms B_sweep_ones
#print axioms C_sweep_ones
#print axioms A_sweep_left_ones
#print axioms D_sweep_left_zeros
#print axioms E_sweep_left_ones

end BB6.Agent1Raw56.LE17557LocalSweeps
