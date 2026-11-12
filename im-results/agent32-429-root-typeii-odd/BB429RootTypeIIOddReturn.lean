import BB429RootOddSection
import Frontier429
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429RootTypeIIOddReturn

open Frontier429 BB429RootPairNormalizer

private theorem e0_even_left_to_A3 (r : List Bool) :
    run 7 ⟨4, ones2 3 ++ [false], false, r⟩ =
      some ⟨0, [], false, pairs 3 ++ false :: r⟩ := by
  have h1 : run 1 ⟨4, ones2 3 ++ [false], false, r⟩ =
      some (ae 3 [] (false :: r)) := by rfl
  rw [show 7 = 1 + 6 by omega, run_add, h1]
  simp only [Option.bind_some]
  simpa only [ae] using ae_sweep 3 [] (false :: r)

private theorem a0_outword8 (l r : List Bool) :
    run 8 ⟨0, l, false, [false, true, true, true, false] ++ r⟩ =
      some ⟨0, ones2 2 ++ l, false, false :: r⟩ := by
  rfl

private theorem a0_fixed8 (l r : List Bool) :
    run 8 ⟨0, l, false, [false, true, true, true, true, false] ++ r⟩ =
      some ⟨0, ones2 2 ++ l, false, [true, false] ++ r⟩ := by
  rfl

private theorem a0_outWords_sweep (n : Nat) (l r : List Bool) :
    run (8 * n) ⟨0, l, false, false :: (outWords n ++ r)⟩ =
      some ⟨0, ones2 (2 * n) ++ l, false, false :: r⟩ := by
  induction n generalizing l r with
  | zero =>
      simp [outWords, run]
  | succ n ih =>
      rw [show 8 * (n + 1) = 8 + 8 * n by omega, run_add]
      change
        (run 8 ⟨0, l, false,
          [false, true, true, true, false] ++ (outWords n ++ r)⟩).bind
            (run (8 * n)) =
          some ⟨0, ones2 (2 * (n + 1)) ++ l, false, false :: r⟩
      rw [a0_outword8]
      simp only [Option.bind_some]
      simpa [Nat.mul_succ, ones2_add, List.append_assoc] using
        (ih (l := ones2 2 ++ l) (r := r))

private theorem a0_outWords_to_C0 (n k : Nat) :
    run (8 * n + 8 + 2 * (k + 1) + 4)
      ⟨0, ones2 3, false,
        false :: (outWords n ++
          ([true, true, true, true, false] ++ pairs k ++ [false, true]))⟩ =
      some ⟨2, [true, false] ++ ones2 (k + 2 * n + 7), false, []⟩ := by
  let r : List Bool :=
    [true, true, true, true, false] ++ pairs k ++ [false, true]
  let z0 : Z := ⟨0, ones2 3, false, false :: (outWords n ++ r)⟩
  let z1 : Z := ⟨0, ones2 (2 * n) ++ ones2 3, false, false :: r⟩
  let z2 : Z :=
    ⟨0, ones2 2 ++ ones2 (2 * n) ++ ones2 3, false,
      [true, false] ++ pairs k ++ [false, true]⟩
  let z3 : Z :=
    ⟨0, ones2 (k + 1) ++ ones2 2 ++ ones2 (2 * n) ++ ones2 3,
      false, [false, true]⟩
  have h1 : run (8 * n) z0 = some z1 := by
    simpa [z0, z1, r] using a0_outWords_sweep n (ones2 3) r
  have h2 : run 8 z1 = some z2 := by
    simpa [z1, z2, r, List.append_assoc] using
      a0_fixed8 (ones2 (2 * n) ++ ones2 3) (pairs k ++ [false, true])
  have h3 : run (2 * (k + 1)) z2 = some z3 := by
    change
      run (2 * (k + 1))
        ⟨0, ones2 2 ++ ones2 (2 * n) ++ ones2 3, false,
          pairs (k + 1) ++ [false, true]⟩ = some z3
    simpa [z3] using
      ab_sweep (k + 1) (ones2 2 ++ ones2 (2 * n) ++ ones2 3)
        [false, true]
  have hleft :
      ones2 (k + 1) ++ ones2 2 ++ ones2 (2 * n) ++ ones2 3 =
        ones2 (k + 2 * n + 6) := by
    rw [← ones2_add (k + 1) 2]
    rw [← ones2_add (k + 3) (2 * n)]
    rw [← ones2_add (k + 3 + 2 * n) 3]
    congr 1
    omega
  have hfinal :
      [true, false, true, true] ++ ones2 (k + 2 * n + 6) =
        [true, false] ++ ones2 (k + 2 * n + 7) := by
    calc
      [true, false, true, true] ++ ones2 (k + 2 * n + 6) =
          [true, false] ++ (ones2 1 ++ ones2 (k + 2 * n + 6)) := by rfl
      _ = [true, false] ++ ones2 (1 + (k + 2 * n + 6)) := by
        rw [ones2_add]
      _ = [true, false] ++ ones2 (k + 2 * n + 7) := by
        congr 1
        omega
  have h4 : run 4 z3 =
      some ⟨2, [true, false] ++ ones2 (k + 2 * n + 7), false, []⟩ := by
    have hleft' : z3 =
        ⟨0, ones2 (k + 2 * n + 6), false, [false, true]⟩ := by
      simp [z3, hleft]
    rw [hleft']
    simpa [hfinal] using finish4 (ones2 (k + 2 * n + 6))
  calc
    run (8 * n + 8 + 2 * (k + 1) + 4) z0 =
        run (8 * n + (8 + (2 * (k + 1) + 4))) z0 := by
          congr 1
          omega
    _ = (run (8 * n) z0).bind (run (8 + (2 * (k + 1) + 4))) :=
      run_add _ _ _
    _ = run (8 + (2 * (k + 1) + 4)) z1 := by rw [h1]; rfl
    _ = (run 8 z1).bind (run (2 * (k + 1) + 4)) := run_add _ _ _
    _ = run (2 * (k + 1) + 4) z2 := by rw [h2]; rfl
    _ = (run (2 * (k + 1)) z2).bind (run 4) := run_add _ _ _
    _ = run 4 z3 := by rw [h3]; rfl
    _ = some ⟨2, [true, false] ++ ones2 (k + 2 * n + 7), false, []⟩ := h4

theorem c0_typeII_odd_endpoint (k n : Nat) :
    run (4 * k + 14 * n + 37)
      ⟨2,
        true :: ones2 (k + 1) ++
          (false :: true :: false :: inWords n ++ (ones2 3 ++ [false])),
        false, []⟩ =
      some ⟨2, [true, false] ++ ones2 (k + 2 * n + 7), false, []⟩ := by
  let r : List Bool :=
    outWords n ++
      ([true, true, true, true, false] ++ pairs k ++ [false, true])
  let z0 : Z :=
    ⟨2,
      true :: ones2 (k + 1) ++
        (false :: true :: false :: inWords n ++ (ones2 3 ++ [false])),
      false, []⟩
  let z1 : Z := ⟨4, ones2 3 ++ [false], false, r⟩
  let z2 : Z := ⟨0, [], false, pairs 3 ++ false :: r⟩
  let z3 : Z := ⟨0, ones2 3, false, false :: r⟩
  let z4 : Z := ⟨2, [true, false] ++ ones2 (k + 2 * n + 7), false, []⟩
  have h0 : run (2 * k + 10 + 6 * n) z0 = some z1 := by
    simpa [z0, z1, r, List.append_assoc] using
      c0_odd_pairs_to_e0 k n (ones2 3 ++ [false])
  have h1 : run 7 z1 = some z2 := by
    simpa [z1, z2, r] using e0_even_left_to_A3 r
  have h2 : run 6 z2 = some z3 := by
    simpa [z2, z3, r, List.append_assoc] using
      ab_sweep 3 [] (false :: r)
  have h3 : run (8 * n + 8 + 2 * (k + 1) + 4) z3 = some z4 := by
    simpa [z3, z4, r, List.append_assoc] using a0_outWords_to_C0 n k
  calc
    run (4 * k + 14 * n + 37) z0 =
        run ((2 * k + 10 + 6 * n) +
          (7 + (6 + (8 * n + 8 + 2 * (k + 1) + 4)))) z0 := by
            congr 1
            omega
    _ = (run (2 * k + 10 + 6 * n) z0).bind
          (run (7 + (6 + (8 * n + 8 + 2 * (k + 1) + 4)))) :=
      run_add _ _ _
    _ = run (7 + (6 + (8 * n + 8 + 2 * (k + 1) + 4))) z1 := by
      rw [h0]
      rfl
    _ = (run 7 z1).bind (run (6 + (8 * n + 8 + 2 * (k + 1) + 4))) :=
      run_add _ _ _
    _ = run (6 + (8 * n + 8 + 2 * (k + 1) + 4)) z2 := by
      rw [h1]
      rfl
    _ = (run 6 z2).bind (run (8 * n + 8 + 2 * (k + 1) + 4)) :=
      run_add _ _ _
    _ = run (8 * n + 8 + 2 * (k + 1) + 4) z3 := by
      rw [h2]
      rfl
    _ = some z4 := h3

#print axioms c0_typeII_odd_endpoint

end BB429RootTypeIIOddReturn
