import W4CZeroSafe
import BB429JuncHeadExcursion
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429PositiveSafe

open BB429OddExcursion BB429SourceE1Return
open BB429FinishScanEDelta BB429JuncHeadExcursion BB429W4CZeroSafe

private theorem ones_add (m n : Nat) : ones (m+n) = ones m ++ ones n := by
  induction m with
  | zero => simp [ones]
  | succ m ih => simp [ones, Nat.succ_add, List.replicate_succ]

private theorem pairs01_succ_append (n : Nat) :
    pairs01 n ++ [false,true] = pairs01 (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change false :: true :: (pairs01 n ++ [false,true]) =
        false :: true :: pairs01 (n+1)
      rw [ih]

private theorem ones_three_left (n : Nat) (rest : List Bool) :
    ones n ++ (true :: true :: true :: rest) =
      true :: (ones (n+2) ++ rest) := by
  have hp : ones n ++ [true,true,true] = true :: ones (n+2) := by
    calc
      ones n ++ [true,true,true] = ones (n+3) := by
        rw [ones_add]
        rfl
      _ = ones (1+(n+2)) := by congr 1 <;> omega
      _ = true :: ones (n+2) := by rw [ones_add]; rfl
  calc
    ones n ++ (true::true::true::rest) =
        (ones n ++ [true,true,true]) ++ rest := by
      rw [List.append_assoc]
      rfl
    _ = (true::ones (n+2)) ++ rest := by rw [hp]
    _ = true :: (ones (n+2) ++ rest) := rfl

/-- Each A/0 to B/1 positive shift pair executes no C/0 instruction. -/
theorem a01_pair_safe (left suffix : List Bool) :
    runSafe 2 (z 0 left false (true :: suffix)) =
      some (z 0 (true :: true :: left) (suffix.headD false) suffix.tail) := by
  cases suffix <;> rfl

/-- Arbitrary-length rightward positive-u shift avoids C/0. -/
theorem a01_shift_safe (v : Nat) (left suffix : List Bool) :
    runSafe (2*(v+1))
      (z 0 left false (true :: (pairs01 v ++ (true :: suffix)))) =
      some (z 0 (ones (2*(v+1)) ++ left) true suffix) := by
  induction v generalizing left suffix with
  | zero =>
      simpa [pairs01, ones] using (a01_pair_safe left (true :: suffix))
  | succ v ih =>
      have hpair :
          runSafe 2
            (z 0 left false (true :: (pairs01 (v+1) ++ (true :: suffix)))) =
            some (z 0 (true :: true :: left) false
              (true :: (pairs01 v ++ (true :: suffix)))) := by
        simpa [pairs01, List.append_assoc] using
          (a01_pair_safe left (false :: true :: (pairs01 v ++ (true :: suffix))))
      rw [show 2*(v+2) = 2 + 2*(v+1) by omega, runSafe_add, hpair]
      simp only [Option.bind_some]
      rw [ih (true :: true :: left) suffix]
      have hout : ones (2*(v+2)) ++ left =
          ones (2*(v+1)) ++ (true :: true :: left) := by
        rw [show 2*(v+2)=2*(v+1)+2 by omega, ones_add]
        simp [ones, List.append_assoc]
      rw [← hout, show 2+2*(v+1)=2*(v+2) by omega]

/-- One A/1 to F/1 left sweep pair avoids C/0. -/
theorem a11_pair_safe (left suffix : List Bool) :
    runSafe 2 (z 0 (true :: true :: true :: left) true (true :: suffix)) =
      some (z 0 (true :: left) true (true :: false :: true :: suffix)) := by rfl

/-- Arbitrarily many A/1 to F/1 left sweep pairs avoid C/0. -/
theorem a11_shift_safe (p : Nat) (left suffix : List Bool) :
    runSafe (2*p) (z 0 (true :: (ones (2*p) ++ left)) true (true :: suffix)) =
      some (z 0 (true :: left) true (true :: (pairs01 p ++ suffix))) := by
  induction p generalizing left suffix with
  | zero => rfl
  | succ p ih =>
      have hrep : ones (2*(p+1)) = [true,true] ++ ones (2*p) := by
        rw [show 2*(p+1)=2+2*p by omega, ones_add]
        rfl
      have hfirst :
          runSafe 2 (z 0 (true :: true :: true :: (ones (2*p) ++ left))
            true (true :: suffix)) =
            some (z 0 (true :: (ones (2*p) ++ left)) true
              (true :: false :: true :: suffix)) :=
        a11_pair_safe (ones (2*p) ++ left) suffix
      rw [show 2*(p+1)=2+2*p by omega]
      have hrep2 : ones (2+2*p) = true :: true :: ones (2*p) := by
        rw [show 2+2*p=2*(p+1) by omega, hrep]
        rfl
      rw [hrep2]
      simp only [List.cons_append]
      rw [runSafe_add, hfirst]
      simp only [Option.bind_some]
      rw [ih left (false :: true :: suffix)]
      have hr : pairs01 p ++ (false :: true :: suffix) =
          pairs01 (p+1) ++ suffix := by
        calc
          pairs01 p ++ (false :: true :: suffix) =
            (pairs01 p ++ [false,true]) ++ suffix := by
              simp [List.append_assoc]
          _ = pairs01 (p+1) ++ suffix := by rw [pairs01_succ_append]
      rw [hr]

/-- For any positive left parameter and w >= 2 the full positive-u Junc
    return has no C/0 instruction at any intermediate primitive step. -/
theorem junc_positive_safe (u v w : Nat) (hw : 2 ≤ w) :
    runSafe (4*v+10) (junc (u+1) v w) =
      some (junc u (v+2) (w-2)) := by
  have hprep : runSafe 4 (junc (u+1) v w) =
      some (z 0 (true :: true :: true :: (pairs01 u ++ ones 5)) false
        (true :: (pairs01 v ++ ones w ++ [false,true]))) := by
    rfl
  have hones : ones (w-1) = true :: ones (w-2) := by
    have h : w-1 = (w-2)+1 := by omega
    rw [h]
    rfl
  have hfirst : runSafe (2*(v+1))
      (z 0 (true :: true :: true :: (pairs01 u ++ ones 5)) false
        (true :: (pairs01 v ++ ones w ++ [false,true]))) =
      some (midApos u v w) := by
    have hs := a01_shift_safe v (true :: true :: true :: (pairs01 u ++ ones 5))
      (ones (w-1) ++ [false,true])
    have hones1 : ones w = true :: ones (w-1) := by
      cases w with
      | zero => omega
      | succ w => rfl
    have hinput : z 0 (true :: true :: true :: (pairs01 u ++ ones 5)) false
        (true :: (pairs01 v ++ ones w ++ [false,true])) =
        z 0 (true :: true :: true :: (pairs01 u ++ ones 5)) false
        (true :: (pairs01 v ++ (true :: (ones (w-1) ++ [false,true])))) := by
      simp [hones1, List.append_assoc]
    rw [← hinput] at hs
    rw [hs]
    change some (z 0 (ones (2*(v+1)) ++
      (true :: true :: true :: (pairs01 u ++ ones 5)))
      true (ones (w-1) ++ [false,true])) = some (midApos u v w)
    have hleft := ones_three_left (2*(v+1)) (pairs01 u ++ ones 5)
    rw [hleft, show 2*(v+1)+2=2*(v+2) by omega]
    simp [midApos, List.append_assoc]
  have hsecond : runSafe (2*(v+2)) (midApos u v w) =
      some (junc u (v+2) (w-2)) := by
    have hs := a11_shift_safe (v+2) (pairs01 u ++ ones 5)
      (ones (w-2) ++ [false,true])
    have hin : midApos u v w =
      z 0 (true :: (ones (2*(v+2)) ++ (pairs01 u ++ ones 5))) true
        (true :: (ones (w-2) ++ [false,true])) := by
      simp [midApos, hones]
    rw [hin, hs]
    simp [junc, pairs01, List.append_assoc]
  have htime : 4*v+10 = 4 + (2*(v+1)+2*(v+2)) := by omega
  rw [htime, runSafe_add, hprep]
  simp only [Option.bind_some]
  rw [runSafe_add, hfirst]
  simp only [Option.bind_some]
  exact hsecond

/-- Every finite block of successive positive-u Junc returns has no C/0
    instruction at any processed primitive step. -/
theorem junc_positive_iter_safe (N U v w : Nat)
    (hU : N ≤ U) (hw : 2*N ≤ w) :
    runSafe (juncPosFullTime N v) (junc U v w) =
      some (junc (U-N) (v+2*N) (w-2*N)) := by
  induction N generalizing U v w with
  | zero => rfl
  | succ N ih =>
      have hstep0 := junc_positive_safe (U-1) v w (by omega)
      have hstep : runSafe (4*v+10) (junc U v w) =
          some (junc (U-1) (v+2) (w-2)) := by
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ U)] using hstep0
      rw [show juncPosFullTime (N+1) v =
        (4*v+10) + juncPosFullTime N (v+2) by rfl, runSafe_add, hstep]
      simp only [Option.bind_some]
      have htail := ih (U-1) (v+2) (w-2) (by omega) (by omega)
      rw [htail]
      have hu : U-1-N = U-(N+1) := by omega
      have hv : v+2+2*N = v+2*(N+1) := by omega
      have hw' : w-2-2*N = w-2*(N+1) := by omega
      rw [hu,hv,hw']

/-- Explicit original-zipper all-prefix exclusion of C/0 along the
    complete multi-return segment, including the empty return count. -/
theorem junc_positive_iter_no_czero (N U v w t : Nat)
    (hU : N ≤ U) (hw : 2*N ≤ w)
    (ht : t < juncPosFullTime N v) :
    ∃ p, run t (junc U v w) = some p ∧
      (p.state == 2 && !p.current) = false := by
  exact runSafe_no_czero_prefix (juncPosFullTime N v) t
    (junc U v w) (junc (U-N) (v+2*N) (w-2*N))
    (junc_positive_iter_safe N U v w hU hw) ht

#print axioms junc_positive_safe
#print axioms junc_positive_iter_safe
#print axioms junc_positive_iter_no_czero

end BB429PositiveSafe
