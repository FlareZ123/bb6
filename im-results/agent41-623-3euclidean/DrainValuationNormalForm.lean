import Agent49ParitySource

namespace BB6.Agent41DrainValuationNormalForm

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource

/--
An exact closed form for one successful evalA call.

The decomposition
  k = ternaryOnes v + 3^v * (3*q + 2*eps)
says that the low-order base-three digits of k consist of v copies of 1,
followed by 0 (eps = 0) or 2 (eps = 1).  The source evaluator consumes
exactly this run.
-/
theorem evalA_3adic_run
    (a k m v q eps : Nat)
    (heps : eps ≤ 1)
    (hk : k = ternaryOnes v + 3^v * (3*q + 2*eps))
    (ha : v+1 ≤ a) :
    evalA a k m =
      some (a-v-1+2*eps, q,
        m + (6*q+1+4*eps)*ternaryOnes v + 2*v + 2*(1-eps)) := by
  induction v generalizing a k m with
  | zero =>
      have hk' : k = 3*q + 2*eps := by
        simpa [ternaryOnes] using hk
      by_cases heps0 : eps = 0
      · subst eps
        have hkmod : k % 3 = 0 := by omega
        have hkdiv : k / 3 = q := by omega
        have ha0 : a ≠ 0 := by omega
        simp [evalA, hkmod, hkdiv, ha0, ternaryOnes]
      · have heps1 : eps = 1 := by omega
        subst eps
        have hkmod : k % 3 = 2 := by omega
        have hkdiv : k / 3 = q := by omega
        simp [evalA, hkmod, hkdiv, ternaryOnes]
  | succ v ih =>
      have hpow : 3^(v+1) = 3*3^v := by
        rw [pow_succ]
        ring
      have hones : ternaryOnes (v+1) = 3*ternaryOnes v+1 := rfl
      rw [hpow, hones] at hk
      have hkRec :
          k = 1 + 3*(ternaryOnes v + 3^v*(3*q+2*eps)) := by
        calc
          k = 3*ternaryOnes v+1 + (3*3^v)*(3*q+2*eps) := hk
          _ = 1 + 3*(ternaryOnes v + 3^v*(3*q+2*eps)) := by ring
      have hkmod2 : k % 3 ≠ 2 := by
        rw [hkRec]
        omega
      have ha0 : a ≠ 0 := by omega
      have hkmod0 : k % 3 ≠ 0 := by
        rw [hkRec]
        omega
      have hkdiv :
          k / 3 = ternaryOnes v + 3^v*(3*q+2*eps) := by
        rw [hkRec]
        omega
      have habudget : v+1 ≤ a-1 := by omega
      rw [evalA]
      simp only [if_neg hkmod2, if_neg ha0, if_neg hkmod0]
      rw [hkdiv]
      have hIH :=
        ih (a-1)
          (ternaryOnes v + 3^v*(3*q+2*eps))
          (m + 2*(ternaryOnes v + 3^v*(3*q+2*eps)) + 3)
          rfl habudget
      rw [hIH]
      simp only [Option.some.injEq, Prod.mk.injEq]
      constructor
      · omega
      constructor
      · rfl
      · have hpow2 : 2*ternaryOnes v+1 = 3^v :=
          twice_ones_add_one_eq_pow v
        have hshift :
            2*(ternaryOnes v + 3^v*(3*q+2*eps))+3
              = (6*q+1+4*eps)*3^v+2 := by
          rw [← hpow2]
          ring
        have hplus : 3^v + ternaryOnes v = ternaryOnes (v+1) := by
          rw [← hpow2, hones]
          ring
        rw [hshift, hplus]
        ring

end BB6.Agent41DrainValuationNormalForm
