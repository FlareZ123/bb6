import Agent49ParitySource

namespace BB6.Agent41DrainValuationNormalForm

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource

/--
An exact closed form for one successful evalA call.

The decomposition
  k = ternaryOnes v + 3^v * (3*q + 2*eps)
says that the low-order base-three digits of k consist of v copies of 1,
followed by 0 (eps = 0) or 2 (eps = 1). The source evaluator consumes
exactly this run. The budget v+1-eps is exact for this single call.
-/
theorem evalA_3adic_run
    (a k m v q eps : Nat)
    (heps : eps ≤ 1)
    (hk : k = ternaryOnes v + 3^v * (3*q + 2*eps))
    (ha : v+1-eps ≤ a) :
    evalA a k m =
      some (a+2*eps-(v+1), q,
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
        rw [Nat.sub_add_cancel (by omega : 1 ≤ a)]
  | succ v ih =>
      have hpow : 3^(v+1) = 3*3^v := by
        rw [Nat.pow_succ]
        omega
      have hones : ternaryOnes (v+1) = 3*ternaryOnes v+1 := rfl
      rw [hpow, hones] at hk
      have hkRec :
          k = 1 + 3*(ternaryOnes v + 3^v*(3*q+2*eps)) := by
        calc
          k = 3*ternaryOnes v+1 + (3*3^v)*(3*q+2*eps) := hk
          _ = 3*ternaryOnes v+1 + 3*(3^v*(3*q+2*eps)) := by rw [Nat.mul_assoc]
          _ = 1 + 3*(ternaryOnes v + 3^v*(3*q+2*eps)) := by rw [Nat.mul_add]; omega
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
      have habudget : v+1-eps ≤ a-1 := by omega
      rw [evalA]
      simp only [if_neg hkmod2, if_neg ha0, if_neg hkmod0]
      rw [hkdiv]
      let k0 := ternaryOnes v + 3^v*(3*q+2*eps)
      have hIH :=
        ih (a-1) k0 (m + 2*k0 + 3) (by trivial) habudget
      rw [hIH]
      simp only [Option.some.injEq, Prod.mk.injEq]
      constructor
      · omega
      · constructor
        · trivial
        · have hpow2 : 2*ternaryOnes v+1 = 3^v :=
            twice_ones_add_one_eq_pow v
          have hshift :
              2*(ternaryOnes v + 3^v*(3*q+2*eps))+3 =
                (6*q+1+4*eps)*3^v+2 := by
            have hcoeff : 1+2*(3*q+2*eps)=6*q+1+4*eps := by omega
            have hmul : 3^v + 2*(3^v*(3*q+2*eps)) = (6*q+1+4*eps)*3^v := by
              have hcomm : 3^v*(3*q+2*eps) = (3*q+2*eps)*3^v := Nat.mul_comm _ _
              calc
                3^v + 2*(3^v*(3*q+2*eps)) = 3^v + 2*((3*q+2*eps)*3^v) := by rw [hcomm]
                _ = 1*3^v + (2*(3*q+2*eps))*3^v := by simp [Nat.mul_assoc]
                _ = (1+2*(3*q+2*eps))*3^v := by rw [Nat.add_mul]
                _ = (6*q+1+4*eps)*3^v := by rw [hcoeff]
            calc
              2*(ternaryOnes v + 3^v*(3*q+2*eps))+3
                  = (2*ternaryOnes v+1) + 2*(3^v*(3*q+2*eps)) + 2 := by
                      rw [Nat.mul_add]
                      omega
              _ = 3^v + 2*(3^v*(3*q+2*eps)) + 2 := by rw [hpow2]
              _ = (6*q+1+4*eps)*3^v+2 := by rw [hmul]
          have hplus : 3^v + ternaryOnes v = ternaryOnes (v+1) := by
            rw [← hpow2, hones]
            omega
          calc
            m + 2*k0 + 3 + (6*q+1+4*eps)*ternaryOnes v + 2*v + 2*(1-eps)
                = m + (2*k0+3) + (6*q+1+4*eps)*ternaryOnes v + 2*v + 2*(1-eps) := by omega
            _ = m + ((6*q+1+4*eps)*3^v+2) + (6*q+1+4*eps)*ternaryOnes v + 2*v + 2*(1-eps) := by rw [hshift]
            _ = m + (6*q+1+4*eps)*(3^v+ternaryOnes v) + 2*(v+1) + 2*(1-eps) := by
                  rw [Nat.mul_add]
                  omega
            _ = m + (6*q+1+4*eps)*ternaryOnes (v+1) + 2*(v+1) + 2*(1-eps) := by rw [hplus]

end BB6.Agent41DrainValuationNormalForm
