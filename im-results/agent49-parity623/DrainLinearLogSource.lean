import Agent8DrainQuadraticLogSource

/-!
DRAFT: candidate sharp linear-in-ternary-length excess bound for the
original Cryptids #623 B-drain. The proof is source-shaped and imports the
unmodified source through Agent8DrainQuadraticLogSource. It has not yet
been compiled in CI; treat as an intermediate proof draft until then.

Proposed theorem:
  b < 3^n -> drainB a b d = some (.D aa dd)
    -> dd <= d + 3*b + 4*n + 2

The coefficient 4 and constant 2 are sharp. For n>=1, let
b_1=2 and b_(n+1)=3*b_n+1. Then
drainB (n+1) b_n d = some (.D 0 (d+3*b_n+4*n+2)).
-/

namespace BB6.Agent49DrainLinearLogSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8DrainQuadraticLogSource

/-- If a successful evaluator returns a positive residual block count,
record the exact number r of ternary digits consumed by this evaluator.
The remaining output index is below 3^s, where r+s=n. -/
theorem evalA_positive_depth (n : Nat) :
    ∀ a k m aa bb dd : Nat,
      k < 3^n → 0 < bb →
      evalA a k m = some (aa,bb,dd) →
      ∃ r s : Nat,
        r+s=n ∧ 0<r ∧ bb<3^s ∧ dd+3*bb≤m+k+2*r := by
  induction n with
  | zero =>
      intro a k m aa bb dd hk hbb hs
      have hk0 : k=0 := by simpa using hk
      subst k
      rw [evalA] at hs
      by_cases ha : a=0
      · simp [ha] at hs
      · simp [ha] at hs
        cases hs
        omega
  | succ n ih =>
      intro a k m aa bb dd hk hbb hs
      rw [evalA] at hs
      by_cases h2 : k%3=2
      · simp [h2] at hs
        cases hs
        have hpow : 3^(n+1)=3*3^n := by rw [Nat.pow_succ]; omega
        have hq : k/3<3^n := by omega
        refine ⟨1,n,by omega,by omega,hq,by omega⟩
      · by_cases ha : a=0
        · by_cases h0 : k%3=0
          · simp [h2,ha,h0] at hs
          · simp [h2,ha,h0] at hs
            cases hs
            have hpow : 3^(n+1)=3*3^n := by rw [Nat.pow_succ]; omega
            have hq : k/3<3^n := by omega
            refine ⟨1,n,by omega,by omega,hq,by omega⟩
        · by_cases h0 : k%3=0
          · simp [h2,ha,h0] at hs
            cases hs
            have hpow : 3^(n+1)=3*3^n := by rw [Nat.pow_succ]; omega
            have hq : k/3<3^n := by omega
            refine ⟨1,n,by omega,by omega,hq,by omega⟩
          · simp [h2,ha,h0] at hs
            have hpow : 3^(n+1)=3*3^n := by rw [Nat.pow_succ]; omega
            have hq : k/3<3^n := by omega
            have hr := ih (a-1) (k/3) (m+2*(k/3)+3)
              aa bb dd hq hbb hs
            rcases hr with ⟨r,s,hrs,hrpos,hbs,hpot⟩
            refine ⟨r+1,s,by omega,by omega,hbs,?_⟩
            omega

/-- Sharp linear-logarithmic upper envelope for every successful complete
original-source B-drain. -/
theorem drainB_upper_linear_log (n : Nat) :
    ∀ a b d aa dd : Nat, b<3^n →
      drainB a b d = some (.D aa dd) →
      dd ≤ d+3*b+4*n+2 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro a b d aa dd hb hs
      by_cases hb0 : b=0
      · subst b
        simp [drainB] at hs
        cases hs
        omega
      · have hn : 0<n := by
          by_contra h
          have hn0 : n=0 := by omega
          subst n
          simp at hb
          omega
        rw [drainB] at hs
        simp only [if_neg hb0] at hs
        cases hev : evalA a (b-1) (d+2*b+3) with
        | none => simp [hev] at hs
        | some p =>
            rcases p with ⟨a1,b1,d1⟩
            simp only [hev,Option.bind_some] at hs
            by_cases hlt : b1<b
            · simp only [if_pos hlt] at hs
              by_cases hb1 : b1=0
              · subst b1
                simp [drainB] at hs
                cases hs
                have hlog := evalA_upper_log n a (b-1) (d+2*b+3)
                  a1 0 d1 (by omega) hev
                omega
              · have hdepth := evalA_positive_depth n a (b-1)
                  (d+2*b+3) a1 b1 d1 (by omega) (by omega) hev
                rcases hdepth with ⟨r,s,hrs,hrpos,hbs,hpot⟩
                have hsn : s<n := by omega
                have hrec := ih s hsn a1 b1 d1 aa dd hbs hs
                omega
            · simp [hlt] at hs

#print axioms evalA_positive_depth
#print axioms drainB_upper_linear_log
end BB6.Agent49DrainLinearLogSource
