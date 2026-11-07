import Agent8DrainQuadraticLogSource

/-!
DRAFT: sharp linear-in-ternary-length bounds for the original Cryptids #623
B-drain. The proof text has been compiled locally with Lean 4.36.0-rc2 against an
exact copy of the upstream evalA/drainB equations. The pinned source workflow
still needs to compile this module through its actual imports; treat it as an
intermediate result until that source-level CI check passes.

For b < 3^n and a successful drain:
  output third counter <= d + 3*b + 4*n + 2
  output first counter + n + 1 >= a

Both bounds are sharp, and one family attains both simultaneously.
For n>=1, take a=n+1 and b_n=(5*3^(n-1)-1)/2. The drain recurrence
reduces (a,b_n) to (a-1,b_(n-1)) at each outer call, so the final first
counter is zero and the third-counter excess is exactly 4*n+2.
The separate family b=(3^n+1)/2, a=n+1 also attains the first-counter
loss n+1.
-/

namespace BB6.Agent49DrainLinearLogSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8DrainQuadraticLogSource

/-- Any successful evaluator loses at most n+1 from its first counter
when its block input is below 3^n. -/
theorem evalA_first_lower_log (n : Nat) :
    ∀ a k m aa bb dd : Nat,
      k < 3^n →
      evalA a k m = some (aa,bb,dd) →
      aa+n+1≥a := by
  induction n with
  | zero =>
      intro a k m aa bb dd hk hs
      have hk0 : k=0 := by simpa using hk
      subst k
      rw [evalA] at hs
      by_cases ha : a=0
      · simp [ha] at hs
      · simp [ha] at hs
        cases hs
        omega
  | succ n ih =>
      intro a k m aa bb dd hk hs
      rw [evalA] at hs
      by_cases h2 : k%3=2
      · simp [h2] at hs
        cases hs
        omega
      · by_cases ha : a=0
        · by_cases h0 : k%3=0
          · simp [h2,ha,h0] at hs
          · simp [h2,ha,h0] at hs
            cases hs
            omega
        · by_cases h0 : k%3=0
          · simp [h2,ha,h0] at hs
            cases hs
            omega
          · simp [h2,ha,h0] at hs
            have hpow : 3^(n+1)=3*3^n := by rw [Nat.pow_succ]; omega
            have hq : k/3<3^n := by omega
            have hr := ih (a-1) (k/3) (m+2*(k/3)+3) aa bb dd hq hs
            omega

/-- If a successful evaluator returns a positive residual block count,
record the exact number r of ternary digits consumed by this evaluator.
The remaining output index is below 3^s, where r+s=n. -/
theorem evalA_positive_depth (n : Nat) :
    ∀ a k m aa bb dd : Nat,
      k < 3^n → 0 < bb →
      evalA a k m = some (aa,bb,dd) →
      ∃ r s : Nat,
        r+s=n ∧ 0<r ∧ bb<3^s ∧ aa+r≥a ∧ dd+3*bb≤m+k+2*r := by
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
        rcases hs with ⟨rfl, rfl, rfl⟩
        have hpow : 3^(n+1)=3*3^n := by rw [Nat.pow_succ]; omega
        have hq : k/3<3^n := by omega
        refine ⟨1,n,by omega,by omega,hq,by omega,by omega⟩
      · by_cases ha : a=0
        · by_cases h0 : k%3=0
          · simp [h2,ha,h0] at hs
          · simp [h2,ha,h0] at hs
            rcases hs with ⟨rfl, rfl, rfl⟩
            have hpow : 3^(n+1)=3*3^n := by rw [Nat.pow_succ]; omega
            have hq : k/3<3^n := by omega
            refine ⟨1,n,by omega,by omega,hq,by omega,by omega⟩
        · by_cases h0 : k%3=0
          · simp [h2,ha,h0] at hs
            cases hs
            have hpow : 3^(n+1)=3*3^n := by rw [Nat.pow_succ]; omega
            have hq : k/3<3^n := by omega
            refine ⟨1,n,by omega,by omega,hq,by omega,by omega⟩
          · simp [h2,ha,h0] at hs
            have hpow : 3^(n+1)=3*3^n := by rw [Nat.pow_succ]; omega
            have hq : k/3<3^n := by omega
            have hr := ih (a-1) (k/3) (m+2*(k/3)+3)
              aa bb dd hq hbb hs
            rcases hr with ⟨r,s,hrs,hrpos,hbs,hfirst,hpot⟩
            refine ⟨r+1,s,by omega,by omega,hbs,by omega,?_⟩
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
          cases n with
          | zero =>
              simp at hb
              omega
          | succ n => omega
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
                rcases hdepth with ⟨r,s,hrs,hrpos,hbs,hfirst,hpot⟩
                have hsn : s<n := by omega
                have hrec := ih s hsn a1 b1 d1 aa dd hbs hs
                omega
            · simp [hlt] at hs

/-- The drain loses at most n+1 from its first counter, independently of
the magnitude of the block count below 3^n. -/
theorem drainB_first_lower_log (n : Nat) :
    ∀ a b d aa dd : Nat, b<3^n →
      drainB a b d = some (.D aa dd) →
      aa+n+1≥a := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro a b d aa dd hb hs
      by_cases hb0 : b=0
      · subst b
        simp [drainB] at hs
        cases hs
        omega
      · rw [drainB] at hs
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
                have hfirst := evalA_first_lower_log n a (b-1)
                  (d+2*b+3) a1 0 d1 (by omega) hev
                omega
              · have hdepth := evalA_positive_depth n a (b-1)
                  (d+2*b+3) a1 b1 d1 (by omega) (by omega) hev
                rcases hdepth with ⟨r,s,hrs,hrpos,hbs,hfirst,hpot⟩
                have hsn : s<n := by omega
                have hrec := ih s hsn a1 b1 d1 aa dd hbs hs
                omega
            · simp [hlt] at hs

/-- A sharp block-count family: b_0=2 and b_(n+1)=3*b_n+1. -/
def sharpBlock : Nat → Nat
  | 0 => 2
  | n+1 => 3*sharpBlock n + 1

/-- The linear-logarithmic first-loss and third-counter bounds are
simultaneously sharp on this family. -/
theorem drainB_sharp_witness (n d : Nat) :
    drainB (n+2) (sharpBlock n) d =
      some (.D 0 (d+3*sharpBlock n+4*(n+1)+2)) := by
  induction n generalizing d with
  | zero =>
      change drainB 2 2 d = some (.D 0 (d+12))
      have hEval : evalA 2 1 (d+7) = some (0,0,d+12) := by
        simp [evalA]
      rw [drainB.eq_1]
      rw [if_neg (by decide : 2 ≠ 0)]
      rw [hEval]
      simp only [Option.bind_some, if_pos (by decide : 0 < 2)]
      simp [drainB]
  | succ n ih =>
      have hlt : sharpBlock n < 3*sharpBlock n+1 := by omega
      have hEval :
          evalA (n+3) ((3*sharpBlock n+1)-1)
            (d+2*(3*sharpBlock n+1)+3) =
              some (n+2, sharpBlock n, d+2*(3*sharpBlock n+1)+5) := by
        simp [evalA]
      change drainB (n+3) (3*sharpBlock n+1) d =
        some (.D 0 (d+3*sharpBlock (n+1)+4*((n+1)+1)+2))
      rw [drainB.eq_1]
      rw [if_neg (by omega : 3*sharpBlock n+1 ≠ 0)]
      rw [hEval]
      simp only [Option.bind_some, if_pos hlt]
      calc
        drainB (n+2) (sharpBlock n) (d+2*(3*sharpBlock n+1)+5) =
            some (.D 0 ((d+2*(3*sharpBlock n+1)+5)+3*sharpBlock n+4*(n+1)+2)) :=
          ih (d+2*(3*sharpBlock n+1)+5)
        _ = some (.D 0 (d+3*sharpBlock (n+1)+4*((n+1)+1)+2)) := by
          simp [sharpBlock]
          omega

#print axioms evalA_first_lower_log
#print axioms evalA_positive_depth
#print axioms drainB_upper_linear_log
#print axioms drainB_first_lower_log
#print axioms drainB_sharp_witness
end BB6.Agent49DrainLinearLogSource
