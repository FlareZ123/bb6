import Agent49CanonicalRayCocycleSource
import Agent49DrainLinearLogSource
import Agent22ExactDrainCocycleDepthSource

/-!
# Unified signed-drop and full-drain depth bounds for the four #623 rays

The first-counter logarithmic bounds (Agent49) and the exact weighted drain
depth bound (Agent22) are packaged here as one source theorem.  The RE ray is
normalized as a single B-drain: its initial evalA call is exactly the first
unfolding of drainB (2*k+3) (m+1) 0.  Thus its count R includes that first
evaluator, and its correction constant is 5 rather than the split convention's
7.  All four rays now use a full-drain count R <= n.
-/

namespace BB6.Agent8RootRayDepthSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent8BudgetSource
open BB6.Agent49CanonicalRayCocycleSource
open BB6.Agent49DrainLinearLogSource
open BB6.Agent22ExactDrainCocycleDepthSource

/-- A successful drain with b < 3^n has signed first-counter drop in
[-n,n+1], and its exact weighted residual is at most n. -/
theorem drainB_depth_package (n a b d aa dd : Nat)
    (hbudget : b <= ternaryOnes a)
    (hpow : b < 3^n)
    (hbase : drainB a b d = some (.D aa dd)) :
    exists r : Nat, r <= n /\
      -(n : Int) <= (a : Int) - (aa : Int) /\
      (a : Int) - (aa : Int) <= (n : Int) + 1 /\
      2*aa + dd = 2*a + d + 3*b + 2*r := by
  have hlo := drainB_first_lower_log n a b d aa dd hpow hbase
  have hup := drainB_first_upper_log n a b d aa dd hpow hbase
  obtain ⟨r, hr, hweight⟩ :=
    drainB_weighted_depth n a b d aa dd hbudget hpow hbase
  refine ⟨r, hr, ?_, ?_, hweight⟩
  · omega
  · omega

/-- Far-left odd boundary drain: the full outer count R gives
delta + 2 beta = 2 R + 4. -/
theorem leftOddBaseDepth (n k m : Nat)
    (hbudget : m+3 <= ternaryOnes k)
    (hpow : m+3 < 3^n) :
    exists B E R, drainB k (m+3) 5 = some (.D B E) /\
      R <= n /\
      -(n : Int) <= (k : Int) - (B : Int) /\
      (k : Int) - (B : Int) <= (n : Int) + 1 /\
      (E : Int) - 3*(m : Int) +
        2*((B : Int) - (k : Int) - 5) = 2*R + 4 := by
  obtain ⟨B, E, hbase⟩ := drainB_safe_ones (m+3) k 5 hbudget
  obtain ⟨R, hR, hDlo, hDhi, hweight⟩ :=
    drainB_depth_package n k (m+3) 5 B E hbudget hpow hbase
  refine ⟨B, E, R, hbase, hR, hDlo, hDhi, ?_⟩
  omega

/-- Far-left even boundary drain: the full outer count R gives
delta + 2 beta = 2 R + 4. -/
theorem leftEvenBaseDepth (n k m : Nat)
    (hbudget : m+2 <= ternaryOnes k)
    (hpow : m+2 < 3^n) :
    exists B E R, drainB k (m+2) 2 = some (.D B E) /\
      R <= n /\
      -(n : Int) <= (k : Int) - (B : Int) /\
      (k : Int) - (B : Int) <= (n : Int) + 1 /\
      (E : Int) - 3*(m : Int) +
        2*((B : Int) - (k : Int) - 2) = 2*R + 4 := by
  obtain ⟨B, E, hbase⟩ := drainB_safe_ones (m+2) k 2 hbudget
  obtain ⟨R, hR, hDlo, hDhi, hweight⟩ :=
    drainB_depth_package n k (m+2) 2 B E hbudget hpow hbase
  refine ⟨B, E, R, hbase, hR, hDlo, hDhi, ?_⟩
  omega

/-- Far-right odd boundary drain: the full outer count R gives
delta + 2 beta = 2 R + 8. -/
theorem rightOddBaseDepth (n k m : Nat)
    (hm : 1 <= m)
    (hbudget : m-1 <= ternaryOnes (2*k+5))
    (hpow : m-1 < 3^n) :
    exists B E R, drainB (2*k+5) (m-1) 3 = some (.D B E) /\
      R <= n /\
      -(n : Int) <= (2*k+5 : Int) - (B : Int) /\
      (2*k+5 : Int) - (B : Int) <= (n : Int) + 1 /\
      (E : Int) - 3*(m : Int) +
        2*((B : Int) - 2*(k : Int) - 1) = 2*R + 8 := by
  obtain ⟨B, E, hbase⟩ := drainB_safe_ones (m-1) (2*k+5) 3 hbudget
  obtain ⟨R, hR, hDlo, hDhi, hweight⟩ :=
    drainB_depth_package n (2*k+5) (m-1) 3 B E hbudget hpow hbase
  refine ⟨B, E, R, hbase, hR, hDlo, hDhi, ?_⟩
  omega

/-- The right-even high-level branch is one full B-drain.  Its initial
evalA call is precisely the first recursive layer of drainB with block m+1. -/
theorem rightEvenBundledBase (m k : Nat)
    (hm : 0 < m)
    (he : m % 2 = 0)
    (hbudget : m < ternaryOnes (2*k+3)) :
    exists B E,
      highLevelNext (.D m (m+2+2*k)) = some (.D B E) /\
      drainB (2*k+3) (m+1) 0 = some (.D B E) := by
  have hbudgetFull : m+1 <= ternaryOnes (2*k+3) := by omega
  obtain ⟨a1, b1, d1, hEval, hbudget1⟩ :=
    evalA_ones_budget (2*k+3) m (2*m+5) hbudget
  have hdecrease : b1 < m+1 := by
    have hq := evalA_second_le_quotient (2*k+3) m (2*m+5) a1 b1 d1 hEval
    omega
  have hbaseEq : highLevelNext (.D m (m+2+2*k)) =
      (evalA (2*k+3) m (2*m+5)).bind
        (fun p => drainB p.1 p.2.1 p.2.2) := by
    rw [highLevelNext]
    have h0 : m != 0 := by omega
    have h1 : !((m+2+2*k)%2=1 /\ m>=m+2+2*k+5) := by omega
    have h2 : !((m+2+2*k)%2=0 /\ m>=m+2+2*k+3) := by omega
    have hodd : m%2 != 1 := by omega
    have heq : m != m+2+2*k+2 := by omega
    have hdBaseNotOne : (m+2+2*k)%2 != 1 := by omega
    simp only [if_neg h0, if_neg h1, if_neg h2, if_neg hodd,
      if_neg heq, if_neg hdBaseNotOne]
    have harg : m+2+2*k+1-m = 2*k+3 := by omega
    rw [harg]
  have hbundle : drainB (2*k+3) (m+1) 0 =
      (evalA (2*k+3) m (2*m+5)).bind
        (fun p => drainB p.1 p.2.1 p.2.2) := by
    rw [drainB]
    simp [hEval, hdecrease]
  obtain ⟨B, E, hDrain⟩ :=
    drainB_safe_ones (m+1) (2*k+3) 0 hbudgetFull
  refine ⟨B, E, ?_, hDrain⟩
  rw [hbaseEq, hbundle, hDrain]

/-- Far-right even boundary drain, bundled from the original high-level
branch: R counts the initial evaluator as well as all subsequent iterations,
so delta + 2 beta = 2 R + 5. -/
theorem rightEvenBaseDepth (n k m : Nat)
    (hm : 0 < m)
    (he : m % 2 = 0)
    (hbudget : m+1 <= ternaryOnes (2*k+3))
    (hpow : m+1 < 3^n) :
    exists B E R,
      highLevelNext (.D m (m+2+2*k)) = some (.D B E) /\
      R <= n /\
      -(n : Int) <= (2*k+3 : Int) - (B : Int) /\
      (2*k+3 : Int) - (B : Int) <= (n : Int) + 1 /\
      (E : Int) - 3*(m : Int) +
        2*((B : Int) - 2*(k : Int) - 2) = 2*R + 5 := by
  have hstrict : m < ternaryOnes (2*k+3) := by omega
  obtain ⟨B, E, hhigh, hDrain⟩ :=
    rightEvenBundledBase m k hm he hstrict
  obtain ⟨R, hR, hDlo, hDhi, hweight⟩ :=
    drainB_depth_package n (2*k+3) (m+1) 0 B E hbudget hpow hDrain
  refine ⟨B, E, R, hhigh, hR, hDlo, hDhi, ?_⟩
  omega

#print axioms drainB_depth_package
#print axioms leftOddBaseDepth
#print axioms leftEvenBaseDepth
#print axioms rightOddBaseDepth
#print axioms rightEvenBundledBase
#print axioms rightEvenBaseDepth

end BB6.Agent8RootRayDepthSource
