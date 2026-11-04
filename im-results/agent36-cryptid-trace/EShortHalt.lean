import Lean.Elab.Tactic.Omega
import Boundary

namespace CryptidBoundary
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- The E-boundary reached by I_(3k+4)(0 1101100 ys). -/
def eShort (k : Nat) (ys : List Bool) : Cfg :=
  ⟨false::false::pairs (4*k+3) ++ [true,true], false,
    [true,true,false,true,true,false,false] ++ ys,4⟩

/-- Universal finite prefix of 65 actual primitive instructions. -/
theorem eShort_pre (k : Nat) (ys : List Bool) :
    (run 65 (eShort k ys)).st=5 ∧
    (run 65 (eShort k ys)).h=true := by
  simp [eShort,run,step,goL,goR,pairs,List.append_assoc]

private theorem halt_step (c : Cfg) (hc : c.st=6) :
    (step c).st=6 := by
  cases c with
  | mk l h r st =>
    simp only at hc
    subst st
    cases h <;> simp [step]

private theorem halt_run (n : Nat) (c : Cfg) (hc : c.st=6) :
    (run n c).st=6 := by
  induction n generalizing c with
  | zero => simpa [run] using hc
  | succ n ih =>
    change (run n (step c)).st=6
    exact ih (step c) (halt_step c hc)

def eShortStart (k : Nat) (ys : List Bool) : Cfg :=
  init (List.replicate (3*k+2) true ++
    false::([true,true,false,true,true,false,false] ++ ys))

def eShortTime (k : Nat) : Nat := 12*k*k+41*k+99

/-- The last state before the first terminal transition is F reading 1. -/
theorem eShort_last (k : Nat) (ys : List Bool) :
    (run (eShortTime k-1) (eShortStart k ys)).st=5 ∧
    (run (eShortTime k-1) (eShortStart k ys)).h=true := by
  have ht : eShortTime k-1=(12*k*k+41*k+33)+65 := by
    simp [eShortTime]
  rw [ht,run_add]
  unfold eShortStart
  rw [prefix_E]
  exact eShort_pre k ys

/-- Every input I_(3k+4)(0 1101100 ys) halts for the first time at T. -/
theorem eShort_halt_exact (k : Nat) (ys : List Bool) :
    (run (eShortTime k) (eShortStart k ys)).st=6 ∧
    ∀ t, t<eShortTime k →
      (run t (eShortStart k ys)).st≠6 := by
  have hh := eShort_last k ys
  have ht : eShortTime k = (eShortTime k-1)+1 := by
    simp [eShortTime]
  constructor
  · rw [ht,run_add]
    have h : (run (eShortTime k-1) (eShortStart k ys)).st=5 := hh.1
    have hb : (run (eShortTime k-1) (eShortStart k ys)).h=true := hh.2
    cases hc : run (eShortTime k-1) (eShortStart k ys) with
    | mk l b r st =>
      simp only [hc, Cfg.st, Cfg.h] at h hb
      subst st
      subst b
      simp [run,step]
  · intro t hlt hbad
    have ht2 : eShortTime k-1 =
      t+((eShortTime k-1)-t) := by omega
    rw [ht2,run_add] at hh
    have hhalt := halt_run ((eShortTime k-1)-t)
      (run t (eShortStart k ys)) hbad
    omega

#print axioms eShort_pre
#print axioms eShort_halt_exact

end CryptidBoundary
