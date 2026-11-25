import ReverseLagBlocks
import LagSource

namespace BB6.Agent45ReverseBlock

open BB6.Agent45.DelayedCarry

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Split the 30-bit delayed target into eight 4-bit blocks and a final
    2-bit block. -/
def parts30 (s B : Nat) : List (List Nat) :=
  [ targetWord 30 s B 4,
    targetWord 30 (s+4) B 4,
    targetWord 30 (s+8) B 4,
    targetWord 30 (s+12) B 4,
    targetWord 30 (s+16) B 4,
    targetWord 30 (s+20) B 4,
    targetWord 30 (s+24) B 4,
    targetWord 30 (s+28) B 2 ]

theorem targetWord_add (n s B k j : Nat) :
    targetWord n s B (k+j) =
      targetWord n s B k ++ targetWord n (s+k) B j := by
  induction j with
  | zero => simp [targetWord]
  | succ j ih =>
    simp [Nat.add_succ,targetWord,ih,List.append_assoc,Nat.add_assoc]

theorem parts30_flat (s B : Nat) :
    (parts30 s B).flatten = targetWord 30 s B 30 := by
  unfold parts30
  simp only [List.flatten_cons,List.flatten_nil]
  rw [targetWord_add 30 s B 28 2,
      targetWord_add 30 s B 24 4,
      targetWord_add 30 s B 20 4,
      targetWord_add 30 s B 16 4,
      targetWord_add 30 s B 12 4,
      targetWord_add 30 s B 8 4,
      targetWord_add 30 s B 4 4]
  simp [List.append_assoc]

theorem parts30_fitted (s B : Nat) :
    Fitted (30+s+3) (parts30 s B) := by
  simp [parts30,Fitted,targetWord_length] <;> omega

/-- Twelve four-bit Covered steps, beginning at the authentic cost-one
    prefix, reach s=49. -/
def run30 : Nat → List Prefix
  | 0 => [(1,16)]
  | k+1 =>
      nextBlockByFold 30 (1+4*k) 4
        (fun B => parts30 (1+4*k+4) B) (run30 k)

theorem run30_covered (k : Nat) :
    Covered 30 (1+4*k) (run30 k) := by
  induction k with
  | zero =>
    simpa [run30] using covered_first 30
  | succ k ih =>
    have hflat : ∀ B,
        (parts30 (1+4*k+4) B).flatten =
          targetWord 30 (1+4*k+4) B 30 := by
      intro B
      exact parts30_flat _ _
    have hfit : ∀ B,
        Fitted (30+(1+4*k+4)+3) (parts30 (1+4*k+4) B) := by
      intro B
      exact parts30_fitted _ _
    have hnext := covered_next_block 30 (1+4*k) 4 (run30 k)
      (fun B => parts30 (1+4*k+4) B) (by omega) ih hflat hfit
    simpa [run30,Nat.mul_succ,Nat.add_assoc] using hnext

/-- The final three-bit extension reaches s=52, so n+s=82. -/
def final30 : List Prefix :=
  nextBlockByFold 30 49 3 (fun B => parts30 52 B) (run30 12)

theorem final30_covered : Covered 30 52 final30 := by
  have hprev : Covered 30 49 (run30 12) := by
    simpa using run30_covered 12
  have hflat : ∀ B, (parts30 52 B).flatten=targetWord 30 52 B 30 := by
    intro B
    exact parts30_flat _ _
  have hfit : ∀ B, Fitted (30+52+3) (parts30 52 B) := by
    intro B
    exact parts30_fitted _ _
  have hnext := covered_next_block 30 49 3 (run30 12)
    (fun B => parts30 52 B) (by omega) hprev hflat hfit
  simpa [final30] using hnext

theorem final30_empty : final30=[] := by decide

/-- The same block filter propagates the existing arithmetic margin
    certificate; the final finite list is empty. -/
theorem run30_cert (k : Nat) :
    Cert 30 82 (1+4*k) (run30 k) := by
  induction k with
  | zero =>
    exact cert_first 30 82 (by decide)
  | succ k ih =>
    have hgood : MarginOK 30 82 (1+4*k) 4 (run30 k)=true := by decide
    have hflat : ∀ B,
        (parts30 (1+4*k+4) B).flatten =
          targetWord 30 (1+4*k+4) B 30 := by
      intro B
      exact parts30_flat _ _
    have hfit : ∀ B,
        Fitted (30+(1+4*k+4)+3) (parts30 (1+4*k+4) B) := by
      intro B
      exact parts30_fitted _ _
    have hnext := cert_next_block 30 82 (1+4*k) 4 (run30 k)
      (fun B => parts30 (1+4*k+4) B) (by omega) ih hgood hflat hfit
    simpa [run30,Nat.mul_succ,Nat.add_assoc] using hnext

theorem cert30 : Cert 30 82 52 [] := by
  have hprev := run30_cert 12
  have hgood : MarginOK 30 82 49 3 (run30 12)=true := by decide
  have hflat : ∀ B, (parts30 52 B).flatten=targetWord 30 52 B 30 := by
    intro B
    exact parts30_flat _ _
  have hfit : ∀ B, Fitted (30+52+3) (parts30 52 B) := by
    intro B
    exact parts30_fitted _ _
  have hnext := cert_next_block 30 82 49 3 (run30 12)
    (fun B => parts30 52 B) (by omega) hprev hgood hflat hfit
  have hempty : nextBlockByFold 30 49 3
      (fun B => parts30 52 B) (run30 12) = [] := by
    simpa [final30] using final30_empty
  simpa [hempty] using hnext

/-- Reprove the existing n=30 critical-reset exclusion using the fitted
    reverse-block Covered/Cert bridge. -/
theorem noCriticalReset30 :
    ¬ BB6.Agent1.Reach 2 (14*2^30-2*30-10) := by
  exact critical_reset_no_reach_of_lag 30 82 52
    (by omega) (by decide) (by omega) (by decide) (by decide) cert30

#print axioms parts30_flat
#print axioms parts30_fitted
#print axioms run30_covered
#print axioms final30_empty
#print axioms run30_cert
#print axioms cert30
#print axioms noCriticalReset30

end BB6.Agent45ReverseBlock
