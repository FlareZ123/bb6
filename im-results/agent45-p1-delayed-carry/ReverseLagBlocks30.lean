import ReverseLagBlocks

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

/-- One finite certificate transition with a supplied margin check. -/
theorem run30_cert_step (k : Nat)
    (hcert : Cert 30 82 (1+4*k) (run30 k))
    (hgood : MarginOK 30 82 (1+4*k) 4 (run30 k)=true) :
    Cert 30 82 (1+4*k+4) (run30 (k+1)) := by
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
    (fun B => parts30 (1+4*k+4) B) (by omega) hcert hgood hflat hfit
  simpa [run30] using hnext

/-- The 12 four-bit transitions, each with its concrete finite margin check. -/
theorem run30_cert : Cert 30 82 49 (run30 12) := by
  have c0 : Cert 30 82 1 (run30 0) := by
    simpa [run30] using cert_first 30 82 (by decide)
  have c1 : Cert 30 82 5 (run30 1) := by
    simpa using run30_cert_step 0 c0 (by decide)
  have c2 : Cert 30 82 9 (run30 2) := by
    simpa using run30_cert_step 1 c1 (by decide)
  have c3 : Cert 30 82 13 (run30 3) := by
    simpa using run30_cert_step 2 c2 (by decide)
  have c4 : Cert 30 82 17 (run30 4) := by
    simpa using run30_cert_step 3 c3 (by decide)
  have c5 : Cert 30 82 21 (run30 5) := by
    simpa using run30_cert_step 4 c4 (by decide)
  have c6 : Cert 30 82 25 (run30 6) := by
    simpa using run30_cert_step 5 c5 (by decide)
  have c7 : Cert 30 82 29 (run30 7) := by
    simpa using run30_cert_step 6 c6 (by decide)
  have c8 : Cert 30 82 33 (run30 8) := by
    simpa using run30_cert_step 7 c7 (by decide)
  have c9 : Cert 30 82 37 (run30 9) := by
    simpa using run30_cert_step 8 c8 (by decide)
  have c10 : Cert 30 82 41 (run30 10) := by
    simpa using run30_cert_step 9 c9 (by decide)
  have c11 : Cert 30 82 45 (run30 11) := by
    simpa using run30_cert_step 10 c10 (by decide)
  have c12 : Cert 30 82 49 (run30 12) := by
    simpa using run30_cert_step 11 c11 (by decide)
  exact c12

theorem cert30 : Cert 30 82 52 [] := by
  have hprev := run30_cert
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

#print axioms parts30_flat
#print axioms parts30_fitted
#print axioms run30_covered
#print axioms final30_empty
#print axioms run30_cert
#print axioms cert30

end BB6.Agent45ReverseBlock
