/-!
# Counted token clauses

Append inside the original #85 namespace. Derived from the source clauses of
google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a
(BusyBeaver/BB6/Accelerations/M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean).
Original source Copyright (c) 2026 Google LLC; Apache-2.0.
The only change to the local tactic and atomic theorems is to retain the
exact ReachesIn exponent instead of existential ReachesPlus.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

local macro "a12cstep" : tactic => `(tactic| (
  try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
    encTokens_nil, encTokens_zero, encTokens_succ,
    encRightNat_nil, encRightNat_zero, encRightNat_succ,
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons, ListBlank.tail_cons,
    ListBlank.head_default_fin, ListBlank.tail_default, ListBlank.cons_zero_default,
    list_pow_zero, list_pow_succ, List.nil_append, List.cons_append,
    zeros_append_default, Nat.mul_zero, Nat.mul_add, Nat.mul_one]
  refine ReachesIn.step_left (by rfl) ?_
  simp only [Tape.move, Tape.write, encTokens_nil, encTokens_zero, encTokens_succ,
    encRightNat_nil, encRightNat_zero, encRightNat_succ,
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons, ListBlank.tail_cons,
    ListBlank.head_default_fin, ListBlank.tail_default, ListBlank.cons_zero_default,
    list_pow_zero, list_pow_succ, List.nil_append, List.cons_append,
    zeros_append_default, Nat.mul_zero, Nat.mul_add, Nat.mul_one]))

local macro "a12cfinish" : tactic => `(tactic| (
  unfold ReachesIn
  try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
    encTokens_nil, encTokens_zero, encTokens_succ,
    encRightNat_nil, encRightNat_zero, encRightNat_succ, encLeft_nil, encRight_nil,
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons, ListBlank.tail_cons,
    ListBlank.head_default_fin, ListBlank.tail_default, ListBlank.cons_zero_default,
    list_pow_zero, list_pow_succ, List.nil_append, List.cons_append,
    zeros_append_default, Nat.mul_zero, Nat.mul_add, Nat.mul_one]
  simp only [encRightNat_cons_one, encLeft_cons_one, encRight_cons_one, multiStep_zero]
  try rfl))

local macro "a12cexecute" n:num : tactic => `(tactic| (
  iterate $n a12cstep
  a12cfinish))

private theorem a12c_EL_0_cons (k1 : ℕ) (K2 : List ℕ) (R3 : List (ℕ × ℕ)) (L : List ℕ) :
    (tok_EL (0 :: k1 :: K2) R3 L) [target]⊢^{1} tok_CR ((k1 + 1) :: K2) R3 L := by
  unfold tok_EL tok_CR; a12cexecute 1

private theorem a12c_EL_1 (K1 : List ℕ) (R3 : List (ℕ × ℕ)) (L : List ℕ) :
    (tok_EL (1 :: K1) R3 L) [target]⊢^{2} tok_EL K1 R3 (0 :: L) := by
  unfold tok_EL; a12cexecute 2

private theorem a12c_EL_2 (K1 : List ℕ) (R3 : List (ℕ × ℕ)) (L : List ℕ) :
    (tok_EL (2 :: K1) R3 (0 :: L)) [target]⊢^{7} tok_EL K1 R3 (0 :: 1 :: L) := by
  unfold tok_EL; a12cexecute 7

private theorem a12c_EL_add3 (k : ℕ) (K1 : List ℕ) (R3 : List (ℕ × ℕ)) (L : List ℕ) :
    (tok_EL ((k + 3) :: K1) R3 L) [target]⊢^{5} tok_DR (2 :: k :: K1) R3 L := by
  unfold tok_EL tok_DR; a12cexecute 5

private theorem a12c_DR_nil_8 (K1 : List ℕ) (R3 : List (ℕ × ℕ)) :
    (tok_DR (2 :: K1) R3 []) [target]⊢^{8} tok_EL K1 R3 [0, 1] := by
  unfold tok_DR tok_EL; a12cexecute 8

private theorem a12c_DR_zero (K1 : List ℕ) (R3 : List (ℕ × ℕ)) (L1 : List ℕ) :
    (tok_DR (2 :: K1) R3 (0 :: L1)) [target]⊢^{4} tok_DR (2 :: 1 :: K1) R3 L1 := by
  unfold tok_DR; a12cexecute 4

private theorem a12c_DR_1_nil_28 (K1 : List ℕ) (R3 : List (ℕ × ℕ)) :
    (tok_DR (2 :: K1) R3 [1]) [target]⊢^{28} tok_EL (1 :: K1) R3 [0, 0, 0, 1] := by
  unfold tok_DR tok_EL; a12cexecute 28

private theorem a12c_DR_succ (K1 : List ℕ) (R3 : List (ℕ × ℕ)) (a : ℕ) (L1 : List ℕ) :
    (tok_DR (2 :: K1) R3 ((a + 1) :: L1)) [target]⊢^{3} tok_CR (1 :: 1 :: K1) R3 (a :: L1) := by
  unfold tok_DR tok_CR; a12cexecute 3

private theorem a12c_CR_1_nil_9 (K1 : List ℕ) (R3 : List (ℕ × ℕ)) :
    (tok_CR (1 :: K1) R3 []) [target]⊢^{9} tok_EL K1 R3 [0, 1] := by
  unfold tok_CR tok_EL; a12cexecute 9

private theorem a12c_CR_add2_nil_21 (k : ℕ) (K1 : List ℕ) (R3 : List (ℕ × ℕ)) :
    (tok_CR ((k + 2) :: K1) R3 []) [target]⊢^{21} tok_EL (k :: K1) R3 [0, 0, 1] := by
  unfold tok_CR tok_EL; a12cexecute 21

private theorem a12c_CR_zero (k : ℕ) (K1 : List ℕ) (R3 : List (ℕ × ℕ)) (L1 : List ℕ) :
    (tok_CR (k :: K1) R3 (0 :: L1)) [target]⊢^{2} tok_CR ((k + 2) :: K1) R3 L1 := by
  unfold tok_CR; a12cexecute 2

private theorem a12c_CR_1_nil_33 (k : ℕ) (K1 : List ℕ) (R3 : List (ℕ × ℕ)) :
    (tok_CR (k :: K1) R3 [1]) [target]⊢^{33} tok_EL (k :: K1) R3 [0, 0, 0, 1] := by
  unfold tok_CR tok_EL; a12cexecute 33

private theorem a12c_CR_1_0 (k : ℕ) (K1 : List ℕ) (R3 : List (ℕ × ℕ)) (L2 : List ℕ) :
    (tok_CR (k :: K1) R3 (1 :: 0 :: L2)) [target]⊢^{5} tok_CR (1 :: (k + 3) :: K1) R3 L2 := by
  unfold tok_CR; a12cexecute 5

private theorem a12c_CR_1_1_nil_25 (k : ℕ) (K1 : List ℕ) (R3 : List (ℕ × ℕ)) :
    (tok_CR (k :: K1) R3 [1, 1]) [target]⊢^{25} tok_EL (k :: K1) R3 [0, 0, 1] := by
  unfold tok_CR tok_EL; a12cexecute 25

private theorem a12c_CR_1_1_cons_25 (k : ℕ) (K1 : List ℕ) (R3 : List (ℕ × ℕ)) (c : ℕ) (L3 : List ℕ) :
    (tok_CR (k :: K1) R3 (1 :: 1 :: c :: L3)) [target]⊢^{25}
      tok_EL (k :: K1) R3 (0 :: 0 :: (c + 2) :: L3) := by
  unfold tok_CR tok_EL; a12cexecute 25

private theorem a12c_CR_1_add2 (k : ℕ) (K1 : List ℕ) (R3 : List (ℕ × ℕ)) (a : ℕ) (L2 : List ℕ) :
    (tok_CR (k :: K1) R3 (1 :: (a + 2) :: L2)) [target]⊢^{15} tok_DR (2 :: 1 :: k :: K1) R3 (a :: L2) :=
      by
  unfold tok_CR tok_DR; a12cexecute 15

private theorem a12c_CR_add2_halts (K : List ℕ) (R3 : List (ℕ × ℕ)) (a : ℕ) (L1 : List ℕ) :
    ∃ cfg_, ((tok_CR K R3 ((a + 2) :: L1)) [target]⊢^{2} cfg_) ∧
            (step target cfg_).isNone := by
  refine ⟨((1 : Fin 2) >> (1 : Fin 2) >> encTokens K R3) {{A}}> (encRightNat (a :: L1)), ?_,
    by simp only [encRightNat]; bb_halt⟩
  unfold tok_CR; a12cexecute 2


private theorem a12cDRsweep (z : ℕ) (K L : List ℕ) :
    ReachesIn target (4*z)
      (tok_DR (2::K) [] (List.replicate z 0 ++ L))
      (tok_DR (2::List.replicate z 1 ++ K) [] L) := by
  induction z generalizing K with
  | zero => exact ReachesIn.zero _ _
  | succ z ih =>
    have h := ReachesIn.trans (a12c_DR_zero K [] (List.replicate z 0 ++ L))
      (ih (1::K))
    change ReachesIn target (4+4*z) (tok_DR (2::K) [] (List.replicate (z+1) 0 ++ L)) (tok_DR (2::(List.replicate z 1 ++ 1::K)) [] L) at h
    rw [a12_rep_push 1 z K] at h
    have hc : 4+4*z = 4*(z+1) := by omega
    rw [hc] at h
    exact h

private theorem a12cELsweep (z : ℕ) (K L : List ℕ) :
    ReachesIn target (2*z)
      (tok_EL (List.replicate z 1 ++ K) [] L)
      (tok_EL K [] (List.replicate z 0 ++ L)) := by
  induction z generalizing L with
  | zero => exact ReachesIn.zero _ _
  | succ z ih =>
    have h := ReachesIn.trans (a12c_EL_1 (List.replicate z 1 ++ K) [] L)
      (ih (0::L))
    rw [a12_rep_push 0 z L] at h
    have hc : 2+2*z = 2*(z+1) := by omega
    rw [hc] at h
    exact h

private theorem a12cCRsweep (z k : ℕ) (K L : List ℕ) :
    ReachesIn target (2*z)
      (tok_CR (k::K) [] (List.replicate z 0 ++ L))
      (tok_CR ((k+2*z)::K) [] L) := by
  induction z generalizing k with
  | zero => exact ReachesIn.zero _ _
  | succ z ih =>
    have h := ReachesIn.trans (a12c_CR_zero k K [] (List.replicate z 0 ++ L))
      (ih (k+2))
    have hc : 2+2*z = 2*(z+1) := by omega
    have hk : k+2+2*z = k+2*(z+1) := by omega
    rw [hc,hk] at h
    exact h

/-- Counted subtract-three H cycle; k+1 is the positive zero-prefix length. -/
private theorem a12cHstep (x k : ℕ) (K : List ℕ) :
    ReachesIn target (6*(k+1)+35)
      (a12H (x+3) (k+1) K []) (a12H x (k+5) K []) := by
  have h1 := a12c_EL_add3 x K [] (List.replicate (k+1) 0 ++ [1])
  have h2 := a12cDRsweep (k+1) (x::K) [1]
  have h3 := a12c_DR_1_nil_28 (List.replicate (k+1) 1 ++ x::K) []
  have h4 := a12cELsweep (k+2) (x::K) [0,0,0,1]
  have hz : List.replicate (k+2) (0:ℕ) ++ [0,0,0,1] =
      List.replicate (k+5) 0 ++ [1] := by
    have h := congrArg (fun L : List ℕ => L ++ [1]) (a12_rep_add (0:ℕ) (k+2) 3)
    simpa [List.append_assoc] using h.symm
  rw [hz] at h4
  have h := ReachesIn.trans h1 (ReachesIn.trans h2 (ReachesIn.trans h3 h4))
  have hc : 5+(4*(k+1)+(28+2*(k+2))) = 6*(k+1)+35 := by omega
  rw [hc] at h
  exact h

/-- Exact quadratic cost of q subtract-three cycles; q may be zero. -/
def a12HCost (q r : ℕ) : ℕ := 12*q*q+(6*r+23)*q

private theorem a12cHbatch (q x k : ℕ) (K : List ℕ) :
    ReachesIn target (a12HCost q (k+1))
      (a12H (x+3*q) (k+1) K [])
      (a12H x (k+1+4*q) K []) := by
  induction q generalizing k with
  | zero =>
    simpa [a12HCost] using ReachesIn.zero target (a12H x (k+1) K [])
  | succ q ih =>
    have h1 := a12cHstep (x+3*q) k K
    have h2 := ih (k+4)
    have hx : x+3*q+3 = x+3*(q+1) := by omega
    have hr : k+4+1+4*q = k+1+4*(q+1) := by omega
    rw [hx] at h1
    rw [hr] at h2
    have h := ReachesIn.trans h1 h2
    have hc : (6*(k+1)+35)+a12HCost q (k+4+1) =
        a12HCost (q+1) (k+1) := by
      unfold a12HCost
      ring
    rw [hc] at h
    exact h

private theorem a12cHmod (x k : ℕ) (K : List ℕ) :
    ReachesIn target (a12HCost (x/3) (k+1))
      (a12H x (k+1) K [])
      (a12H (x%3) (k+1+4*(x/3)) K []) := by
  have h := a12cHbatch (x/3) (x%3) k K
  have hx : x%3+3*(x/3)=x := by omega
  rw [hx] at h
  exact h

#print axioms a12cDRsweep
#print axioms a12cELsweep
#print axioms a12cCRsweep
#print axioms a12cHmod
