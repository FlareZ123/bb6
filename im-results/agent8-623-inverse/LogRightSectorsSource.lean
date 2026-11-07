import Agent8LogRightSource

/-!
Four source #623 branch-specific logarithmic right-safety conditions.
A successful first accelerated transition under the stated inequalities
must be followed by another successful transition. No blank-root outcome.
-/

namespace BB6.Agent8LogRightSectorsSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8LogRightSource
open BB6.Agent8GateRepulsionSource
open BB6.Agent8BudgetSource

theorem odd_left_of_diag_right_safe (a d k ell aa dd : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=1) (hleft : d+5≤a)
    (hbound : d+3 < 3^k)
    (hroom : a+k+ell ≤ 4*d+19)
    (hpow : 2*(a-d-5+k)+3 ≤ 3^ell)
    (hs : highLevelNext (.D a d)=some (.D aa dd)) :
    ∃b e, highLevelNext (.D aa dd)=some (.D b e) := by
  have h0 : a≠0 := by omega
  have h1 : d%2=1 ∧ a≥d+5 := ⟨hd,by omega⟩
  simp only [highLevelNext, if_neg h0, if_pos h1] at hs
  have hf := drainB_first_le_pow k (a-d-5) (d+3) 5 aa dd hbound hs
  have ht := drainB_d3 (d+3) (a-d-5) 5 aa dd hs
  have hp := BB6.Agent49ParitySource.next_preserves_even a d aa dd he (by
    simpa only [highLevelNext,if_neg h0,if_pos h1] using hs)
  exact next_safe_right_log aa dd ell hp (by omega) (by omega)

theorem even_left_of_diag_right_safe (a d k ell aa dd : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=0) (hleft : d+3≤a)
    (hbound : d+2 < 3^k)
    (hroom : a+k+ell ≤ 4*d+10)
    (hpow : 2*(a-d-2+k)+3 ≤ 3^ell)
    (hs : highLevelNext (.D a d)=some (.D aa dd)) :
    ∃b e, highLevelNext (.D aa dd)=some (.D b e) := by
  have h0 : a≠0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : d%2=0 ∧ a≥d+3 := ⟨hd,by omega⟩
  simp only [highLevelNext, if_neg h0,if_neg h1,if_pos h2] at hs
  have hf := drainB_first_le_pow k (a-d-2) (d+2) 2 aa dd hbound hs
  have ht := drainB_d3 (d+2) (a-d-2) 2 aa dd hs
  have hp := BB6.Agent49ParitySource.next_preserves_even a d aa dd he (by
    simpa only [highLevelNext,if_neg h0,if_neg h1,if_pos h2] using hs)
  exact next_safe_right_log aa dd ell hp (by omega) (by omega)

theorem odd_right_of_diag_right_safe (a d k ell aa dd : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=1) (hright : a<d+5)
    (hbound : a-1 < 3^k)
    (hroom : d+4+k+ell ≤ 4*a)
    (hpow : 2*(d+4-a+k)+3 ≤ 3^ell)
    (hs : highLevelNext (.D a d)=some (.D aa dd)) :
    ∃b e, highLevelNext (.D aa dd)=some (.D b e) := by
  have h0 : a≠0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2≠1 := by omega
  have h4 : a≠d+2 := by omega
  simp only [highLevelNext,if_neg h0,if_neg h1,if_neg h2,if_neg h3,
    if_neg h4,if_pos hd] at hs
  have hf := drainB_first_le_pow k (d+4-a) (a-1) 3 aa dd hbound hs
  have ht := drainB_d3 (a-1) (d+4-a) 3 aa dd hs
  have hp := BB6.Agent49ParitySource.next_preserves_even a d aa dd he (by
    simpa only [highLevelNext,if_neg h0,if_neg h1,if_neg h2,if_neg h3,
    if_neg h4,if_pos hd] using hs)
  exact next_safe_right_log aa dd ell hp (by omega) (by omega)

theorem even_right_of_diag_right_safe (a d k ell aa dd : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=0) (hright : a≤d)
    (hbound : a < 3^k)
    (hroom : d+k+ell ≤ 3*a+3)
    (hpow : 2*(d+2-a+k)+3 ≤ 3^ell)
    (hs : highLevelNext (.D a d)=some (.D aa dd)) :
    ∃b e, highLevelNext (.D aa dd)=some (.D b e) := by
  have h0 : a≠0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2≠1 := by omega
  have h4 : a≠d+2 := by omega
  have h5 : d%2≠1 := by omega
  have hp := BB6.Agent49ParitySource.next_preserves_even a d aa dd he hs
  simp only [highLevelNext,if_neg h0,if_neg h1,if_neg h2,if_neg h3,
    if_neg h4,if_neg h5] at hs
  cases hev : evalA (d+1-a) a (2*a+5) with
  | none => simp [hev] at hs
  | some p =>
    rcases p with ⟨a1,b1,d1⟩
    simp only [hev,Option.bind_some] at hs
    have ha1 := evalA_first_le_succ (d+1-a) a (2*a+5) a1 b1 d1 hev
    have hb1 := BB6.Agent8DrainLogDepthSource.evalA_second_le_quotient
      (d+1-a) a (2*a+5) a1 b1 d1 hev
    have hd1 := evalA_third_ge (d+1-a) a (2*a+5) a1 b1 d1 hev
    have hbk : b1 < 3^k := by omega
    have hf := drainB_first_le_pow k a1 b1 d1 aa dd hbk hs
    have ht := drainB_d3 b1 a1 d1 aa dd hs
    exact next_safe_right_log aa dd ell hp (by omega) (by omega)

#print axioms odd_left_of_diag_right_safe
#print axioms even_left_of_diag_right_safe
#print axioms odd_right_of_diag_right_safe
#print axioms even_right_of_diag_right_safe
end BB6.Agent8LogRightSectorsSource
