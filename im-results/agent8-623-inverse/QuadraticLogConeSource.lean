import Agent8DrainQuadraticLogSource

/-!
Uniform asymptotically fivefold outer two-step safety cones for original
Cryptids #623 accelerator. All theorems require a successful first step.
The large input ratio needed for a certified second step improves from
roughly 9 to 5, with additive O((log input)^2) ternary budgets.
No conclusion about all-time blank-root survival.
-/

namespace BB6.Agent8QuadraticLogConeSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8DrainQuadraticLogSource
open BB6.Agent8LogConeSource
open BB6.Agent8DrainFirstSharpSource
open BB6.Agent8DrainSevenSource

theorem drainB_quadratic_left_two_step (a b d n ell aa dd : Nat)
    (hs : drainB a b d = some (.D aa dd)) (hb : b<3^n)
    (hgap : d+4*b+n*(n+5)+5+ell≤a)
    (hpower : 2*(d+3*b+n*(n+5))+7≤3^ell) :
    ∃bb ee, highLevelNext (.D aa dd) = some (.D bb ee) := by
  have hf := drainB_first_lower_sharp b a d aa dd hs
  have ht := drainB_upper_quadratic_log n a b d aa dd hb hs
  exact next_safe_left_log aa dd ell (by omega) (by omega)

theorem odd_far_left_quadratic_two_step (a d n ell aa dd : Nat)
    (ha : 0<a) (hd : d%2=1)
    (hb : d+3<3^n) (hroom : 5*d+27+n*(n+5)+ell≤a)
    (hpower : 6*d+35+2*(n*(n+5))≤3^ell)
    (hs : highLevelNext (.D a d)=some (.D aa dd)) :
    ∃bb ee, highLevelNext (.D aa dd)=some (.D bb ee) := by
  have h0 : a≠0 := by omega
  have h1 : d%2=1 ∧ a≥d+5 := ⟨hd,by omega⟩
  simp only [highLevelNext,if_neg h0,if_pos h1] at hs
  exact drainB_quadratic_left_two_step (a-d-5) (d+3) 5 n ell aa dd
    hs hb (by omega) (by omega)

theorem even_far_left_quadratic_two_step (a d n ell aa dd : Nat)
    (ha : 0<a) (hd : d%2=0)
    (hb : d+2<3^n) (hroom : 5*d+17+n*(n+5)+ell≤a)
    (hpower : 6*d+23+2*(n*(n+5))≤3^ell)
    (hs : highLevelNext (.D a d)=some (.D aa dd)) :
    ∃bb ee, highLevelNext (.D aa dd)=some (.D bb ee) := by
  have h0 : a≠0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : d%2=0 ∧ a≥d+3 := ⟨hd,by omega⟩
  simp only [highLevelNext,if_neg h0,if_neg h1,if_pos h2] at hs
  exact drainB_quadratic_left_two_step (a-d-2) (d+2) 2 n ell aa dd
    hs hb (by omega) (by omega)

theorem odd_far_right_quadratic_two_step (a d n ell aa dd : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=1)
    (hb : a-1<3^n) (hroom : 5*a+n*(n+5)+ell≤d)
    (hpower : 6*a+7+2*(n*(n+5))≤3^ell)
    (hs : highLevelNext (.D a d)=some (.D aa dd)) :
    ∃bb ee, highLevelNext (.D aa dd)=some (.D bb ee) := by
  have h0 : a≠0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2≠1 := by omega
  have h4 : a≠d+2 := by omega
  simp only [highLevelNext,if_neg h0,if_neg h1,if_neg h2,if_neg h3,
    if_neg h4,if_pos hd] at hs
  exact drainB_quadratic_left_two_step (d+4-a) (a-1) 3 n ell aa dd
    hs hb (by omega) (by omega)

theorem even_far_right_quadratic_two_step (a d n ell aa dd : Nat)
    (ha : 0<a) (he : a%2=0) (hd : d%2=0)
    (hb : a<3^n) (hroom : 5*a+n*(n+5)+2*n+12+ell≤d)
    (hpower : 6*a+4*n+21+2*(n*(n+5))≤3^ell)
    (hs : highLevelNext (.D a d)=some (.D aa dd)) :
    ∃bb ee, highLevelNext (.D aa dd)=some (.D bb ee) := by
  have h0 : a≠0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2≠1 := by omega
  have h4 : a≠d+2 := by omega
  have h5 : d%2≠1 := by omega
  simp only [highLevelNext,if_neg h0,if_neg h1,if_neg h2,if_neg h3,
    if_neg h4,if_neg h5] at hs
  cases hev : evalA (d+1-a) a (2*a+5) with
  | none => simp [hev] at hs
  | some p =>
    rcases p with ⟨a1,b1,d1⟩
    simp only [hev,Option.bind_some] at hs
    have hf := evalA_first_potential (d+1-a) a (2*a+5) a1 b1 d1 hev
    have ht := evalA_upper_log n (d+1-a) a (2*a+5) a1 b1 d1 hb hev
    have hq := BB6.Agent8DrainLogDepthSource.evalA_second_le_quotient
      (d+1-a) a (2*a+5) a1 b1 d1 hev
    have hbk : b1<3^n := by omega
    exact drainB_quadratic_left_two_step a1 b1 d1 n ell aa dd hs hbk
      (by omega) (by omega)

#print axioms drainB_quadratic_left_two_step
#print axioms odd_far_left_quadratic_two_step
#print axioms even_far_left_quadratic_two_step
#print axioms odd_far_right_quadratic_two_step
#print axioms even_far_right_quadratic_two_step
end BB6.Agent8QuadraticLogConeSource
