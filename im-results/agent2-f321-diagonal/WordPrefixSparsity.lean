import RootWordCriterion
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321PrefixSparsity
open BB6.Agent31F321Density
open BB6.Agent2F321Bulk
open BB6.Agent2F321Diagonal
open BB6.Agent2F321WordGuard
open BB6.Agent2F321RootWord

/-- Binary digit cost: High consumes one digit, Far consumes two. -/
def S (w : List InverseLetter) : Nat := (compile w).shift
@[simp] theorem S_nil : S []=0 := rfl
@[simp] theorem S_high (w : List InverseLetter) : S (.high::w)=S w+1 := rfl
@[simp] theorem S_far (w : List InverseLetter) : S (.far::w)=S w+2 := rfl

theorem P_eq_pow (w : List InverseLetter) : P w=2^S w := rfl

theorem word_cost_le (w : List InverseLetter) : L w≤3*S w := by
  induction w with
  | nil => decide
  | cons z w ih => cases z <;> simp <;> omega

theorem word_rank {w a d A D} (hw : WordRun w a d A D) : A+D=a+d+L w := by
  induction hw with
  | nil => simp
  | high hg _ ih => simp; omega
  | far h1 h2 _ ih => simp; omega

/-- Exact rank difference and exponential growth of the second-coordinate
    difference between two runs following the same guarded word. -/
theorem word_gap {w : List InverseLetter} {a d b e A D B E δ ε : Nat}
    (h1 : WordRun w a d A D) (h2 : WordRun w b e B E)
    (hx : a+d+δ=b+e) (hd : e+ε≤d) :
    A+D+δ=B+E ∧ E+P w*ε≤D := by
  induction w generalizing a d b e A D B E ε with
  | nil =>
      cases h1; cases h2
      simpa using And.intro hx hd
  | cons z w ih =>
      cases h1 with
      | high hg1 ht1 =>
          cases h2 with
          | high hg2 ht2 =>
              have hx' : (a-d-2)+(2*d+3)+δ=(b-e-2)+(2*e+3) := by omega
              have hd' : 2*e+3+2*ε≤2*d+3 := by omega
              have h := ih ht1 ht2 hx' hd'
              have he : P w*(2*ε)=(2*P w)*ε := by ac_rfl
              simpa only [P_high,he] using h
      | far ha1 hd1 ht1 =>
          cases h2 with
          | far ha2 hd2 ht2 =>
              have hx' : (4*a+6)+(d-3*a)+δ=(4*b+6)+(e-3*b) := by omega
              have hd' : e-3*b+4*ε≤d-3*a := by omega
              have h := ih ht1 ht2 hx' hd'
              have he : P w*(4*ε)=(4*P w)*ε := by ac_rfl
              simpa only [P_far,he] using h

/-- The first Far creates a second-counter gap of exactly three times the
    difference between the original first counters. -/
theorem firstFar_gap {w : List InverseLetter} {a b d A D B E δ : Nat}
    (h1 : WordRun (.far::w) a d A D) (h2 : WordRun (.far::w) b d B E)
    (hx : a+δ=b) : E+P w*(3*δ)≤D := by
  cases h1 with
  | far ha1 hd1 ht1 =>
      cases h2 with
      | far ha2 hd2 ht2 =>
          have hx' : (4*a+6)+(d-3*a)+δ=(4*b+6)+(d-3*b) := by omega
          have hd' : d-3*b+3*δ≤d-3*a := by omega
          exact (word_gap ht1 ht2 hx' hd').2

private theorem pow_two_lower (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

private theorem long_gap_bound (h r : Nat) :
    7*2^h+3*(h+6+r)<3*2^(h+4+r) := by
  induction r with
  | zero =>
      have hp := pow_two_lower h
      simp only [Nat.add_zero]
      rw [Nat.pow_add 2 h 4]
      change 7*2^h+3*(h+6)<3*(2^h*16)
      omega
  | succ r ih =>
      rw [show h+4+(r+1)=(h+4+r)+1 by omega,Nat.pow_succ]
      have hp := pow_two_lower (h+4+r)
      omega

/-- A cutoff-free common-prefix uniqueness theorem. Once a Far-headed word
    has consumed h+6 binary digits, at most one starting first counter R
    can follow that prefix from the same small-second anchor class. -/
theorem long_prefix_unique {h : Nat} {w : List InverseLetter} {R R' c a d b e A D B E : Nat}
    (hc : c=1 ∨ c=2) (hlen : h+6≤S (.far::w))
    (hh1 : HighRun h R c a d) (hh2 : HighRun h R' c b e)
    (hw1 : WordRun (.far::w) a d A D) (hw2 : WordRun (.far::w) b e B E) : R=R' := by
  have h1 := high_run_coordinates hh1
  have h2 := high_run_coordinates hh2
  unfold X Y at h1 h2
  have hmul : 2^h*(2*(c+3))=2*(2^h*(c+3)) := by ac_rfl
  rw [hmul] at h1 h2
  have hde : d=e := by omega
  subst e
  have hfirstBound : a+d+5≤7*2^h := by
    cases hw1 with
    | far h1' h2' _ =>
        have hd : d+3=2^h*(c+3) := by omega
        have hd' : d+3≤5*2^h := by
          rw [hd]
          rcases hc with rfl | rfl <;> omega
        omega
  have hsecondBound : b+d+5≤7*2^h := by
    cases hw2 with
    | far h1' h2' _ =>
        have hd : d+3=2^h*(c+3) := by omega
        have hd' : d+3≤5*2^h := by
          rw [hd]
          rcases hc with rfl | rfl <;> omega
        omega
  have hcost := word_cost_le (.far::w)
  have hRank1 := word_rank hw1
  have hRank2 := word_rank hw2
  have hlen' : h+4≤S w := by simp at hlen; omega
  let r := S w-(h+4)
  have hr : h+4+r=S w := by dsimp [r]; omega
  have hgap := long_gap_bound h r
  rw [hr] at hgap
  have hlenEq : h+6+r=S (.far::w) := by simp; omega
  rw [hlenEq,←P_eq_pow] at hgap
  have hD : D<3*P w := by omega
  have hE : E<3*P w := by omega
  by_cases hab : a<b
  · have he := firstFar_gap (δ:=b-a) hw1 hw2 (by omega)
    have hm := Nat.mul_le_mul_left (P w) (show 3≤3*(b-a) by omega)
    rw [Nat.mul_comm (P w) 3] at hm
    omega
  · by_cases hba : b<a
    · have he := firstFar_gap (δ:=a-b) hw2 hw1 (by omega)
      have hm := Nat.mul_le_mul_left (P w) (show 3≤3*(a-b) by omega)
      rw [Nat.mul_comm (P w) 3] at hm
      omega
    · omega

/-- A word ending in the terminal gate already determines the starting anchor
    uniquely, even when it is too short for long-prefix uniqueness. -/
theorem short_terminal_unique {h w R R' c t t'}
    (h1 : PrefixTail h w R c t) (h2 : PrefixTail h w R' c t') : R=R' := by
  have he1 := prefix_tail_equations h1
  have he2 := prefix_tail_equations h2
  have he : Q w*(t+3)=Q w*(t'+3) := he1.2.trans he2.2.symm
  have ht := Nat.eq_of_mul_eq_mul_left (Q_pos w) he
  omega

/-- For anchors R≤2^k, the leading High block has length at most k when k≥2. -/
theorem leadingHigh_le {h k R c a d : Nat}
    (hk : 2≤k) (hR : R≤2^k) (hc : c=1 ∨ c=2)
    (hh : HighRun h R c a d) : h≤k := by
  have he := high_run_coordinates hh
  unfold X Y at he
  have hmul : 2^h*(2*(c+3))=2*(2^h*(c+3)) := by ac_rfl
  rw [hmul] at he
  have hp := pow_two_lower h
  have hk' : 4≤2^k := by
    have hh := Nat.pow_le_pow_right (by decide : 0<2) hk
    exact hh
  have hbound : 4*2^h≤2^k+5+h := by
    rcases hc with rfl | rfl <;> omega
  by_cases hle : h≤k
  · exact hle
  · have hle' : k+1≤h := by omega
    have hpow := Nat.pow_le_pow_right (by decide : 0<2) hle'
    rw [Nat.pow_succ] at hpow
    omega

#print axioms word_gap
#print axioms long_prefix_unique
#print axioms short_terminal_unique
#print axioms leadingHigh_le
end BB6.Agent2F321PrefixSparsity
