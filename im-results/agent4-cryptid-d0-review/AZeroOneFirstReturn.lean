import AZeroSource
import AOneSource
import PrefixNoF
import A1100First
import BoundaryPadding

/-!
# First-return strengthening for the two elementary A rows

This is a source-level proof draft for the A-zero (q=b=0) and A-one (q>0,b=0)
DRegular rows. It combines the already checked exact endpoint macros with
Agent 2's quantified prefix no-F lemma, zero-padding bisimulation, and the
original sweepD_noF theorem.

**Compilation status:** not locally preflighted in the authoring invocation:
the local Python and container runtimes returned tool-level ClientError.
Do not treat this file as kernel-checked until it has been compiled and its
axioms printed in the original-source environment.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.CryptidARegularFirstReturn

open CryptidBoundary
open BB6.AZeroSource
open BB6.AOneSource
open BB6.CryptidPrefixFirstReturn

/-- No control-state F occurs at any time strictly before n. -/
def NoF (c : Cfg) (n : Nat) : Prop :=
  ∀ t, t < n → (run t c).st ≠ 5

private theorem appendNoF (c d : Cfg) (a b : Nat)
    (hc : NoF c a) (he : run a c = d) (hd : NoF d b) :
    NoF c (a+b) := by
  intro t ht
  by_cases hsmall : t < a
  · exact hc t hsmall
  · obtain ⟨u, hu⟩ : ∃ u, t = a+u := ⟨t-a, by omega⟩
    rw [hu, run_add, he]
    exact hd u (by omega)

/-- The A-empty close has no intermediate F state, including its initial
    A-state and the three-step entry into the D sweep. -/
private theorem aEmpty_noF (m : Nat) :
    NoF (BB6.AZeroSource.aEmpty m) (2*m+6) := by
  intro t ht
  by_cases hsmall : t < 3
  · have hcases : t=0 ∨ t=1 ∨ t=2 := by omega
    rcases hcases with rfl | rfl | rfl
    all_goals simp [BB6.AZeroSource.aEmpty, run, step, goL, goR, pairs]
  · obtain ⟨u, hu⟩ : ∃ u, t=3+u := ⟨t-3, by omega⟩
    rw [hu, run_add, BB6.AZeroSource.a_empty_three]
    exact CryptidBoundary.sweepD_noF m [true,true] u (by omega)

/-- Padding the implicit all-zero tail by one explicit zero lets the
    universal prefixA_positive_noF theorem apply to the blank-right case. -/
private theorem zeroPrefixNoF (k t : Nat)
    (hpos : 0<t) (ht : t<12*k*k+41*k+32) :
    (run t (init (List.replicate (3*k+1) true))).st ≠ 5 := by
  let xs := List.replicate (3*k+1) true
  have h := (BB6.BoundaryPadding.source_init_pad t 1 xs).2.2.2
  change (run t (init xs)).st =
    (run t (init (xs ++ [false]))).st at h
  rw [h]
  exact BB6.CryptidPrefixFirstReturn.prefixA_positive_noF
    k [] t hpos ht

/-- Strict positive-time first return for the canonical A row with q=b=0.
    The endpoint is already supplied by AZeroSource.full_A_zero. -/
theorem full_A_zero_first_return (k : Nat) :
    ∀ t, 0<t → t<12*k*k+49*k+44 →
      (run t (init (List.replicate (3*k+1) true))).st ≠ 5 := by
  intro t hpos ht
  by_cases hprefix : t < 12*k*k+41*k+32
  · exact zeroPrefixNoF k t hpos hprefix
  · have hp : t = (12*k*k+41*k+32) +
        (t-(12*k*k+41*k+32)) := by omega
    rw [hp, run_add, prefix_A_nil]
    change (run (t-(12*k*k+41*k+32))
      (BB6.AZeroSource.aEmpty (4*k+3))).st ≠ 5
    exact aEmpty_noF (4*k+3) (t-(12*k*k+41*k+32)) (by omega)

/-- Each two-step 10-token A increment avoids state F. -/
private theorem ab_ten_noF (m : Nat) (ys : List Bool) :
    NoF (BB6.AOneSource.ab m (true::false::ys)) 2 := by
  intro t ht
  have hcases : t=0 ∨ t=1 := by omega
  rcases hcases with rfl | rfl
  all_goals simp [BB6.AOneSource.ab, run, step, goL, goR, pairs]

/-- The complete repeated 10-token prefix avoids F for every q and suffix. -/
private theorem ab_ten_run_noF (m q : Nat) (ys : List Bool) :
    NoF (BB6.AOneSource.ab m (pairs q ++ ys)) (2*q) := by
  induction q generalizing m ys with
  | zero =>
      intro t ht
      omega
  | succ q ih =>
      have hstart :
          BB6.AOneSource.ab m (pairs (q+1) ++ ys) =
          BB6.AOneSource.ab m (true::false::(pairs q ++ ys)) := by
        rfl
      rw [hstart]
      have h := appendNoF
        (BB6.AOneSource.ab m (true::false::(pairs q ++ ys)))
        (BB6.AOneSource.ab (m+1) (pairs q ++ ys))
        2 (2*q)
        (ab_ten_noF m (pairs q ++ ys))
        (BB6.AOneSource.a_ten m (pairs q ++ ys))
        (ih (m+1) ys)
      simpa [show 2*(q+1)=2+2*q by omega] using h

/-- The five-step A-one front and following D sweep contain no F before
    their terminal F/0 section. -/
private theorem ab_one_close_noF (m : Nat) :
    NoF (BB6.AOneSource.ab m [true]) (2*m+10) := by
  have hfront : NoF (BB6.AOneSource.ab m [true]) 5 := by
    intro t ht
    have hcases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    all_goals simp [BB6.AOneSource.ab, run, step, goL, goR, pairs]
  have hrun : run 5 (BB6.AOneSource.ab m [true]) =
      sweepD (m+1) [true,true] :=
    BB6.AOneSource.a_one_front m
  have htail : NoF (sweepD (m+1) [true,true])
      (2*(m+1)+3) := by
    intro t ht
    exact CryptidBoundary.sweepD_noF (m+1) [true,true] t ht
  have h := appendNoF
    (BB6.AOneSource.ab m [true])
    (sweepD (m+1) [true,true])
    5 (2*(m+1)+3) hfront hrun htail
  simpa [show 5+(2*(m+1)+3)=2*m+10 by omega] using h

/-- A complete A-one section (q alternating 10 tokens followed by one)
    has no intermediate F state. -/
private theorem ab_suffix_noF (m q : Nat) :
    NoF (BB6.AOneSource.ab m (pairs q ++ [true]))
      (2*q + 2*(m+q) + 10) := by
  exact appendNoF
    (BB6.AOneSource.ab m (pairs q ++ [true]))
    (BB6.AOneSource.ab (m+q) [true])
    (2*q) (2*(m+q)+10)
    (ab_ten_run_noF m q [true])
    (BB6.AOneSource.a_ten_run m q [true])
    (ab_one_close_noF (m+q))

/-- Strict positive-time first return for the canonical A row q>0,b=0.
    The endpoint is supplied by AOneSource.full_A_one. -/
theorem full_A_one_first_return (k q : Nat) :
    ∀ t, 0<t →
      t < 12*k*k+41*k+32+2*q+2*(4*k+3+q)+10 →
      (run t (init (List.replicate (3*k+1) true ++
        false::(pairs q ++ [true])))).st ≠ 5 := by
  intro t hpos ht
  by_cases hprefix : t < 12*k*k+41*k+32
  · exact BB6.CryptidPrefixFirstReturn.prefixA_positive_noF
      k (pairs q ++ [true]) t hpos hprefix
  · have hp : t = (12*k*k+41*k+32) +
        (t-(12*k*k+41*k+32)) := by omega
    rw [hp, run_add, prefix_A]
    change (run (t-(12*k*k+41*k+32))
      (BB6.AOneSource.ab (4*k+3) (pairs q ++ [true]))).st ≠ 5
    exact ab_suffix_noF (4*k+3) q
      (t-(12*k*k+41*k+32)) (by omega)

#print axioms full_A_zero_first_return
#print axioms full_A_one_first_return

end BB6.CryptidARegularFirstReturn
