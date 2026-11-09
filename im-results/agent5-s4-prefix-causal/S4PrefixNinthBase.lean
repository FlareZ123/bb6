import S4Prefix5457
import Lean.Elab.Tactic.Omega

namespace S4PrefixNinth
open S4PrefixCausal S4PrefixEighthCycle S4Prefix5457 S4Toggle S4PrefixSeven
open S4PrefixContraction

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- The first nine digits of the source-certified state at return 5457. -/
def cycle9Start : List Nat := cycle8PeriodicStart ++ [171050]

/-- The remaining nine digits of the complete source-certified state. -/
def tail5457 : List Nat :=
  [366446, 435688, 443554, 1702180, 1770018, 211301, 281569, 35137, 35134]

theorem s5457_decomp :
    S4Prefix5457.s5457 = cycle9Start ++ tail5457 := by
  rfl

/-- Tail-recursive iteration of the same source prefix map. -/
def prefixRunFast : Nat → List Nat → List Nat
  | 0, xs => xs
  | n+1, xs => prefixRunFast n (pp xs)

theorem prefixRun_commute_pp (n : Nat) (xs : List Nat) :
    prefixRun n (pp xs) = pp (prefixRun n xs) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [prefixRun, ih]

theorem prefixRunFast_eq (n : Nat) : ∀ xs,
    prefixRunFast n xs = prefixRun n xs := by
  induction n with
  | zero => intro xs; rfl
  | succ n ih =>
      intro xs
      change prefixRunFast n (pp xs) = pp (prefixRun n xs)
      rw [ih (pp xs), prefixRun_commute_pp n xs]

private theorem prun_add_local (m n : Nat) (xs : List Nat) :
    prun (m+n) xs = (prun m xs).bind (prun n) := by
  induction n with
  | zero => simp [prun]
  | succ n ih =>
      rw [Nat.add_succ]
      simp only [prun, ih]
      cases h : prun m xs with
      | none => simp [h]
      | some U => simp [h, prun]

/-- Every successful root state after return 5457 has the nine-digit
prefix obtained by iterating the source prefix map from cycle9Start. -/
theorem root_nine_prefix_from_5457 (n : Nat) (U : List Nat)
    (h : prun (5457+n) seed = some U) :
    U.take 9 = prefixRun n cycle9Start := by
  have hstate : prun n S4Prefix5457.s5457 = some U := by
    rw [prun_add_local, S4Prefix5457.seed5457] at h
    simpa using h
  have hfull : prun n (cycle9Start ++ tail5457) = some U := by
    rw [s5457_decomp] at hstate
    exact hstate
  simpa [cycle9Start, cycle8PeriodicStart, S4PrefixSeven.cycle7] using
    (prun_prefix n cycle9Start tail5457 U hfull)

/-- Additivity of the forward prefix iteration. -/
private theorem prefixRun_add_local (m n : Nat) (xs : List Nat) :
    prefixRun (m+n) xs = prefixRun n (prefixRun m xs) := by
  induction n with
  | zero => simp [prefixRun]
  | succ n ih =>
      rw [Nat.add_succ]
      simp [prefixRun, ih]

theorem prefixRunFast_add (m n : Nat) (xs : List Nat) :
    prefixRunFast (m+n) xs = prefixRunFast n (prefixRunFast m xs) := by
  calc
    prefixRunFast (m+n) xs = prefixRun (m+n) xs := prefixRunFast_eq _ _
    _ = prefixRun n (prefixRun m xs) := prefixRun_add_local m n xs
    _ = prefixRunFast n (prefixRunFast m xs) := by
      rw [prefixRunFast_eq, prefixRunFast_eq]

/-- Appending one digit commutes with every iterate, with a possibly
changed final digit. -/
theorem prefixRunFast_append_one (n : Nat) : ∀ xs v,
    ∃ w, prefixRunFast n (xs ++ [v]) =
      prefixRunFast n xs ++ [w] := by
  induction n with
  | zero =>
      intro xs v
      exact ⟨v, rfl⟩
  | succ n ih =>
      intro xs v
      obtain ⟨w, hw⟩ := pp_append_one xs v
      obtain ⟨w', hw'⟩ := ih (pp xs) w
      refine ⟨w', ?_⟩
      change prefixRunFast n (pp (xs ++ [v])) =
        prefixRunFast n (pp xs) ++ [w']
      rw [hw, hw']

def return9Fast (v : Nat) : Nat :=
  (prefixRunFast 20480 (cycle8PeriodicStart ++ [v])).getLast!

/-- One 20,480-return block resets the first eight digits and updates
the ninth digit by return9Fast. -/
theorem block20480_ninth (v : Nat) :
    prefixRunFast 20480 (cycle8PeriodicStart ++ [v]) =
      cycle8PeriodicStart ++ [return9Fast v] := by
  obtain ⟨w, hw⟩ :=
    prefixRunFast_append_one 20480 cycle8PeriodicStart v
  have hprefix :
      prefixRunFast 20480 cycle8PeriodicStart = cycle8PeriodicStart := by
    rw [prefixRunFast_eq, prefixRun_20480_cycle]
  have hlast : return9Fast v = w := by
    unfold return9Fast
    rw [hw, hprefix]
    simp
  rw [hw, hprefix, hlast]

#print axioms s5457_decomp
#print axioms root_nine_prefix_from_5457
#print axioms block20480_ninth

end S4PrefixNinth
