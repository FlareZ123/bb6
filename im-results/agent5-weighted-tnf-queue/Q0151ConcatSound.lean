import Q0151PreimageFold
import Q0151RunAddition
import Q0151RightWords

set_option maxHeartbeats 0

/-!
Exact unbounded run-list algebra for q0-151's finite segment/right summaries.
A current left segment is represented by zero or more closed positive
one-runs, followed by a positive open one-run. Its last run merges with
the first right run, if any. The finite segConcat operation agrees with
the right signature of that actual concatenated run list, for every
length and every number of closed runs. This is source-independent
arithmetic; relating the physical bit segment to this run representation
is the remaining bridge.
-/

namespace BB6.Agent5Q0151ConcatSound
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151Preimage
open BB6.Agent5Q0151PreimageFold
open BB6.Agent5Q0151Category
open BB6.Agent5Q0151RunAddition
open BB6.Agent5Q0151RightWords

def runCat (n : Nat) : Nat := cat (n+1)
def runWord (xs : List Nat) : List Nat := xs.map runCat

def segmentOfRuns : List Nat → Nat → SegmentSummary
  | [], last => ⟨0,0,1,runCat last⟩
  | first::rest, last =>
      ⟨runCat first,forward (runWord rest) 0,
        forward (runWord rest) 1,runCat last⟩

def mergeLast (last : Nat) : List Nat → List Nat
  | [] => [last]
  | first::rest => (last+first+1)::rest

theorem suffixMask_append (xs ys : List Nat) :
    suffixMask (xs ++ ys) =
      backward (runWord xs) (suffixMask ys) := by
  induction xs with
  | nil => rfl
  | cons n ns ih =>
      change pre (runCat n) (suffixMask (ns ++ ys)) =
        pre (runCat n) (backward (runWord ns) (suffixMask ys))
      exact congrArg (pre (runCat n)) ih

theorem backward_lt_four (xs : List Nat) (t : Nat)
    (ht : t < 4) : backward xs t < 4 := by
  induction xs with
  | nil => exact ht
  | cons n ns ih =>
      change pre n (backward ns t) < 4
      exact pre_lt_four n (backward ns t)

theorem mask_reconstruct (t : Nat) (ht : t < 4) :
    (if maskAccept t 0 then 1 else 0) +
    (if maskAccept t 1 then 2 else 0) = t := by
  have h : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
  rcases h with h0 | h1 | h2 | h3 <;> subst t <;> decide

theorem pair_preimage (xs : List Nat) (t : Nat) (ht : t < 4) :
    pairPre (forward xs 0) (forward xs 1) t =
      backward xs t := by
  change (if maskAccept t (forward xs 0) then 1 else 0) +
    (if maskAccept t (forward xs 1) then 2 else 0) =
      backward xs t
  rw [← backward_forward xs t 0 (by simp [LiveMode]),
      ← backward_forward xs t 1 (by simp [LiveMode])]
  exact mask_reconstruct (backward xs t) (backward_lt_four xs t ht)

theorem plus_merge (a b : Nat) :
    plus (runCat a) (runCat b) = runCat (a+b+1) := by
  calc
    plus (runCat a) (runCat b) = cat ((a+1)+(b+1)) := plus_cat _ _
    _ = runCat (a+b+1) := by
      congr 1
      omega

theorem concat_run_summary (closed : List Nat) (last : Nat)
    (right : List Nat) :
    segConcat (segmentOfRuns closed last) (rightSig right) =
      rightSig (closed ++ mergeLast last right) := by
  have hl : runCat last ≠ 0 := cat_pos last
  cases closed with
  | nil =>
      cases right with
      | nil =>
          simp [segmentOfRuns,segConcat,rightSig,mergeLast,runCat,
            emptyRight,hl,plus]
      | cons first rest =>
          have hh : runCat first ≠ 0 := cat_pos first
          simp [segmentOfRuns,segConcat,rightSig,mergeLast,
            runCat,hl,hh,plus_merge]
  | cons first rest =>
      have hf : runCat first ≠ 0 := cat_pos first
      cases right with
      | nil =>
          have hpre : pre (runCat last) 4 < 4 :=
            pre_lt_four (runCat last) 4
          have htail : suffixMask (rest ++ [last]) =
              backward (runWord rest) (pre (runCat last) 4) := by
            rw [suffixMask_append]
            rfl
          calc
            segConcat (segmentOfRuns (first::rest) last) (rightSig []) =
                ⟨runCat first,
                  pairPre (forward (runWord rest) 0)
                    (forward (runWord rest) 1)
                    (pre (runCat last) 4)⟩ := by
                simp [segmentOfRuns,segConcat,rightSig,
                  emptyRight,hf,hl,plus]
            _ = ⟨runCat first,suffixMask (rest ++ [last])⟩ := by
                rw [pair_preimage (runWord rest) _ hpre,htail]
            _ = rightSig ((first::rest) ++ mergeLast last []) := by
                simp [rightSig,mergeLast,runCat]
      | cons rightFirst rightRest =>
          have hr : runCat rightFirst ≠ 0 := cat_pos rightFirst
          have hpre : pre (runCat (last+rightFirst+1))
              (suffixMask rightRest) < 4 :=
            pre_lt_four _ _
          have htail : suffixMask
              (rest ++ (last+rightFirst+1)::rightRest) =
              backward (runWord rest)
                (pre (runCat (last+rightFirst+1))
                  (suffixMask rightRest)) := by
            rw [suffixMask_append]
            rfl
          calc
            segConcat (segmentOfRuns (first::rest) last)
                (rightSig (rightFirst::rightRest)) =
                ⟨runCat first,
                  pairPre (forward (runWord rest) 0)
                    (forward (runWord rest) 1)
                    (pre (runCat (last+rightFirst+1))
                      (suffixMask rightRest))⟩ := by
                simp [segmentOfRuns,segConcat,rightSig,
                  hf,hl,hr,plus_merge]
            _ = ⟨runCat first,
                  suffixMask (rest ++ (last+rightFirst+1)::rightRest)⟩ := by
                rw [pair_preimage (runWord rest) _ hpre,htail]
            _ = rightSig ((first::rest) ++
                mergeLast last (rightFirst::rightRest)) := by
                simp [rightSig,mergeLast,runCat]

#print axioms suffixMask_append
#print axioms pair_preimage
#print axioms plus_merge
#print axioms concat_run_summary
end BB6.Agent5Q0151ConcatSound
