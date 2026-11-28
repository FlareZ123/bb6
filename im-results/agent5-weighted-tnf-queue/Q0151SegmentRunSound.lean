import Q0151ConcatSound

set_option maxHeartbeats 0

/-!
Exact unbounded bit-level decoding of concrete q0-151 left-segment words.
A valid segment consists of a finite list of positive closed one-runs
(each followed by one zero), and a final positive open one-run.
This relates segAppend to the 2-mode run-language algebra used in
Q0151ConcatSound; it is independent of finite exploration.
-/

namespace BB6.Agent5Q0151SegmentRunSound
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151ConcatSound
open BB6.Agent5Q0151Category
open BB6.Agent5Q0151RunAddition
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151PreimageFold

def bitRuns : List Nat → List Bool
  | [] => []
  | n::ns => List.replicate (n+1) true ++ false :: bitRuns ns

def closeRun (s : SegmentSummary) (n : Nat) : SegmentSummary :=
  if s.first = 0 then ⟨runCat n,0,1,0⟩
  else ⟨s.first,dnext s.imageN (runCat n),
    dnext s.imageP (runCat n),0⟩

theorem segAppend_append (s : SegmentSummary) (u v : List Bool) :
    segAppend s (u ++ v) = segAppend (segAppend s u) v := by
  simp [segAppend,List.foldl_append]

theorem appendOnes (s : SegmentSummary) (m n : Nat)
    (h : s.last = cat m) :
    segAppend s (List.replicate n true) =
      {s with last := cat (m+n)} := by
  induction n generalizing s m with
  | zero =>
      simp [segAppend,h]
  | succ n ih =>
      simp only [List.replicate_succ]
      change segAppend (segBit s true) (List.replicate n true) =
        {s with last := cat (m+(n+1))}
      have hs : (segBit s true).last = cat (m+1) := by
        change plus s.last 1 = cat (m+1)
        rw [h,show (1:Nat) = cat 1 by decide, plus_cat]
      have hh := ih (segBit s true) (m+1) hs
      simpa [segBit,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem appendClosed (s : SegmentSummary) (n : Nat)
    (hs : s.last = 0) :
    segAppend s (List.replicate (n+1) true ++ [false]) =
      closeRun s n := by
  rw [segAppend_append]
  have h0 : s.last = cat 0 := by simpa [cat] using hs
  rw [appendOnes s 0 (n+1) h0]
  have hp : cat (n+1) ≠ 0 := cat_pos n
  by_cases hf : s.first = 0
  · simp [segAppend,segBit,segClosed,closeRun,hf,hp,runCat]
  · simp [segAppend,segBit,segClosed,closeRun,hf,hp,runCat]

def closedFold (s : SegmentSummary) (xs : List Nat) : SegmentSummary :=
  xs.foldl closeRun s

theorem closeRun_last (s : SegmentSummary) (n : Nat) :
    (closeRun s n).last = 0 := by
  simp [closeRun]
  split <;> rfl

theorem bitRuns_sound (s : SegmentSummary) (xs : List Nat)
    (hs : s.last = 0) :
    segAppend s (bitRuns xs) = closedFold s xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons n ns ih =>
      change segAppend s ((List.replicate (n+1) true ++ [false]) ++
        bitRuns ns) = closedFold (closeRun s n) ns
      rw [segAppend_append,appendClosed s n hs]
      exact ih (closeRun s n) (closeRun_last s n)

theorem closedFold_summary (xs : List Nat) :
    closedFold emptySegment xs =
      match xs with
      | [] => emptySegment
      | first::rest =>
          ⟨runCat first,forward (runWord rest) 0,
            forward (runWord rest) 1,0⟩ := by
  cases xs with
  | nil => rfl
  | cons first rest =>
      have hfirst : closeRun emptySegment first =
          ⟨runCat first,0,1,0⟩ := by
        rfl
      rw [show closedFold emptySegment (first::rest) =
        closedFold (closeRun emptySegment first) rest by rfl, hfirst]
      induction rest generalizing first with
      | nil => rfl
      | cons n ns ih =>
          -- Both closures are left folds of the same two-mode transition.
          simp only [closedFold,List.foldl_cons,runWord,List.map_cons,
            forward,List.foldl_cons]
          have hf : runCat first ≠ 0 := cat_pos first
          simpa [closeRun,hf,closedFold] using ih first

theorem segmentBits_sound (closed : List Nat) (last : Nat) :
    segAppend emptySegment
        (bitRuns closed ++ List.replicate (last+1) true) =
      segmentOfRuns closed last := by
  rw [segAppend_append,bitRuns_sound emptySegment closed (by decide)]
  rw [closedFold_summary]
  cases closed with
  | nil =>
      have h : (emptySegment : SegmentSummary).last = cat 0 := by decide
      rw [appendOnes _ 0 (last+1) h]
      simp [segmentOfRuns,cat,runCat]
  | cons first rest =>
      have h : (⟨runCat first,forward (runWord rest) 0,
          forward (runWord rest) 1,0⟩ : SegmentSummary).last = cat 0 := by
        decide
      rw [appendOnes _ 0 (last+1) h]
      simp [segmentOfRuns,cat,runCat]

#print axioms appendOnes
#print axioms appendClosed
#print axioms bitRuns_sound
#print axioms closedFold_summary
#print axioms segmentBits_sound
end BB6.Agent5Q0151SegmentRunSound
