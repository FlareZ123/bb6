import Q0151GoodEmptyRight
import Q0151SourceActions11
import Q0151SourceActions12
import Q0151B2AllowedSecond

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
An original-machine / 814-control macro-region bridge for q0-151.
A *physical* stack is constrained by all-length Scan segment grammar
and by the exact 50 saved symbols of the kernel-decided finite invariant.
The three general constructors below transport any authentic stay, push,
or pop macro into a Good region with positive primitive elapsed time.
They do not identify arbitrary abstract paths with physical ones.
-/

namespace BB6.Agent5Q0151RegionLift
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151PhysicalStack
open BB6.Agent5Q0151SourceActions1
open BB6.Agent5Q0151SourceActions3
open BB6.Agent5Q0151SegmentGrammar
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151FiniteCertificate
open BB6.Agent5Q0151StackSaturation

def StackOK (ss : List (List Bool)) : Prop :=
  ∀ s, s ∈ ss → SegGood s ∧ segAppend emptySegment s ∈ savedSegments

def Region (x : P) : Prop :=
  ∃ b : Bool, ∃ s : List Bool, ∃ ss : List (List Bool),
    ∃ rs : List Nat,
      x = boundary (srcQ b) s ss (runBits rs) ∧
      SegGood s ∧ StackOK ss ∧ Good (co b s rs)

theorem initial : Region (boundary 1 [true] [] []) := by
  have hco : co true [true] [] = seed := by decide +kernel
  refine ⟨true,[true],[],[],rfl,good_one,?_,?_⟩
  · intro t ht
    cases ht
  · rw [hco]
    exact seedGood

theorem stay_step {b b' : Bool} {s s' : List Bool}
    {ss : List (List Bool)} {rs rs' : List Nat}
    (hc : Good (co b s rs)) (hss : StackOK ss)
    (hs' : SegGood s')
    (ha : Action.stay (co b' s' rs') ∈ delta (co b s rs))
    (hg : Goes (boundary (srcQ b) s ss (runBits rs))
      (boundary (srcQ b') s' ss (runBits rs'))) :
    ∃ y, Region y ∧
      Goes (boundary (srcQ b) s ss (runBits rs)) y := by
  have hs := finite_closed (co b s rs) hc
    (Action.stay (co b' s' rs')) ha
  change Good (co b' s' rs') at hs
  exact ⟨boundary (srcQ b') s' ss (runBits rs'),
    ⟨b',s',ss,rs',rfl,hs',hss,hs⟩,hg⟩

theorem push_step {b b' : Bool} {s s' : List Bool}
    {ss : List (List Bool)} {rs rs' : List Nat}
    (hc : Good (co b s rs)) (hs : SegGood s)
    (hss : StackOK ss) (hs' : SegGood s')
    (ha : Action.push (co b' s' rs') (segAppend emptySegment s) ∈
      delta (co b s rs))
    (hg : Goes (boundary (srcQ b) s ss (runBits rs))
      (boundary (srcQ b') s' (s::ss) (runBits rs'))) :
    ∃ y, Region y ∧
      Goes (boundary (srcQ b) s ss (runBits rs)) y := by
  have hsafe := finite_closed (co b s rs) hc
    (Action.push (co b' s' rs') (segAppend emptySegment s)) ha
  change Good (co b' s' rs') ∧
    segAppend emptySegment s ∈ savedSegments at hsafe
  have hnew : StackOK (s::ss) := by
    intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with he | hv
    · subst v
      exact ⟨hs,hsafe.2⟩
    · exact hss v hv
  exact ⟨boundary (srcQ b') s' (s::ss) (runBits rs'),
    ⟨b',s',s::ss,rs',rfl,hs',hnew,hsafe.1⟩,hg⟩

theorem pop_step {b : Bool} {s : List Bool}
    {ss : List (List Bool)} {rs decoded : List Nat}
    (hc : Good (co b s rs))
    (hss : StackOK ss)
    (ha : Action.pop (rightSig decoded) ∈ delta (co b s rs))
    (hg : Goes (boundary (srcQ b) s ss (runBits rs))
      (boundary 1 (popSaved ss ++ [true,true,true,true])
        (popTail ss) (runBits decoded)))
    (hr : resume (rightSig decoded)
      (segAppend emptySegment (popSaved ss)) =
      co true (popSaved ss ++ [true,true,true,true]) decoded) :
    ∃ y, Region y ∧
      Goes (boundary (srcQ b) s ss (runBits rs)) y := by
  have hsaved : segAppend emptySegment (popSaved ss) ∈
      savedSegments := by
    cases ss with
    | nil =>
        simpa [popSaved,segAppend] using blankMem
    | cons v vs =>
        simpa [popSaved] using (hss v (by simp)).2
  have hsafe := finite_closed (co b s rs) hc
    (Action.pop (rightSig decoded)) ha
  change ∀ v, v ∈ savedSegments →
    Good (resume (rightSig decoded) v) at hsafe
  have hnew : Good (co true
      (popSaved ss ++ [true,true,true,true]) decoded) := by
    have h := hsafe (segAppend emptySegment (popSaved ss)) hsaved
    rwa [hr] at h
  have hseg : SegGood (popSaved ss ++ [true,true,true,true]) := by
    cases ss with
    | nil =>
        simpa [popSaved] using good_ones_four
    | cons v vs =>
        simpa [popSaved] using
          (good_append (hss v (by simp)).1 good_ones_four)
  have htail : StackOK (popTail ss) := by
    cases ss with
    | nil =>
        intro z hz
        cases hz
    | cons v vs =>
        intro z hz
        apply hss z
        simp only [List.mem_cons]
        exact Or.inr hz
  exact ⟨boundary 1 (popSaved ss ++ [true,true,true,true])
      (popTail ss) (runBits decoded),
    ⟨true,popSaved ss ++ [true,true,true,true],popTail ss,
      decoded,rfl,hseg,htail,hnew⟩,hg⟩

#print axioms initial
#print axioms stay_step
#print axioms push_step
#print axioms pop_step
end BB6.Agent5Q0151RegionLift
