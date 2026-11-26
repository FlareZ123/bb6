import LaneClock
import WeightedWord
import WordBlockSource

namespace BB6.Agent12LaneClockSource

open BB6.Agent12WordBlock
open BB6.Agent12BitEventWord
open BB6.Agent12BitPlanes
open BB6.Agent12BitEventCertificate
open BB6.Agent12PlaneOps
open BB6.Agent12LaneWord
open BB6.Agent12LaneCertificate
open BB6.Agent12LaneClock
open BB6.Agent12LaneGenerator
open BB6.Agent12PlaneSum
open BB6.Agent12WeightedWord
open BB6.Agent12Clock

/-- Include the terminal position N in the binary index planes. -/
def indexPlanesSentinel (N : Nat) : List Nat :=
  (List.range (N.log2+1)).map (fun i =>
    indexPlane N i ||| (if N.testBit i then 2^N else 0))

def fillKnownPlane (N q p : Nat) : Nat :=
  let known := q ||| 2^N
  fillKnown (full N) (N.log2+1) 1 (p &&& known) known

def fillKnownPlanes (N q : Nat) (ps : List Nat) : List Nat :=
  ps.map (fillKnownPlane N q)

/-- Recover the held-at-next-event state planes, the zero-run age planes,
    and the two event-coordinate planes from a raw lane trace. The sentinel
    at N is explicitly included in the index planes. -/
def recoverAligned (s t : State) (N q : Nat) : Aligned :=
  let v : BB6.Agent12LaneCertificate.Trace := BB6.Agent12LaneGenerator.recover s t N q
  let bs := fillKnownPlanes N q v.bs
  let ms := fillKnownPlanes N q v.ms
  let p := fillKnownPlane N q v.p
  let ix := indexPlanesSentinel N
  let age := subP (fillKnownPlanes N q ix) ix
  let mask := full N
  let c := constP v.bs.length 2 mask
  let a := subP (subP (shiftP bs) c) [p>>>1]
  let x := subP (subP v.bs c) [v.p]
  ⟨bs,ms,p,age,a,x⟩

/-- Only the local tick equation is needed for the clock argument. -/
structure TickSpec (q N : Nat) (u : Nat → BitState) : Prop where
  next : ∀ j<N, u j = tick (q.testBit j) (u (j+1))

/-- The two local recurrences saying that an event resets the held state
    and an idle bit preserves it while increasing its age. -/
structure OriginRecurrence (q N : Nat) (u orig : Nat → BitState)
    (age : Nat → Nat) : Prop where
  event : ∀ j<N, q.testBit j=true → orig j=u j ∧ age j=0
  idle : ∀ j<N, q.testBit j=false →
    orig j=orig (j+1) ∧ age j=age (j+1)+1

/-- The raw lane at j is exactly the held state after age j idle ticks. -/
theorem lane_eq_idle_origin (q N : Nat) (u orig : Nat → BitState)
    (age : Nat → Nat) (ts : TickSpec q N u)
    (os : OriginRecurrence q N u orig age)
    (hTop : u N=idle (age N) (orig N)) :
    ∀ j≤N, u j=idle (age j) (orig j) := by
  have hrec : ∀ n j, j+n=N → u j=idle (age j) (orig j) := by
    intro n
    induction n with
    | zero =>
        intro j hj
        have h : j=N := by omega
        subst j
        exact hTop
    | succ n ih =>
        intro j hj
        have hjlt : j<N := by omega
        have hnext : j+1+n=N := by omega
        by_cases he : q.testBit j=true
        · obtain ⟨ho,ha⟩ := os.event j hjlt he
          calc
            u j = orig j := ho.symm
            _ = idle (age j) (orig j) := by rw [ha]; simp [idle_zero]
        · have hf : q.testBit j=false := by cases h : q.testBit j <;> simp_all
          obtain ⟨ho,ha⟩ := os.idle j hjlt hf
          calc
            u j = tick (q.testBit j) (u (j+1)) := ts.next j hjlt
            _ = tick false (idle (age (j+1)) (orig (j+1))) := by
              rw [hf, ih (j+1) hnext]
            _ = idle (age (j+1)+1) (orig (j+1)) := tick_false_idle _ _
            _ = idle (age j) (orig j) := by rw [ha,ho]
  intro j hj
  exact hrec (N-j) j (by omega)

/-- At an event, the clock terms are precisely the ordinary section-edge
    clock terms for the depth age(j+1)+1. -/
theorem event_clock (q N j : Nat) (u orig : Nat → BitState)
    (age : Nat → Nat) (ts : TickSpec q N u)
    (os : OriginRecurrence q N u orig age)
    (hj : j<N) (he : q.testBit j=true)
    (hBoundary : u (j+1)=idle (age (j+1)) (orig (j+1)))
    (hState : orig (j+1)=lift s) (hAge : age (j+1)=d) :
    callsAt u orig age j=edgeClock (d+1) s ∧
    weightAt u orig age j=edgeWeight6 (d+1) s := by
  have hpost : u j=lift (step (d+1) s) := by
    calc
      u j = tick (q.testBit j) (u (j+1)) := ts.next j hj
      _ = tick true (idle d (lift s)) := by rw [he,hBoundary,hState,hAge]
      _ = lift (step (d+1) s) := tick_true_lift d s
  constructor
  · simp [callsAt,edgeClock,hState,hAge,lift,parity,gap]
    <;> omega
  · simp [weightAt,edgeWeight6,weight6,BB6.Agent12Clock.cost6,
      hState,hAge,hpost,lift,parity,step]
    grind

/-- Sum the event clocks in descending bit order. This is exactly the
    ordinary word clock, including arbitrary initial idle age. -/
theorem clock_word (q N d : Nat) (u orig : Nat → BitState)
    (age : Nat → Nat) (ts : TickSpec q N u)
    (os : OriginRecurrence q N u orig age) (s : State)
    (hState : orig N=lift s) (hAge : age N=d)
    (hBoundary : u N=idle d (orig N)) :
    clocks (word q d N) s =
      (isum (fun j => if q.testBit j then callsAt u orig age j else 0) N 0,
       isum (fun j => if q.testBit j then weightAt u orig age j else 0) N 0) := by
  induction N generalizing d s with
  | zero =>
      simp [word,clocks,isum]
  | succ N ih =>
      let ts' : TickSpec q N u :=
        ⟨fun j hj => ts.next j (by omega)⟩
      let os' : OriginRecurrence q N u orig age :=
        ⟨fun j hj he => os.event j (by omega) he,
         fun j hj he => os.idle j (by omega) he⟩
      by_cases he : q.testBit N=true
      · obtain ⟨ho,ha⟩ := os.event N (by omega) he
        have hpost : u N=lift (step (d+1) s) := by
          calc
            u N = tick (q.testBit N) (u (N+1)) := ts.next N (by omega)
            _ = tick true (idle d (lift s)) := by rw [he,hBoundary,hState]
            _ = lift (step (d+1) s) := tick_true_lift d s
        have hState' : orig N=lift (step (d+1) s) := ho.trans hpost
        have hAge' : age N=0 := ha
        have hBoundary' : u N=idle 0 (orig N) := by
          simpa [idle_zero] using hpost.trans hState'.symm
        have htail := ih (d:=0) (s:=step (d+1) s) ts' os'
          hState' hAge' hBoundary'
        have hBoundaryAge : u (N+1)=idle (age (N+1)) (orig (N+1)) := by
          rw [hAge]
          exact hBoundary
        have hev := event_clock q (N+1) N u orig age ts os
          (by omega) he hBoundaryAge hState hAge
        simp only [word,he,ite_true,clocks,isum,Nat.zero_add]
        rw [htail]
        simp [hev,Int.add_comm]
      · have hf : q.testBit N=false := by cases h : q.testBit N <;> simp_all
        obtain ⟨ho,ha⟩ := os.idle N (by omega) hf
        have hState' : orig N=lift s := ho.trans hState
        have hAge' : age N=d+1 := by rw [ha,hAge]
        have hBoundary' : u N=idle (d+1) (orig N) := by
          calc
            u N = tick (q.testBit N) (u (N+1)) := ts.next N (by omega)
            _ = tick false (idle d (orig (N+1))) := by rw [hf,hBoundary]
            _ = idle (d+1) (orig (N+1)) := tick_false_idle d _
            _ = idle (d+1) (orig N) := by rw [ho]
        have htail := ih (d:=d+1) (s:=s) ts' os'
          hState' hAge' hBoundary'
        simpa [word,hf,clocks,isum] using htail

/-- The bit-plane sums are the exact aggregate clocks of the represented
    ordinary word, not merely independent polynomial checks. -/
theorem clock_sums_of_checks (s t : State) (N q K : Nat)
    (v : BB6.Agent12LaneCertificate.Trace) (w : BB6.Agent12LaneClock.Aligned)
    (hc : BB6.Agent12LaneCertificate.checked s t N q K v)
    (ha : BB6.Agent12LaneClock.alignmentChecked N q v w) :
    sumTerms N q (callsTerms N w)=(clocks (word q 0 N) s).1 ∧
    sumTerms N q (weightTerms N w)=(clocks (word q 0 N) s).2 := by
  have spec := BB6.Agent12LaneCertificate.spec_of_checked s t N q K v hc
  obtain ⟨hN,hq,hclose,hstart,hfinish,hcounts,hK,hrest⟩ := hc
  let ts : TickSpec q N (lane v) := ⟨spec.next⟩
  have os0 := BB6.Agent12LaneClock.origin_spec N q v w ha
  let os : OriginRecurrence q N (lane v) (origin w) (value w.age) :=
    ⟨os0.event,os0.idle⟩
  have hState : origin w N=lift s := ha.1.trans hstart
  have hAge : value w.age N=0 := ha.2.1
  have hBoundary : lane v N=idle 0 (origin w N) := by
    rcases os0.top with ⟨ho,ha'⟩
    calc
      lane v N=origin w N := ho.symm
      _=idle (value w.age N) (origin w N) :=
        congrArg (fun d => idle d (origin w N)) ha'
  have hclock := clock_word q N 0 (lane v) (origin w) (value w.age)
    ts os s hState hAge hBoundary
  have hcalls := BB6.Agent12LaneClock.calls_sum N q v w ha hq
  have hweights := BB6.Agent12LaneClock.weight_sum N q v w ha hq
  exact ⟨hcalls.trans (congrArg Prod.fst hclock).symm,
         hweights.trans (congrArg Prod.snd hclock).symm⟩

end BB6.Agent12LaneClockSource
