import NoFatalGuard
import BubbleExact
import BB429FinishScanEDelta
import BB429JuncHeadExcursion
import BB429PhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429LowEvenR32

open BB6Coverage BB429OddExcursion BB429SourceE1Delta BB429FinishScanEDelta
open BB429JuncHeadExcursion BB429PhysicalFrontier BB429PhysicalBridge
open BB429DeltaPhysicalBridge BB429NoFatalGuard

/-- Authentic-chart input for the concrete low-even r=32 branch. -/
def lowEvenStart : Zipper := junc 45 0 58

/-- First intermediate endpoint after 28 positive-u Junc transitions. -/
def lowEvenMid : Zipper := midApos 17 54 4

/-- Second intermediate endpoint, immediately before the final 869 steps. -/
def lowEvenTurn : Zipper := junc 16 58 0

/-- Exact prepared-chart endpoint predicted by the r=32 low-even row. -/
def lowEvenEnd : Zipper := junc 11 0 146

/-- The first 3192-step segment is the N=28 instance of the general
    positive-u Junc intermediate-return theorem. -/
theorem lowEvenR32_segment1_delta :
    runWithDelta 3192 lowEvenStart = some (lowEvenMid, 56) := by
  have h := juncPos_iter_mid_delta 28 45 0 58 (by omega) (by omega) (by omega)
  have ht : juncPosMidTime 28 0 = 3192 := by
    decide
  simpa [lowEvenStart, lowEvenMid, ht] using h

/-- Exact second segment of the concrete r=32 return. -/
theorem lowEvenR32_segment2_delta :
    runWithDelta 346 lowEvenMid = some (lowEvenTurn, -114) := by
  decide

/-- Exact final segment of the concrete r=32 return. -/
theorem lowEvenR32_segment3_delta :
    runWithDelta 869 lowEvenTurn = some (lowEvenEnd, -23) := by
  decide

/-- Exact total primitive displacement of Junc(45,58) -> Junc(11,146). -/
theorem lowEvenR32_total_delta :
    runWithDelta 4407 lowEvenStart = some (lowEvenEnd, -81) := by
  have h1 := lowEvenR32_segment1_delta
  have h2 := lowEvenR32_segment2_delta
  have h3 := lowEvenR32_segment3_delta
  have h12 : runWithDelta (3192+346) lowEvenStart =
      some (lowEvenTurn, -58) := by
    rw [runWithDelta_add, h1]
    simp only [Option.bind_some]
    rw [h2]
    simp only [Option.map_some]
    decide
  have ht : (3192+346)+869 = 4407 := by omega
  rw [← ht, runWithDelta_add, h12]
  simp only [Option.bind_some]
  rw [h3]
  simp only [Option.map_some]
  decide

/-- First guarded segment. The guard rejects only the genuine C/01
    halting gateway, not harmless C/0 visits with a blank right cell. -/
theorem lowEvenR32_segment1_no_fatal :
    runNoFatal 3192 lowEvenStart = some lowEvenMid := by
  decide

/-- Second guarded segment. -/
theorem lowEvenR32_segment2_no_fatal :
    runNoFatal 346 lowEvenMid = some lowEvenTurn := by
  decide

/-- Final guarded segment, including both harmless C/0/blank-right events. -/
theorem lowEvenR32_segment3_no_fatal :
    runNoFatal 869 lowEvenTurn = some lowEvenEnd := by
  decide

/-- Compose the three guarded source segments into one exact 4407-step
    no-fatal run from Junc(45,58) to Junc(11,146). -/
theorem lowEvenR32_no_fatal_source :
    runNoFatal 4407 lowEvenStart = some lowEvenEnd := by
  have h12 : runNoFatal (3192+346) lowEvenStart = some lowEvenTurn :=
    runNoFatal_compose 3192 346 lowEvenStart lowEvenMid lowEvenTurn
      lowEvenR32_segment1_no_fatal lowEvenR32_segment2_no_fatal
  have htotal : runNoFatal ((3192+346)+869) lowEvenStart = some lowEvenEnd :=
    runNoFatal_compose (3192+346) 869 lowEvenStart lowEvenTurn lowEvenEnd
      h12 lowEvenR32_segment3_no_fatal
  have ht : (3192+346)+869 = 4407 := by omega
  simpa [ht] using htotal

/-- The guarded source execution is the ordinary original-source zipper run. -/
theorem lowEvenR32_source_endpoint :
    BB429OddExcursion.run 4407 lowEvenStart = some lowEvenEnd :=
  runNoFatal_to_run 4407 lowEvenStart lowEvenEnd lowEvenR32_no_fatal_source

/-- Exact C/0 event trace, recording absolute segment time, displacement
    from the original Junc(45,58) entry, and the immediate right bit. -/
def cZeroEventTrace : Nat → Nat → Int → Zipper → List (Nat × Int × Bool)
  | 0, t, delta, c =>
      if c.state == 2 && !c.current then
        [(t, delta, c.right.getD 0 false)]
      else []
  | n+1, t, delta, c =>
      let here :=
        if c.state == 2 && !c.current then
          [(t, delta, c.right.getD 0 false)]
        else []
      match BB429OddExcursion.action c.state c.current with
      | none => here
      | some (_, _, rightward) =>
          match BB429OddExcursion.one c with
          | none => here
          | some d =>
              here ++ cZeroEventTrace n (t+1)
                (delta + (if rightward then 1 else -1)) d

/-- The final 869 steps contain the two C/0 events at global times 3664
    and 4069. Both have a blank immediate right neighbor. -/
theorem lowEvenR32_tail_czero_event_census :
    cZeroEventTrace 869 3538 (-58) lowEvenTurn =
      [(3664, 64, false), (4069, 67, false)] := by
  decide

/-- On every complete physical tape represented by Junc(45,58), the
    4407-step original-machine return reaches Junc(11,146), moves the
    head left by 81, and avoids the exact C/01 halting gateway at every
    primitive prefix, including the endpoint. -/
theorem lowEvenR32_no_fatal_physical
    (c : Config) (hrep : Represents lowEvenStart c) :
    ∃ d : Config,
      BB6Coverage.run target429 4407 c = some d ∧
      Represents lowEvenEnd d ∧
      d.head = c.head - 81 ∧
      (∀ t : Nat, t ≤ 4407 →
        ∃ e : Config,
          BB6Coverage.run target429 t c = some e ∧
          ¬(e.state.val = 2 ∧ e.tape e.head = false ∧
            e.tape (e.head+1) = true)) := by
  obtain ⟨d, hraw, hrepD, hhead⟩ :=
    source_runWithDelta_rep 4407 lowEvenStart c hrep
      lowEvenEnd (-81) lowEvenR32_total_delta
  refine ⟨d, hraw, hrepD, hhead, ?_⟩
  intro t ht
  obtain ⟨p, hp, hpSafe⟩ :=
    runNoFatal_prefix 4407 t lowEvenStart lowEvenEnd
      lowEvenR32_no_fatal_source ht
  obtain ⟨e, he, hrepE⟩ :=
    source_run_rep t lowEvenStart c hrep p hp
  refine ⟨e, he, ?_⟩
  intro hbad
  have hstate : p.state = 2 := hrepE.1.symm.trans hbad.1
  have hcurrent : p.current = false := hrepE.2.1.symm.trans hbad.2.1
  have hr0' : e.tape (e.head+1) = p.right.getD 0 false :=
    BB429PhysicalBridge.represents_right_one p e hrepE
  have hright0 : p.right[0]?.getD false = true := by
    simpa using hr0'.symm.trans hbad.2.2
  have hfatal : fatalCZero p = true := by
    simp [fatalCZero, hstate, hcurrent, hright0]
  simp [hfatal] at hpSafe

/-- Raw-run composition for the unchanged physical machine. -/
private theorem physical_run_add (m n : Nat) (a b c : Config)
    (h1 : BB6Coverage.run target429 m a = some b)
    (h2 : BB6Coverage.run target429 n b = some c) :
    BB6Coverage.run target429 (m+n) a = some c := by
  rw [BB6Bubble.run_add', h1]
  exact h2

/-- Conditional blank-root extension: any genuine blank-root entry into
    Junc(45,58) inherits the complete 4407-step no-fatal physical segment. -/
theorem blank_root_lowEvenR32_no_fatal
    (n : Nat) (c : Config)
    (hentry : BB6Coverage.run target429 n blank = some c)
    (hrep : Represents lowEvenStart c) :
    ∃ d : Config,
      BB6Coverage.run target429 (n+4407) blank = some d ∧
      Represents lowEvenEnd d ∧
      d.head = c.head - 81 ∧
      (∀ t : Nat, t ≤ 4407 →
        ∃ e : Config,
          BB6Coverage.run target429 (n+t) blank = some e ∧
          ¬(e.state.val = 2 ∧ e.tape e.head = false ∧
            e.tape (e.head+1) = true)) := by
  obtain ⟨d, hraw, hrepD, hhead, hprefix⟩ :=
    lowEvenR32_no_fatal_physical c hrep
  refine ⟨d, ?_, hrepD, hhead, ?_⟩
  · exact physical_run_add n 4407 blank c d hentry hraw
  · intro t ht
    obtain ⟨e, he, hgood⟩ := hprefix t ht
    refine ⟨e, ?_, hgood⟩
    exact physical_run_add n t blank c e hentry he

#print axioms lowEvenR32_segment1_delta
#print axioms lowEvenR32_segment2_delta
#print axioms lowEvenR32_segment3_delta
#print axioms lowEvenR32_total_delta
#print axioms lowEvenR32_segment1_no_fatal
#print axioms lowEvenR32_segment2_no_fatal
#print axioms lowEvenR32_segment3_no_fatal
#print axioms lowEvenR32_no_fatal_source
#print axioms lowEvenR32_tail_czero_event_census
#print axioms lowEvenR32_no_fatal_physical
#print axioms blank_root_lowEvenR32_no_fatal

end BB429LowEvenR32
