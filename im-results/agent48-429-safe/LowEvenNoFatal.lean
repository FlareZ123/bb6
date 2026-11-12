import BB429JuncHeadExcursion
import BB429PhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429LowEvenNoFatal

open BB6Coverage BB429OddExcursion BB429JuncHeadExcursion
open BB429PhysicalFrontier BB429PhysicalBridge

/-- The actual halting gateway is C/0 with a marked cell immediately
    to the right. Harmless C/0/blank-right visits are allowed. -/
def fatalCZero (c : Zipper) : Bool :=
  c.state == 2 && !c.current && c.right.headD false

/-- Run the original zipper interpreter, rejecting only a C/0 whose
    immediate right neighbor is marked. This is stricter than raw
    halting, since it rejects the fatal gateway before the next D/1
    instruction. -/
def runNoFatal : Nat → Zipper → Option Zipper
  | 0, c =>
      if fatalCZero c then none else some c
  | n+1, c =>
      if fatalCZero c then none else
        (BB429OddExcursion.one c).bind (runNoFatal n)

/-- A successful guarded run is the exact ordinary original-source run. -/
theorem runNoFatal_to_run (n : Nat) (z z' : Zipper)
    (hsafe : runNoFatal n z = some z') :
    BB429OddExcursion.run n z = some z' := by
  induction n generalizing z with
  | zero =>
      cases hf : fatalCZero z with
      | true =>
          simp [runNoFatal, hf] at hsafe
      | false =>
          simp [runNoFatal, hf] at hsafe
          simpa [BB429OddExcursion.run] using hsafe
  | succ n ih =>
      cases hf : fatalCZero z with
      | true =>
          simp [runNoFatal, hf] at hsafe
      | false =>
          cases hstep : BB429OddExcursion.one z with
          | none =>
              simp [runNoFatal, hf, hstep] at hsafe
          | some d =>
              have htail : runNoFatal n d = some z' := by
                simpa [runNoFatal, hf, hstep] using hsafe
              have hrun := ih d z' htail
              simp [BB429OddExcursion.run, hstep, hrun]

/-- Every source configuration through the endpoint of a successful
    guarded run is nonfatal, and every prefix exists in the ordinary
    zipper semantics. -/
theorem runNoFatal_prefix (n t : Nat) (z z' : Zipper)
    (hsafe : runNoFatal n z = some z') (ht : t ≤ n) :
    ∃ p, BB429OddExcursion.run t z = some p ∧
      fatalCZero p = false := by
  induction n generalizing t z z' with
  | zero =>
      have ht0 : t = 0 := by omega
      subst t
      cases hf : fatalCZero z with
      | true =>
          simp [runNoFatal, hf] at hsafe
      | false =>
          simp [runNoFatal, hf] at hsafe
          exact ⟨z, by simp [BB429OddExcursion.run], hf⟩
  | succ n ih =>
      cases hf : fatalCZero z with
      | true =>
          simp [runNoFatal, hf] at hsafe
      | false =>
          by_cases ht0 : t = 0
          · subst t
            exact ⟨z, by simp [BB429OddExcursion.run], hf⟩
          · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := by omega
            have ht' : t' ≤ n := by omega
            cases hstep : BB429OddExcursion.one z with
            | none =>
                simp [runNoFatal, hf, hstep] at hsafe
            | some d =>
                have htail : runNoFatal n d = some z' := by
                  simpa [runNoFatal, hf, hstep] using hsafe
                obtain ⟨p, hp, hpSafe⟩ := ih t' d z' htail ht'
                refine ⟨p, ?_, hpSafe⟩
                simp [BB429OddExcursion.run, hstep, hp]

def lowEvenStart : Zipper := junc 49 0 2
def lowEvenEnd : Zipper := junc 11 0 98

def rootSegmentStart : Zipper := junc 10 0 74
def rootSegmentEnd : Zipper := junc 11 0 98

/-- Exact C/0 event census for the 3619-step J(10,74) return. Each
    entry records (time, head displacement from the segment entry,
    whether the immediate right neighbor is marked). -/
def cZeroEventTrace : Nat → Nat → Int → Zipper → List (Nat × Int × Bool)
  | 0, t, delta, c =>
      if c.state == 2 && !c.current then
        [(t, delta, c.right.headD false)]
      else []
  | n+1, t, delta, c =>
      let here :=
        if c.state == 2 && !c.current then
          [(t, delta, c.right.headD false)]
        else []
      match BB429OddExcursion.action c.state c.current with
      | none => here
      | some (_, _, rightward) =>
          match BB429OddExcursion.one c with
          | none => here
          | some d =>
              here ++ cZeroEventTrace n (t+1)
                (delta + (if rightward then 1 else -1)) d

/-- The two C/0 entries in the low-even r=96 return are both
    blank-right and occur below its +84 head maximum. -/
theorem rootSegment_czero_event_census :
    cZeroEventTrace 3619 0 0 rootSegmentStart =
      [(2924, 80, false), (3329, 83, false)] := by
  decide

/-- The complete J(10,74) -> J(11,98) source segment rejects every
    fatal C/0 gateway, while allowing the two harmless blank-right
    C/0 entries recorded above. -/
theorem rootSegment_no_fatal_source :
    runNoFatal 3619 rootSegmentStart = some rootSegmentEnd := by
  decide

/-- The concrete 719-step low-even r=96 return has exactly the
    required no-fatal-gateway property. The ordinary run endpoint and
    prefix maximum are independently recorded in Low43Continuation.lean. -/
theorem lowEven_r96_no_fatal_source :
    runNoFatal 719 lowEvenStart = some lowEvenEnd := by
  decide

/-- On every physical infinite tape represented by J(49,2), the entire
    719-step original-machine return to J(11,98) avoids the genuine
    halting gateway at every primitive prefix, including the endpoint. -/
theorem lowEven_r96_no_fatal_physical
    (c : Config) (hrep : Represents lowEvenStart c) :
    ∃ d : Config,
      BB6Coverage.run target429 719 c = some d ∧
      Represents lowEvenEnd d ∧
      (∀ t : Nat, t ≤ 719 →
        ∃ e : Config,
          BB6Coverage.run target429 t c = some e ∧
          ¬(e.state.val = 2 ∧ e.tape e.head = false ∧
            e.tape (e.head+1) = true)) := by
  have hsource : BB429OddExcursion.run 719 lowEvenStart = some lowEvenEnd :=
    runNoFatal_to_run 719 lowEvenStart lowEvenEnd lowEven_r96_no_fatal_source
  obtain ⟨d, hraw, hrepD⟩ :=
    source_run_rep 719 lowEvenStart c hrep lowEvenEnd hsource
  refine ⟨d, hraw, hrepD, ?_⟩
  intro t ht
  obtain ⟨p, hp, hpSafe⟩ :=
    runNoFatal_prefix 719 t lowEvenStart lowEvenEnd
      lowEven_r96_no_fatal_source ht
  obtain ⟨e, he, hrepE⟩ :=
    source_run_rep t lowEvenStart c hrep p hp
  refine ⟨e, he, ?_⟩
  intro hbad
  rcases hrepE with ⟨hs, hcur, hleft, hright⟩
  have hstate : p.state = 2 := hs.symm.trans hbad.1
  have hcurrent : p.current = false := hcur.symm.trans hbad.2.1
  have hright0 : p.right.getD 0 false = true := by
    have hr0 := hright 0
    have hr0' : e.tape (e.head+1) = p.right.getD 0 false := by
      simpa using hr0
    exact hr0'.symm.trans hbad.2.2
  have hrightHead : p.right.headD false = true := by
    cases p.right <;> simp_all
  have hfatal : fatalCZero p = true := by
    simp [fatalCZero, hstate, hcurrent, hrightHead]
  simp [hfatal] at hpSafe

#print axioms lowEven_r96_no_fatal_source
#print axioms lowEven_r96_no_fatal_physical

end BB429LowEvenNoFatal
