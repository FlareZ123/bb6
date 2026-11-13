import Low42Physical
import JuncCanonical
import BB429PhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429Low42RootNoFatal

open BB6Coverage BB6Bubble BB429PhysicalFrontier
open BB429OddExcursion BB429FinishScanEDelta
open BB429PhysicalBridge BB429JuncCanonical BB429Low42Physical
open BB429JPhysical

/-- The actual halting gateway is C/0 with a marked immediate right
    neighbor. Harmless C/0/blank-right visits are permitted. -/
def fatalCZero (c : Zipper) : Bool :=
  c.state == 2 && !c.current && c.right.headD false

/-- Original zipper execution guarded against the fatal C/01 gateway. -/
def runNoFatal : Nat → Zipper → Option Zipper
  | 0, c =>
      if fatalCZero c then none else some c
  | n+1, c =>
      if fatalCZero c then none else
        (BB429OddExcursion.one c).bind (runNoFatal n)

/-- A successful guarded run is the exact ordinary source run. -/
theorem runNoFatal_to_run (n : Nat) (z z' : Zipper)
    (hsafe : runNoFatal n z = some z') :
    BB429OddExcursion.run n z = some z' := by
  induction n generalizing z with
  | zero =>
      cases hf : fatalCZero z with
      | true => simp [runNoFatal, hf] at hsafe
      | false =>
          simp [runNoFatal, hf] at hsafe
          simpa [BB429OddExcursion.run] using hsafe
  | succ n ih =>
      cases hf : fatalCZero z with
      | true => simp [runNoFatal, hf] at hsafe
      | false =>
          cases hstep : BB429OddExcursion.one z with
          | none => simp [runNoFatal, hf, hstep] at hsafe
          | some d =>
              have htail : runNoFatal n d = some z' := by
                simpa [runNoFatal, hf, hstep] using hsafe
              have hrun := ih d z' htail
              simp [BB429OddExcursion.run, hstep, hrun]

/-- Every prefix, including the endpoint, of a successful guarded run
    exists in the ordinary zipper semantics and is nonfatal. -/
theorem runNoFatal_prefix (n t : Nat) (z z' : Zipper)
    (hsafe : runNoFatal n z = some z') (ht : t ≤ n) :
    ∃ p, BB429OddExcursion.run t z = some p ∧
      fatalCZero p = false := by
  induction n generalizing t z z' with
  | zero =>
      have ht0 : t = 0 := by omega
      subst t
      cases hf : fatalCZero z with
      | true => simp [runNoFatal, hf] at hsafe
      | false =>
          simp [runNoFatal, hf] at hsafe
          exact ⟨z, by simp [BB429OddExcursion.run], hf⟩
  | succ n ih =>
      cases hf : fatalCZero z with
      | true => simp [runNoFatal, hf] at hsafe
      | false =>
          by_cases ht0 : t = 0
          · subst t
            exact ⟨z, by simp [BB429OddExcursion.run], hf⟩
          · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := by omega
            have ht' : t' ≤ n := by omega
            cases hstep : BB429OddExcursion.one z with
            | none => simp [runNoFatal, hf, hstep] at hsafe
            | some d =>
                have htail : runNoFatal n d = some z' := by
                  simpa [runNoFatal, hf, hstep] using hsafe
                obtain ⟨p, hp, hpSafe⟩ := ih t' d z' htail ht'
                refine ⟨p, ?_, hpSafe⟩
                simp [BB429OddExcursion.run, hstep, hp]

/-- Exact C/0 event trace for the authentic next low-J instance.
    Entries are (primitive time, head displacement, right-neighbor bit). -/
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

def rootLow42Start : Zipper := junc 53 0 20
def rootLow42End : Zipper := junc 0 0 136

/-- The only two C/0 instruction starts in this 1077-step branch are
    at times 510 and 919. Both have a blank immediate right neighbor;
    their head displacements from the J(53,20) entry are 26 and 29. -/
theorem low42_root_czero_event_census :
    cZeroEventTrace 1077 0 0 rootLow42Start =
      [(510, 26, false), (919, 29, false)] := by
  decide

/-- The concrete authentic-root parameter instance of the deficit-4k+2
    family is source-certified to return to Junc(0,0,136) without ever
    executing the fatal C/01 gateway. -/
theorem low42_root_no_fatal_source :
    runNoFatal 1077 rootLow42Start = some rootLow42End := by
  decide

/-- Physical lift to every complete bi-infinite tape represented by
    Junc(53,0,20). Every primitive prefix, including the endpoint,
    avoids C/0 with a marked immediate right neighbor. -/
theorem low42_root_no_fatal_physical
    (c : Config) (hrep : Represents rootLow42Start c) :
    ∃ d : Config,
      BB6Coverage.run target429 1077 c = some d ∧
      Represents rootLow42End d ∧
      (∀ t : Nat, t ≤ 1077 →
        ∃ e : Config,
          BB6Coverage.run target429 t c = some e ∧
          ¬(e.state.val = 2 ∧ e.tape e.head = false ∧
            e.tape (e.head+1) = true)) := by
  have hsource :
      BB429OddExcursion.run 1077 rootLow42Start = some rootLow42End :=
    runNoFatal_to_run 1077 rootLow42Start rootLow42End
      low42_root_no_fatal_source
  obtain ⟨d, hraw, hrepD⟩ :=
    source_run_rep 1077 rootLow42Start c hrep rootLow42End hsource
  refine ⟨d, hraw, hrepD, ?_⟩
  intro t ht
  obtain ⟨p, hp, hpSafe⟩ :=
    runNoFatal_prefix 1077 t rootLow42Start rootLow42End
      low42_root_no_fatal_source ht
  obtain ⟨e, he, hrepE⟩ :=
    source_run_rep t rootLow42Start c hrep p hp
  refine ⟨e, he, ?_⟩
  intro hbad
  rcases hrepE with ⟨hstate, hcurrent, hleft, hright⟩
  have hstate' : p.state = 2 := hstate.symm.trans hbad.1
  have hcurrent' : p.current = false := hcurrent.symm.trans hbad.2.1
  have hright0 : p.right.getD 0 false = true := by
    have hr0 := hright 0
    have hr0' : e.tape (e.head+1) = p.right.getD 0 false := by
      simpa using hr0
    exact hr0'.symm.trans hbad.2.2
  have hrightHead : p.right.headD false = true := by
    cases p.right <;> simp_all
  have hfatal : fatalCZero p = true := by
    simp [fatalCZero, hstate', hcurrent', hrightHead]
  simp [hfatal] at hpSafe

/-- Exact canonical physical J(53,20) instance: the same no-fatal
    certificate ends at Junc(0,0,136), 1077 steps later, with head -109. -/
theorem low42_root_no_fatal_canonical :
    ∃ d : Config,
      BB6Coverage.run target429 1077
        {state:=BB6Bubble.A, head:=0, tape:=jTape 53 20} = some d ∧
      Represents rootLow42End d ∧
      d.head = -109 ∧
      (∀ t : Nat, t ≤ 1077 →
        ∃ e : Config,
          BB6Coverage.run target429 t
            {state:=BB6Bubble.A, head:=0, tape:=jTape 53 20} = some e ∧
          ¬(e.state.val = 2 ∧ e.tape e.head = false ∧
            e.tape (e.head+1) = true)) := by
  let c0 : Config := {state:=BB6Bubble.A, head:=0, tape:=jTape 53 20}
  have hrep : Represents rootLow42Start c0 := by
    simpa [c0] using canonical_junc_rep 53 20 0
  obtain ⟨d, hraw, hrepD, hprefix⟩ :=
    low42_root_no_fatal_physical c0 hrep
  obtain ⟨d', hraw', hrepD', hhead⟩ :=
    low42_raw_head_all 10 21
  have heq : d = d' := Option.some.inj (hraw.symm.trans hraw')
  subst d
  exact ⟨d', hraw', hrepD', hhead, hprefix⟩

/-- Composition lemma for the original physical raw-run semantics. -/
private theorem physical_run_add (m n : Nat) (a b c : Config)
    (h1 : BB6Coverage.run target429 m a = some b)
    (h2 : BB6Coverage.run target429 n b = some c) :
    BB6Coverage.run target429 (m+n) a = some c := by
  rw [BB6Bubble.run_add', h1]
  exact h2

/-- Conditional authentic-root continuation: any genuine blank-root
    entry into Junc(53,0,20) inherits the exact 1077-step no-fatal
    certificate at every absolute primitive time in that segment. -/
theorem blank_root_low42_no_fatal
    (n : Nat) (c : Config)
    (hentry : BB6Coverage.run target429 n blank = some c)
    (hrep : Represents rootLow42Start c) :
    ∃ d : Config,
      BB6Coverage.run target429 (n+1077) blank = some d ∧
      Represents rootLow42End d ∧
      (∀ t : Nat, t ≤ 1077 →
        ∃ e : Config,
          BB6Coverage.run target429 (n+t) blank = some e ∧
          ¬(e.state.val = 2 ∧ e.tape e.head = false ∧
            e.tape (e.head+1) = true)) := by
  obtain ⟨d, hraw, hrepD, hprefix⟩ :=
    low42_root_no_fatal_physical c hrep
  refine ⟨d, ?_, hrepD, ?_⟩
  · exact physical_run_add n 1077 blank c d hentry hraw
  · intro t ht
    obtain ⟨e, he, hgood⟩ := hprefix t ht
    refine ⟨e, ?_, hgood⟩
    exact physical_run_add n t blank c e hentry he

#print axioms low42_root_czero_event_census
#print axioms low42_root_no_fatal_source
#print axioms low42_root_no_fatal_physical
#print axioms low42_root_no_fatal_canonical
#print axioms blank_root_low42_no_fatal

end BB429Low42RootNoFatal
