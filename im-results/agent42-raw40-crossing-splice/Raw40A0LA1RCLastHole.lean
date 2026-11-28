import Raw40A0LA1RCWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent42Raw40A0LA1RCLastHole
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper
open BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier
open BB6.Agent42Raw40A0LA1RCWitness

/-- C1=1RC one-hole E0 machine: 1764 assigned moves from blank,
    one-unit allowed blank delay, then a halting completion. Therefore
    all E0 completions have weighted score at most 1766. -/
theorem last_hole_upper : ∀ m, compatible table m → WeightedBound 1766 m := by
  have hz : (zrun table 1764 start).map project = some z4 :=
    (run_project table 1764 start).trans query
  cases h : zrun table 1764 start with
  | none => simp [h] at hz
  | some z =>
    have hproj : project z = z4 := by
      simpa only [h,Option.map_some,Option.some.injEq] using hz
    have hread : readSlot (embed z) = (4,false) := by
      rw [read_embed]
      have e := congrArg (fun x : Z0 => (x.q,x.l.headD false)) hproj
      exact e.trans (by decide)
    have hrun : knownRun table 1764 = some (embed z) := by
      rw [BB6Coverage.Agent10ZipAudit.knownRun_zip,h]
      rfl
    apply last_hole_sound 1766 table 1764 (embed z) (by omega) hrun
    · rw [hread]
      rfl
    · rw [hread]
      intro slot hs
      rcases slot with ⟨q,a⟩
      have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
      rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases a <;> first
        | exact ⟨_,rfl⟩
        | exact False.elim (hs rfl)
    · rw [hread]
      have hd : (possibleDelays (refine table (4,false) none) 0).all
          (fun d => decide (d ≤ 1)) = true := by decide
      intro d hm
      have h0 : d ≤ 1 := of_decide_eq_true (List.all_eq_true.mp hd d hm)
      omega

theorem oneHole_exact :
    (∀ m, compatible table m → WeightedBound 1766 m) ∧
    (∀ B < 1766, ∃ m, compatible table m ∧ ¬ WeightedBound B m) := by
  refine ⟨last_hole_upper,?_⟩
  intro B hB
  refine ⟨witness,witness_compatible,?_⟩
  intro hb
  have h := hb 1764 1 witness_halts witness_delay
  omega

#print axioms last_hole_upper
#print axioms oneHole_exact
end BB6.Agent42Raw40A0LA1RCLastHole
