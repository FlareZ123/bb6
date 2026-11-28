import Raw40A0LA0REWitness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent42Raw40A0LA0RELastHole
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper
open BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier
open BB6.Agent42Raw40A0LA0REWitness

/-- Exact completion-uniform weighted bound for the attained 22,169-score
    one-hole cylinder, reusing (rather than rerunning) the authentic 22,168
    blank-step proof in Raw40A0LA0REWitness.lean. -/
theorem last_hole_upper : ∀ m, compatible table m → WeightedBound 22169 m := by
  have hz : (zrun table 22168 start).map project = some z44 :=
    (run_project table 22168 start).trans query
  cases h : zrun table 22168 start with
  | none => simp [h] at hz
  | some z =>
    have hproj : project z = z44 := by
      simpa only [h,Option.map_some,Option.some.injEq] using hz
    have hread : readSlot (embed z) = (5,false) := by
      rw [read_embed]
      have e := congrArg (fun x : Z0 => (x.q,x.l.headD false)) hproj
      exact e.trans (by decide)
    have hrun : knownRun table 22168 = some (embed z) := by
      rw [BB6Coverage.Agent10ZipAudit.knownRun_zip,h]
      rfl
    apply last_hole_sound 22169 table 22168 (embed z) (by rfl) hrun
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
      have hd : (possibleDelays (refine table (5,false) none) 0).all
          (fun d => decide (d ≤ 0)) = true := by decide
      intro d hm
      have h0 : d ≤ 0 := of_decide_eq_true (List.all_eq_true.mp hd d hm)
      omega

/-- Source-exact local maximum: all completions bounded at 22,169, with
    the actually halting F0 completion showing every smaller bound fails. -/
theorem oneHole_exact :
    (∀ m, compatible table m → WeightedBound 22169 m) ∧
    (∀ B < 22169, ∃ m, compatible table m ∧ ¬ WeightedBound B m) := by
  refine ⟨last_hole_upper,?_⟩
  intro B hB
  refine ⟨witness,witness_compatible,?_⟩
  intro hb
  have h := hb 22168 0 witness_halts witness_delay
  omega

#print axioms last_hole_upper
#print axioms oneHole_exact
end BB6.Agent42Raw40A0LA0RELastHole
