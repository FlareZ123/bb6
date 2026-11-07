import BB429E1ShiftDelta
import BB429PhysicalBridge
import Lean.Elab.Tactic.Omega

namespace BB429DeltaPhysicalBridge
open BB6Coverage
open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta BB429SourceRows BB429PhysicalFrontier
open BB429E1ShiftDelta BB429PhysicalBridge

/-- A single source zipper instruction with signed displacement has an
    exactly corresponding raw-table step, including its physical head move. -/
theorem sim_one_delta (z : Zipper) (c : Config)
    (hrep : Represents z c) (z' : Zipper) (d : Int)
    (hz : oneWithDelta z = some (z', d)) :
    ∃ c', rawStep BB429PhysicalFrontier.target429 c = some c' ∧
      Represents z' c' ∧ c'.head = c.head + d := by
  rcases hrep with ⟨hstate, hcur, hleft, hright⟩
  have hsource : action z.state z.current =
      (BB429PhysicalFrontier.target429 (readSlot c)).map
        (fun move => (move.next.val, move.write, move.right)) := by
    have h0 := BB429SourceRows.action_matches_target c.state (c.tape c.head)
    simp only [readSlot]
    rw [← hstate, ← hcur]
    exact h0
  cases hact : action z.state z.current with
  | none =>
      simp [oneWithDelta, hact] at hz
  | some a =>
      rcases a with ⟨s, w, rightward⟩
      cases hone : one z with
      | none =>
          simp [oneWithDelta, hact, hone] at hz
      | some z1 =>
          have hpair :
              (z1, if rightward then (1 : Int) else -1) = (z', d) := by
            have hsome :
                some (z1, if rightward then (1 : Int) else -1) = some (z', d) := by
              simpa [oneWithDelta, hact, hone] using hz
            exact Option.some.inj hsome
          have hdelta : (if rightward then (1 : Int) else -1) = d :=
            congrArg Prod.snd hpair
          have hz1 : z1 = z' := congrArg Prod.fst hpair
          subst z'
          obtain ⟨c', hraw', hrep'⟩ :=
            sim_one z c ⟨hstate, hcur, hleft, hright⟩ z1 hone
          cases hmove : BB429PhysicalFrontier.target429 (readSlot c) with
          | none =>
              have hsourceNone : action z.state z.current = none := by
                simpa [hmove] using hsource
              simp [hact] at hsourceNone
          | some move =>
              have htrip :
                  (s, w, rightward) =
                    (move.next.val, move.write, move.right) := by
                have hsome :
                    some (s, w, rightward) =
                      some (move.next.val, move.write, move.right) := by
                  simpa [hact, hmove] using hsource
                exact Option.some.inj hsome
              rcases htrip with ⟨rfl, rfl, rfl⟩
              have hraw : rawStep BB429PhysicalFrontier.target429 c =
                  some (applyMove c move) := by
                simp [rawStep, hmove]
              have heq : c' = applyMove c move :=
                Option.some.inj (hraw'.symm.trans hraw)
              subst c'
              refine ⟨applyMove c move, hraw, hrep', ?_⟩
              simp [applyMove, hdelta]

/-- Generic displacement bridge: any successful `runWithDelta` zipper trace
    lifts to the actual raw `target429` interpreter, preserving the full
    tape representation and adding exactly the same signed head displacement. -/
theorem source_runWithDelta_rep (n : Nat) (z : Zipper) (c : Config)
    (hrep : Represents z c) (z' : Zipper) (d : Int)
    (hz : runWithDelta n z = some (z', d)) :
    ∃ c', BB6Coverage.run BB429PhysicalFrontier.target429 n c = some c' ∧
      Represents z' c' ∧ c'.head = c.head + d := by
  induction n generalizing z c z' d with
  | zero =>
      have hpair : (z, (0 : Int)) = (z', d) := by
        exact Option.some.inj (by simpa [runWithDelta] using hz)
      have hz' : z = z' := congrArg Prod.fst hpair
      have hd : (0 : Int) = d := congrArg Prod.snd hpair
      subst z'
      subst d
      exact ⟨c, by simp [BB6Coverage.run], hrep, by simp⟩
  | succ n ih =>
      cases hstep : oneWithDelta z with
      | none =>
          simp [runWithDelta, hstep] at hz
      | some p =>
          rcases p with ⟨z1, d1⟩
          have hmap :
              (runWithDelta n z1).map
                (fun q => (q.1, d1 + q.2)) = some (z', d) := by
            simpa [runWithDelta, hstep] using hz
          cases htail : runWithDelta n z1 with
          | none =>
              simp [htail] at hmap
          | some q =>
              rcases q with ⟨z2, d2⟩
              have hpair : (z2, d1 + d2) = (z', d) :=
                Option.some.inj (by simpa [htail] using hmap)
              have hz2 : z2 = z' := congrArg Prod.fst hpair
              have hd : d1 + d2 = d := congrArg Prod.snd hpair
              obtain ⟨c1, hraw1, hrep1, hhead1⟩ :=
                sim_one_delta z c hrep z1 d1 hstep
              obtain ⟨c2, hraw2, hrep2, hhead2⟩ :=
                ih z1 c1 hrep1 z2 d2 htail
              have hrepFinal : Represents z' c2 := by
                simpa [hz2] using hrep2
              refine ⟨c2, ?_, hrepFinal, ?_⟩
              · rw [BB429PhysicalBridge.physical_run_succ BB429PhysicalFrontier.target429 n c, hraw1]
                simpa using hraw2
              · calc
                  c2.head = c1.head + d2 := hhead2
                  _ = (c.head + d1) + d2 := by rw [hhead1]
                  _ = c.head + (d1 + d2) := by omega
                  _ = c.head + d := by rw [hd]

/-- The exact raw physical version of the source `sourceScanE` return:
    after its initial E/1 instruction and the complete excursion, the head
    is back at its starting coordinate. -/
theorem physical_sourceScanE_e1_revisit (b : Nat) (suffix : List Bool)
    (c : Config)
    (hrep : Represents (sourceScanE b suffix) c) :
    ∃ c', BB6Coverage.run BB429PhysicalFrontier.target429 (crossTime b + 1) c = some c' ∧
      Represents (z 2 (finalLeft b) true suffix) c' ∧
      c'.head = c.head := by
  simpa using source_runWithDelta_rep (crossTime b + 1)
    (sourceScanE b suffix) c hrep
    (z 2 (finalLeft b) true suffix) 0
    (sourceScanE_e1_revisit_delta b suffix)

/-- Reuse the generic bridge for every prefix of the E/1 shift. -/
theorem physical_shift_E11_prefix_via_delta
    (n j : Nat) (tail suffix : List Bool) (c : Config)
    (hrep : Represents (z 4 (ones n ++ tail) true (ones 6 ++ suffix)) c)
    (hj : j ≤ n) :
    ∃ c', BB6Coverage.run BB429PhysicalFrontier.target429 j c = some c' ∧
      Represents (z 4 (ones (n-j) ++ tail) true (ones (j+6) ++ suffix)) c' ∧
      c'.head = c.head - (j : Int) := by
  exact source_runWithDelta_rep j
    (z 4 (ones n ++ tail) true (ones 6 ++ suffix)) c hrep
    (z 4 (ones (n-j) ++ tail) true (ones (j+6) ++ suffix))
    (-(j : Int)) (e1_left_prefix n j tail suffix hj)


/-- A represented source run that returns none lifts to an exact raw-table
    halt. This is the converse-side companion to source_runWithDelta_rep. -/
theorem source_runWithDelta_none_rep (n : Nat) (z : Zipper) (c : Config)
    (hrep : Represents z c) (hz : runWithDelta n z = none) :
    BB6Coverage.run BB429PhysicalFrontier.target429 n c = none := by
  induction n generalizing z c with
  | zero =>
      simp [runWithDelta] at hz
  | succ n ih =>
      cases hstep : oneWithDelta z with
      | none =>
          rcases hrep with ⟨hstate,hcur,_,_⟩
          have hsource : action z.state z.current =
              (BB429PhysicalFrontier.target429 (readSlot c)).map
                (fun move => (move.next.val,move.write,move.right)) := by
            have h0 := BB429SourceRows.action_matches_target c.state (c.tape c.head)
            simp only [readSlot]
            rw [← hstate, ← hcur]
            exact h0
          have hact : action z.state z.current = none := by
            cases h : action z.state z.current with
            | none => rfl
            | some a =>
                exfalso
                rcases a with ⟨s,w,r⟩
                cases r <;> cases hright' : z.right <;> cases hleft' : z.left <;>
                  simp [oneWithDelta,one,h,hright',hleft'] at hstep
          have hmove : BB429PhysicalFrontier.target429 (readSlot c) = none := by
            cases h : BB429PhysicalFrontier.target429 (readSlot c) with
            | none => rfl
            | some move =>
                have hm : action z.state z.current =
                    some (move.next.val,move.write,move.right) := by
                  simpa [h] using hsource
                rw [hact] at hm
                cases hm
          have hraw : rawStep BB429PhysicalFrontier.target429 c = none := by
            simp [rawStep,hmove]
          rw [BB429PhysicalBridge.physical_run_succ
            BB429PhysicalFrontier.target429 n c, hraw]
          rfl
      | some p =>
          rcases p with ⟨z1,d1⟩
          obtain ⟨c1,hraw1,hrep1,hhead1⟩ :=
            sim_one_delta z c hrep z1 d1 hstep
          have htail : runWithDelta n z1 = none := by
            cases htail : runWithDelta n z1 with
            | none => rfl
            | some q => simp [runWithDelta,hstep,htail] at hz
          have hrawtail := ih z1 c1 hrep1 htail
          rw [BB429PhysicalBridge.physical_run_succ
            BB429PhysicalFrontier.target429 n c, hraw1]
          simpa [hrawtail]

#print axioms source_runWithDelta_none_rep

#print axioms sim_one_delta
#print axioms source_runWithDelta_rep
#print axioms physical_sourceScanE_e1_revisit
#print axioms physical_shift_E11_prefix_via_delta

end BB429DeltaPhysicalBridge
