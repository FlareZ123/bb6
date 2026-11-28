import SweepPumping
import SparseBlankDelay

namespace BB6.Agent7Run0LastHole
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper BB6.Agent13BlankDelay

/-- A projected live prefix is a live raw prefix ending at the same slot. -/
theorem reached_raw (p : PartialMachine) (n : Nat) (z : Z0)
    (hr : run0 p n ⟨0,[],[]⟩ = some z) (m : Machine) (hm : compatible p m) :
    ∃ c, run m n blank = some c ∧ readSlot c = (z.q,z.l.headD false) := by
  have hp : (zrun p n start).map project = some z := (run_project p n start).trans hr
  cases hz : zrun p n start with
  | none => simp [hz] at hp
  | some u =>
    have he : project u = z := by simpa [hz] using hp
    refine ⟨embed u, ?_, ?_⟩
    · have h := zrun_sound p m hm n start u hz
      rwa [start_embed] at h
    · rw [read_embed, ← he]
      rfl

/-- If the only unassigned row is queried at n, any halting completion
    must halt there. Every other completion is total and stays live. -/
theorem halter_exact (p : PartialMachine) (n : Nat) (z : Z0)
    (hr : run0 p n ⟨0,[],[]⟩ = some z)
    (hrest : ∀ s, s ≠ (z.q,z.l.headD false) → ∃ mv, p s = some (some mv))
    (m : Machine) (hm : compatible p m) (k : Nat) (hk : HaltsAfter m k) : k = n := by
  obtain ⟨c,hc,hs⟩ := reached_raw p n z hr m hm
  cases ht : m (z.q,z.l.headD false) with
  | none =>
    have hn : HaltsAfter m n := by
      constructor
      · simp [hc]
      · rw [run,hc]; simp only [Option.bind_some,rawStep,hs,ht,Option.map_none]
    exact halting_time_unique m k n hk hn
  | some mv =>
    have htotal : ∀ s, ∃ v, m s = some v := by
      intro s
      by_cases he : s = (z.q,z.l.headD false)
      · subst s; exact ⟨mv,ht⟩
      · obtain ⟨v,hv⟩ := hrest s he
        exact ⟨v,hm s _ hv⟩
    have hn : ∀ a, (run m a blank).isSome = true := by
      intro a
      induction a with
      | zero => rfl
      | succ a ih =>
        cases h : run m a blank with
        | none => simp [h] at ih
        | some c =>
          obtain ⟨v,hv⟩ := htotal (readSlot c)
          simp [run,h,rawStep,hv]
    have h := hn (k+1)
    rw [hk.2] at h
    contradiction

theorem bound (p : PartialMachine) (n B : Nat) (z : Z0)
    (hr : run0 p n ⟨0,[],[]⟩ = some z)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hrest : ∀ s, s ≠ (z.q,z.l.headD false) → ∃ mv, p s = some (some mv))
    (hslack : n+6 ≤ B) (m : Machine) (hm : compatible p m) : WeightedBound B m := by
  intro k d hk hd
  have he := halter_exact p n z hr hrest m hm k hk
  obtain ⟨s,hp⟩ := (mem_delays_iff (firstOne_terminal p hroot m hm)).mp hd
  have h5 := terminal_delay_le_five hp
  omega

#print axioms reached_raw
#print axioms halter_exact
#print axioms bound
end BB6.Agent7Run0LastHole
