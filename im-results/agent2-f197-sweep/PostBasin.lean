import SelfTheorem

namespace F197.Agent2Self
open Agent2Counter
open Agent2EpochMarker (pre_append)

/-- A finite exact path into an all-time live stream is itself live at all
    finite times, including times before the endpoint. -/
theorem nohalt_of_reach {a b : Config}
    (h : Reach a b) (hb : ∀ t, run t b ≠ none) :
    ∀ t, run t a ≠ none := by
  obtain ⟨k,hk⟩ := h
  intro t ht
  have hp : run (k+t) a ≠ none := by
    rw [run_add,hk]
    exact hb t
  have hnone : run (k+t) a = none := by
    rw [Nat.add_comm,run_add,ht]
    rfl
  exact hp hnone

/-- The post-marker return has its *own* unbounded nonhalting basin,
    not just the particular 72-copy recurrent cylinder used by the original
    proof. Every 1-leading arbitrary infinite suffix works once the LB
    reservoir has 45 blocks, with no bound on the remaining exponent. -/
theorem post_basin_live (q : Nat) (tail : Tape)
    (hq : 45 ≤ q) (ht : tail 0 = true) :
    ∀ t, run t (state 0 OUT (rep LB q tail)) ≠ none := by
  let l : Tape := rep LB (q-45) tail
  have hl : l 0 = true := rep_first LB (by decide) _ tail ht
  have hzero : SelfPostN0 = 0 := by decide
  have hwzero : SelfPostW0 = OUT ++ flat LB 45 := by decide
  have he : rep LB q tail = rep LB 45 l := by
    dsimp [l]
    rw [← rep_add]
    congr 1
    omega
  have hsource :
      state 0 OUT (rep LB q tail) = state SelfPostN0 SelfPostW0 l := by
    rw [hzero,hwzero]
    change b (pre OUT (rep LB q tail)) e =
      b (pre OUT (rep LB 45 l)) e
    rw [he]
  have hendN : SelfPostN256 = 72 := by decide
  have hendW : SelfPostW256 = START ++ newSuffix := by decide
  have hend :
      state SelfPostN256 SelfPostW256 l = state 72 START (pre newSuffix l) := by
    rw [hendN,hendW]
    simp only [state,pre_append]
  have hnew : (pre newSuffix l) 0 = true := by rfl
  obtain ⟨k,_,hk⟩ := SelfPostTrace l hl
  have hreach :
      Reach (state 0 OUT (rep LB q tail)) (state 72 START (pre newSuffix l)) := by
    refine ⟨k, ?_⟩
    rw [hsource]
    rw [← hend]
    exact hk
  exact nohalt_of_reach hreach (self_nonhalt (pre newSuffix l) hnew)

#print axioms post_basin_live
end F197.Agent2Self
