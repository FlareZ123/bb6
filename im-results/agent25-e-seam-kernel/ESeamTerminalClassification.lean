import ESeamPhysicalBridge
import ESeamNoReturn

namespace BB6.PhysicalWindow.ESeam
open BB6.PhysicalWindow

/-- At every primitive time from every E_3 right tape, the only stopped
    events of the full physical refinement are a protected C/1 marker visit
    or the true F/1 halting gate. A premature F/0 return is impossible. -/
theorem terminal_classification (r : Nat) (remote : Nat → Bool)
    (hr : r < 128) (t : Nat)
    (ht : terminal (run t (seed r remote)) = true) :
    ((run t (seed r remote)).pos = 1 ∧
      (run t (seed r remote)).state = 2 ∧
      cell (run t (seed r remote)) 1 = true) ∨
    ((run t (seed r remote)).state = 5 ∧
      scanned (run t (seed r remote)) = 1) := by
  let c := run t (seed r remote)
  by_cases hm : c.pos = 1
  · left
    have hsafe := original_e_base_marker_safe r remote hr t hm
    exact ⟨hm, hsafe.1, hsafe.2⟩
  · right
    have hwf := wellformed_run (seed r remote) (seed_wellformed r remote hr) t
    have hp : 2 ≤ c.pos := by
      have h := hwf.2.2
      change 1 ≤ c.pos at h
      omega
    have hno := seed_no_F0_before_marker r remote hr t hp
    change (c.state == 5 && scanned c == 0 &&
      c.bits.land ((1 <<< c.pos) - 1) == 0) = false at hno
    have hm0 : (c.pos == 1) = false := by simp [hm]
    have hcases : (c.state = 5 ∧ scanned c = 1) ∨
        (((c.pos < 18 ∧ c.state = 5) ∧ scanned c = 0) ∧
          c.bits.land ((1 <<< c.pos) - 1) = 0) := by
      change terminal c = true at ht
      simpa [terminal, hm0] using ht
    have hhalt : (c.state == 5 && scanned c == 1) = true := by
      rcases hcases with ⟨hs, hb⟩ | ⟨⟨⟨_, hs⟩, hb⟩, hz⟩
      · simp [hs, hb]
      · have hx : (c.state == 5 && scanned c == 0 &&
            c.bits.land ((1 <<< c.pos) - 1) == 0) = true := by
          change (c.bits &&& ((1 <<< c.pos) - 1)) = 0 at hz
          simp [hs, hb, hz]
        rw [hno] at hx
        contradiction
    have hpairs := Bool.and_eq_true_iff.mp hhalt
    exact ⟨by simpa using hpairs.1, by simpa using hpairs.2⟩

#print axioms terminal_classification
end BB6.PhysicalWindow.ESeam
