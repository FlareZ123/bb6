import BubblePrefix
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429HeadDisplacement

open BB6Coverage BB6Bubble

/-- Every successful original-table step moves the physical head by exactly
    one cell, in one of the two directions. -/
theorem rawStep_head_displacement (m : Machine) (c c' : Config)
    (h : rawStep m c = some c') :
    c'.head - c.head = 1 ∨ c'.head - c.head = -1 := by
  unfold rawStep at h
  cases hm : m (readSlot c) with
  | none => simp [hm] at h
  | some mv =>
      have hc : c' = applyMove c mv := by
        simpa [hm] using h
      subst c'
      simp [applyMove]
      cases mv.right <;> simp

/-- A successful n-step physical run cannot move its head by more than n
    cells in either direction. -/
theorem run_head_displacement_bound (m : Machine) (n : Nat)
    (c c' : Config) (h : run m n c = some c') :
    -(n : Int) ≤ c'.head - c.head ∧ c'.head - c.head ≤ n := by
  induction n generalizing c c' with
  | zero =>
      simp only [BB6Coverage.run, Option.some.injEq] at h
      subst c'
      constructor <;> simp
  | succ n ih =>
      simp only [BB6Coverage.run] at h
      cases hr : rawStep m c with
      | none => simp [hr] at h
      | some d =>
          simp only [hr, Option.bind_some] at h
          cases ht : run m n d with
          | none => simp [ht] at h
          | some e =>
              have he : e = c' := by simpa [ht] using h
              subst c'
              have hstep := rawStep_head_displacement m c d hr
              have htail := ih d e ht
              rcases hstep with hstep | hstep <;> constructor <;> omega

/-- Every prefix of a successful run is itself successful. -/
theorem run_prefix_exists (m : Machine) (n t : Nat) (c e : Config)
    (hfull : run m n c = some e) (ht : t ≤ n) :
    ∃ d, run m t c = some d := by
  have hlen : n = t + (n-t) := by omega
  have hcomp := run_add' m t (n-t) c
  rw [hlen, hcomp] at hfull
  cases hpre : run m t c with
  | none => simp [hpre] at hfull
  | some d => exact ⟨d, hpre⟩

/-- If an n-step run moves exactly n cells left, every successful prefix
    moves exactly its own length left. -/
theorem run_prefix_left_extremal (m : Machine) (n t : Nat)
    (c d e : Config)
    (hfull : run m n c = some e)
    (hprefix : run m t c = some d)
    (ht : t ≤ n)
    (hdisp : e.head - c.head = -(n : Int)) :
    d.head - c.head = -(t : Int) := by
  have hlen : n = t + (n-t) := by omega
  have hcomp := run_add' m t (n-t) c
  rw [hlen, hcomp, hprefix] at hfull
  simp only [Option.bind_some] at hfull
  have hsuffix : run m (n-t) d = some e := hfull
  have hpreBound := run_head_displacement_bound m t c d hprefix
  have hsufBound := run_head_displacement_bound m (n-t) d e hsuffix
  omega

/-- If an n-step run moves exactly n cells right, every successful prefix
    moves exactly its own length right. -/
theorem run_prefix_right_extremal (m : Machine) (n t : Nat)
    (c d e : Config)
    (hfull : run m n c = some e)
    (hprefix : run m t c = some d)
    (ht : t ≤ n)
    (hdisp : e.head - c.head = (n : Int)) :
    d.head - c.head = (t : Int) := by
  have hlen : n = t + (n-t) := by omega
  have hcomp := run_add' m t (n-t) c
  rw [hlen, hcomp, hprefix] at hfull
  simp only [Option.bind_some] at hfull
  have hsuffix : run m (n-t) d = some e := hfull
  have hpreBound := run_head_displacement_bound m t c d hprefix
  have hsufBound := run_head_displacement_bound m (n-t) d e hsuffix
  omega

/-- A bubble macro consists of a 2q-step extremal left sweep followed by
    2(q+1) steps. If its complete endpoint is two cells right of its start,
    every primitive prefix stays at or left of that endpoint. -/
theorem bubble_macro_prefix_head_bound (m : Machine) (q t : Nat)
    (c c1 c2 d : Config)
    (hAF : run m (2*q) c = some c1)
    (hAFhead : c1.head = c.head - 2*q)
    (hfull : run m (4*q+2) c = some c2)
    (hfullhead : c2.head = c.head + 2)
    (ht : t ≤ 4*q+2)
    (hprefix : run m t c = some d) :
    d.head ≤ c.head + 2 := by
  by_cases hsmall : t ≤ 2*q
  · have hdisp : c1.head - c.head = -(2*q : Int) := by
      rw [hAFhead]
      omega
    have hleft := run_prefix_left_extremal m (2*q) t c d c1
      hAF hprefix hsmall hdisp
    omega
  · let s : Nat := t - 2*q
    have htime : t = 2*q+s := by
      dsimp [s]
      omega
    have hs : s ≤ 2*(q+1) := by
      dsimp [s]
      omega
    have htailFull : run m (2*(q+1)) c1 = some c2 := by
      have hcomp := run_add' m (2*q) (2*(q+1)) c
      have hlen : 2*q + 2*(q+1) = 4*q+2 := by omega
      rw [← hlen] at hfull
      rw [hcomp, hAF] at hfull
      simpa using hfull
    have htailPrefix : run m s c1 = some d := by
      have hcomp := run_add' m (2*q) s c
      rw [htime, hcomp, hAF] at hprefix
      simpa using hprefix
    have hdisp : c2.head - c1.head = (2*(q+1) : Nat) := by
      rw [hAFhead, hfullhead]
      omega
    have hright := run_prefix_right_extremal m (2*(q+1)) s c1 d c2
      htailFull htailPrefix hs hdisp
    rw [hAFhead] at hright
    omega

#print axioms rawStep_head_displacement
#print axioms run_head_displacement_bound
#print axioms run_prefix_exists
#print axioms run_prefix_left_extremal
#print axioms run_prefix_right_extremal
#print axioms bubble_macro_prefix_head_bound

end BB429HeadDisplacement
