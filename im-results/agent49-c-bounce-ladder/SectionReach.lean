import SectionGateBridge
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent49
open BB6.Agent46 (secNext)
open BB6.Agent8Section (run)

abbrev Pair := Nat × Nat
inductive SecReach : Pair → Prop where
  | init : SecReach (5,1)
  | next (s t : Pair) : SecReach s → secNext s = some t → SecReach t

theorem run_reachable (n : Nat) (s : Pair) (h : run secNext n (some (5,1))=some s) :
    SecReach s := by
  induction n generalizing s with
  | zero =>
      have he : s=(5,1) := by simpa [run] using h.symm
      subst s
      exact SecReach.init
  | succ n ih =>
      change (run secNext n (some (5,1))).bind secNext = some s at h
      cases hh : run secNext n (some (5,1)) with
      | none => simp [hh] at h
      | some t =>
          have hr := ih t hh
          have he : secNext t = some s := by simpa [hh] using h
          exact SecReach.next t s hr he

theorem reachable_run (s : Pair) (h : SecReach s) :
    ∃ n : Nat, run secNext n (some (5,1))=some s := by
  induction h with
  | init => exact ⟨0,rfl⟩
  | next s t h ht ih =>
      obtain ⟨n,hn⟩ := ih
      refine ⟨n+1,?_⟩
      change (run secNext n (some (5,1))).bind secNext=some t
      rw [hn]
      exact ht

theorem section_halt_iff_reachable_gate :
    (∃ n : Nat, run secNext n (some (5,1)) = none) ↔
      (∃ s : Pair, SecReach s ∧ SectionGate s.1 s.2) := by
  constructor
  · rintro ⟨n,hn⟩
    induction n using Nat.strongRecOn with
    | ind n ih =>
        cases n with
        | zero => simp [run] at hn
        | succ n =>
            change (run secNext n (some (5,1))).bind secNext=none at hn
            cases hs : run secNext n (some (5,1)) with
            | none => exact ih n (by omega) hs
            | some s =>
                have hc : secNext s=none := by simpa [hs] using hn
                exact ⟨s,run_reachable n s hs,(source_section_gate_iff s.1 s.2).mp hc⟩
  · rintro ⟨s,hr,hgate⟩
    obtain ⟨n,hn⟩ := reachable_run s hr
    refine ⟨n+1,?_⟩
    change (run secNext n (some (5,1))).bind secNext=none
    rw [hn]
    exact (source_section_gate_iff s.1 s.2).mpr hgate

#print axioms section_halt_iff_reachable_gate
end BB6.Agent49
