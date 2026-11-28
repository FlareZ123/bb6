import SideCycle
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50GenericClosedGraph
open BB6Coverage

/-!
Reusable, tape-independent nonhalting criterion for any *partial*
six-state two-symbol machine p. The caller chooses a set S of states
whose every symbol-specific transition is specified, nonhalting and
returns to S. Any finite certified execution from blank to one state
of S then proves that every *total compatible completion* runs forever.

Unlike simulation-based loop detection, this criterion closes arbitrarily
complex tape evolutions, including binary counters, immediately once their
control states form a closed component.
-/
def Closed (p : PartialMachine) (S : Fin 6 → Prop) : Prop :=
  ∀ q b, S q →
    ∃ mv : Move, p (q,b) = some (some mv) ∧ S mv.next

theorem step (p : PartialMachine) (S : Fin 6 → Prop)
    (hclosed : Closed p S)
    (m : Machine) (hm : compatible p m)
    (c : Config) (hc : S c.state) :
    ∃ d, rawStep m c = some d ∧ S d.state := by
  obtain ⟨mv,hp,hn⟩ :=
    hclosed c.state (readSlot c).2 hc
  have hp' : p (readSlot c) = some (some mv) := by
    simpa [readSlot] using hp
  have hmv : m (readSlot c) = some mv :=
    hm (readSlot c) (some mv) hp'
  refine ⟨applyMove c mv, by simp [rawStep,hmv],?_⟩
  simpa [applyMove] using hn

theorem run_closed (p : PartialMachine) (S : Fin 6 → Prop)
    (hclosed : Closed p S)
    (m : Machine) (hm : compatible p m)
    (n : Nat) (c : Config) (hc : S c.state) :
    ∃ d, run m n c = some d ∧ S d.state := by
  induction n with
  | zero => exact ⟨c,rfl,hc⟩
  | succ n ih =>
    obtain ⟨d,hr,hd⟩ := ih
    obtain ⟨e,hs,he⟩ := step p S hclosed m hm d hd
    exact ⟨e,by simp [run,hr,hs],he⟩

theorem never_after
    (p : PartialMachine) (S : Fin 6 → Prop)
    (hclosed : Closed p S)
    (m : Machine) (hm : compatible p m)
    (k : Nat) (z : Config)
    (hprefix : run m k blank = some z)
    (hz : S z.state) : NeverHalts m := by
  intro n
  by_cases hn : n ≤ k
  · cases h : run m n blank with
    | some d => rfl
    | none =>
      have bad := run_none_add m blank n (k-n) h
      have heq : n+(k-n)=k := by omega
      rw [heq,hprefix] at bad
      contradiction
  · obtain ⟨d,hr,_⟩ :=
      run_closed p S hclosed m hm (n-k) z hz
    have heq : n=k+(n-k) := by omega
    have hreach : run m n blank = some d := by
      rw [heq,run_append,hprefix]
      exact hr
    simp [hreach]

#print axioms step
#print axioms run_closed
#print axioms never_after
end BB6.Agent50GenericClosedGraph
