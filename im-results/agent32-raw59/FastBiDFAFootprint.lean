import FastBiDFA

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32FastBiDFA.Footprint
open BB6Coverage
open BB6.Agent1NGram (Trie bits mem_bits mem_states)

/-- Converse of the existing trie checker soundness theorem. -/
theorem trie_all_complete {t : Trie} {f : Nat → Bool}
    (h : ∀ i, t.has i = true → f i = true) : t.all f = true := by
  induction t generalizing f with
  | empty => rfl
  | leaf => exact h 0 rfl
  | branch e o he ho =>
    simp only [Trie.all, Bool.and_eq_true]
    constructor
    · apply he
      intro i hi
      apply h (2*i)
      have hm : (2*i)%2 = 0 := by omega
      have hd : (2*i)/2 = i := by omega
      simpa only [Trie.has,hm,beq_self_eq_true,ite_true,hd] using hi
    · apply ho
      intro i hi
      apply h (2*i+1)
      have hm : ¬ (2*i+1)%2 = 0 := by omega
      have hd : (2*i+1)/2 = i := by omega
      simpa only [Trie.has,beq_iff_eq,hm,ite_false,hd] using hi

/-- Exactly the state-symbol rows containing at least one abstract configuration. -/
def used (c : Cert) (q : Fin 6) (a : Bool) : Bool :=
  !((List.range (rows c q a).size).all (fun l => (row c q a l).all (fun _ => false)))

theorem used_of_state {c q a l r} (hl : l < (rows c q a).size)
    (h : stateOK c q a l r = true) : used c q a = true := by
  unfold used
  cases he : (List.range (rows c q a).size).all (fun l => (row c q a l).all (fun _ => false)) with
  | false => rfl
  | true =>
    have hh := List.all_eq_true.mp he l (List.mem_range.mpr hl)
    have bad : false = true := Trie.all_sound hh h
    cases bad

theorem rowCheck_transport {p p' : PartialMachine} {c : Cert} {q : Fin 6} {a : Bool}
    (h : rowCheck p c q a = true)
    (agree : used c q a = true → p' (q,a) = p (q,a)) :
    rowCheck p' c q a = true := by
  apply List.all_eq_true.mpr
  intro l hl
  apply trie_all_complete
  intro r hr
  have hs : stateOK c q a l r = true := hr
  have hq := agree (used_of_state (List.mem_range.mp hl) hs)
  have hstep := Trie.all_sound (List.all_eq_true.mp h l hl) hr
  simpa only [stateStepOK,hq] using hstep

theorem check_transport {p p' : PartialMachine} {c : Cert}
    (h : check p c = true)
    (agree : ∀ q a, used c q a = true → p' (q,a) = p (q,a)) :
    check p' c = true := by
  simp only [check,Bool.and_eq_true,List.all_eq_true] at h
  exact check_of_rows h.1.1.1 h.1.1.2 h.1.2
    (fun q a => rowCheck_transport (h.2 q (mem_states q) a (mem_bits a)) (agree q a))

def restrict (p : PartialMachine) (c : Cert) : PartialMachine :=
  fun s => if used c s.1 s.2 then p s else none

theorem check_restrict {p c} (h : check p c = true) : check (restrict p c) c = true :=
  check_transport h (fun q a hu => by simp [restrict,hu])

theorem never_restrict (p : PartialMachine) (c : Cert) (hc : check p c = true)
    (m : Machine) (hm : compatible (restrict p c) m) : NeverHalts m :=
  BB6.Agent32FastBiDFA.never (restrict p c) c (check_restrict hc) m hm

#print axioms never_restrict
#print axioms trie_all_complete
#print axioms check_transport
#print axioms check_restrict
end BB6.Agent32FastBiDFA.Footprint
