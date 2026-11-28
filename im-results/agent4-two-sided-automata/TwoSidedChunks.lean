import TwoSidedAutomata
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent4Chunks
open BB6.Agent1NGram

/-- The low-bit-prefix subtree selecting indices congruent to r modulo 2^d. -/
def subtree : Nat → Nat → Trie → Trie
  | 0, _r, t => if _r = 0 then t else .empty
  | _+1, r, .empty => .empty
  | _+1, r, .leaf => if r = 0 then .leaf else .empty
  | d+1, r, .branch e o =>
      if r % 2 = 0 then subtree d (r/2) e else subtree d (r/2) o

@[simp] theorem subtree_zero (t : Trie) : subtree 0 0 t = t := by rfl

/-- Reassemble a Trie.all proof from all low-bit residue subtrees at a fixed depth. -/
theorem Trie.all_of_subtrees (t : Trie) (f : Nat → Bool) (d : Nat)
    (h : ∀ r, r < 2^d → (subtree d r t).all (fun i => f (2^d * i + r)) = true) :
    t.all f = true := by
  induction d generalizing t f with
  | zero =>
      have h0 := h 0 (by decide)
      simpa [subtree] using h0
  | succ d ih =>
      cases t with
      | empty => rfl
      | leaf =>
          have h0 := h 0 (Nat.pow_pos (by decide))
          simpa [subtree, Trie.all] using h0
      | branch e o =>
          simp only [Trie.all, Bool.and_eq_true]
          constructor
          · apply ih e (fun i => f (2*i))
            intro r hr
            have hh := h (2*r) (by rw [Nat.pow_succ]; omega)
            simp [subtree] at hh
            simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_add, Nat.add_assoc,
              Nat.mul_comm, Nat.mul_left_comm] using hh
          · apply ih o (fun i => f (2*i+1))
            intro r hr
            have hh := h (2*r+1) (by rw [Nat.pow_succ]; omega)
            simp [subtree] at hh
            have hdiv : (2*r+1)/2 = r := by omega
            rw [hdiv] at hh
            simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_add, Nat.add_assoc,
              Nat.mul_comm, Nat.mul_left_comm] using hh

open BB6Coverage
open BB6.Agent4Automata

def rowOK (p : PartialMachine) (c : BB6.Agent4Automata.Cert) (q : Fin 6) (a : Bool) : Bool :=
  (BB6.Agent4Automata.row c q a).all (fun i =>
    BB6.Agent4Automata.stateStepOK p c q a
      (i/c.right.edges.size) (i%c.right.edges.size))

/-- Fixed 6-state/2-symbol row conjunction, arranged like List.all over finRange 6. -/
def rows12 (p : PartialMachine) (c : BB6.Agent4Automata.Cert) : Bool :=
  (rowOK p c 0 false && rowOK p c 0 true) &&
  ((rowOK p c 1 false && rowOK p c 1 true) &&
  ((rowOK p c 2 false && rowOK p c 2 true) &&
  ((rowOK p c 3 false && rowOK p c 3 true) &&
  ((rowOK p c 4 false && rowOK p c 4 true) &&
   (rowOK p c 5 false && rowOK p c 5 true)))))

theorem rows12_all {p : PartialMachine} {c : BB6.Agent4Automata.Cert}
    (h : rows12 p c = true) :
    (List.finRange 6).all (fun q => BB6.Agent1NGram.bits.all (fun a => rowOK p c q a)) = true := by
  simpa [rows12, rowOK, BB6.Agent1NGram.bits, List.finRange] using h

/-- Assemble the original checker from a small base proof plus the 12 independent row proofs. -/
theorem check_of_rows12 {p : PartialMachine} {c : BB6.Agent4Automata.Cert}
    (hbase : 0 < c.left.edges.size ∧ 0 < c.right.edges.size ∧
      (c.left.pop 0).contains (false,0) = true ∧
      (c.right.pop 0).contains (false,0) = true ∧
      BB6.Agent4Automata.stateOK c 0 false 0 0 = true)
    (hrows : rows12 p c = true) : BB6.Agent4Automata.check p c = true := by
  have ha := rows12_all hrows
  simp only [BB6.Agent4Automata.check, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · exact ⟨⟨⟨⟨hbase.1, hbase.2.1⟩, hbase.2.2.1⟩, hbase.2.2.2.1⟩,
      hbase.2.2.2.2⟩
  · exact ha

end BB6.Agent4Chunks
