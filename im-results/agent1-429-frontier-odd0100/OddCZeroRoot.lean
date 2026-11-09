import OddCZeroPhysical
import Lean.Elab.Tactic.Omega

namespace BB429OddCZeroRoot

open BB6Coverage BB429PhysicalFrontier BB429PhysicalBridge
open BB429OddExcursion BB429CZeroEvenReturn BB429OddCZeroPhysical

private theorem physical_run_add (m n : Nat) (c : Config) :
    BB6Coverage.run target429 (m+n) c =
    (BB6Coverage.run target429 m c).bind (BB6Coverage.run target429 n) := by
  induction n with
  | zero =>
      simp only [Nat.add_zero]
      change (BB6Coverage.run target429 m c) =
        (BB6Coverage.run target429 m c).bind (fun d => some d)
      cases BB6Coverage.run target429 m c <;> rfl
  | succ n ih =>
      rw [Nat.add_succ]
      change ((BB6Coverage.run target429 (m+n) c).bind (rawStep target429)) =
        (BB6Coverage.run target429 m c).bind
          (fun d => (BB6Coverage.run target429 n d).bind (rawStep target429))
      rw [ih,Option.bind_assoc]

/-- Authentic blank-root odd-parity C/0 section. Every actual blank-run
    encounter with a finite odd marked left run followed by zero and an
    all-zero right tape reaches an exact E/1 configuration, with its unknown
    distant left context intact; all primitive intermediate heads lie
    at most one cell to the right of the entry head. -/
theorem blank_odd_C0_to_E1_corridor (n m : Nat) (tail : List Bool) (c : Config)
    (hroot : BB6Coverage.run target429 n BB6Coverage.blank = some c)
    (hrep : Represents (z 2 (ones (2*m+1) ++ (false :: tail)) false []) c) :
    ∃ d, BB6Coverage.run target429 (n+2*m+6) BB6Coverage.blank = some d ∧
      Represents (z 4 tail true (true :: tens m ++ [false,true])) d ∧
      d.head = c.head - ((2*m+2:Nat):Int) ∧
      (∀ t (p : Config), n ≤ t → t ≤ n+2*m+6 →
        BB6Coverage.run target429 t BB6Coverage.blank = some p →
        p.head ≤ c.head + 1) := by
  obtain ⟨d,hsegment,hrep',hhead⟩ :=
    physical_odd_C0_to_E1 m tail c hrep
  refine ⟨d,?_,hrep',hhead,?_⟩
  · rw [show n+2*m+6=n+(2*m+6) by omega,
      physical_run_add,hroot]
    exact hsegment
  · intro t p hle hge hp
    have ht : t = n+(t-n) := by omega
    have hremain : t-n ≤ 2*m+6 := by omega
    obtain ⟨q,hq,hqbound⟩ :=
      physical_odd_C0_to_E1_prefix_bound m (t-n) tail c hrep hremain
    have hqp : BB6Coverage.run target429 t BB6Coverage.blank = some q := by
      rw [ht,physical_run_add,hroot]
      exact hq
    have heq : q=p := Option.some.inj (hqp.symm.trans hp)
    subst p
    omega

#print axioms blank_odd_C0_to_E1_corridor
end BB429OddCZeroRoot
