import OddAlternatingPhysical
import Lean.Elab.Tactic.Omega

namespace BB429OddAlternatingRoot

open BB6Coverage BB429PhysicalFrontier BB429PhysicalBridge
open BB429OddExcursion BB429CZeroEvenReturn
open BB429OddAlternatingPhysical

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

/-- If a genuine blank-root C/0 global right record has the all-suffix
    odd-alternating chart, it is followed by a second genuine C/0 global
    right record exactly three cells farther right, with every intervening
    physical head at or before the new record. -/
theorem authentic_odd_alternating_record_extension
    (n m q : Nat) (tail : List Bool) (c : Config)
    (hroot : BB6Coverage.run target429 n BB6Coverage.blank = some c)
    (hrep : Represents
      (z 2 (ones (2*m+1) ++ [false] ++ tens (2*q+1) ++ [false] ++ tail)
        false []) c)
    (hprior : ∀ t (d : Config), t ≤ n →
      BB6Coverage.run target429 t BB6Coverage.blank = some d →
      d.head ≤ c.head) :
    ∃ d, BB6Coverage.run target429 (n+4*m+14*q+21)
        BB6Coverage.blank = some d ∧
      Represents
        (z 2 ([true,false] ++ ones (2*m+4*q+6) ++ tail)
          false []) d ∧
      d.head = c.head + 3 ∧
      (∀ t (p : Config), t ≤ n+4*m+14*q+21 →
        BB6Coverage.run target429 t BB6Coverage.blank = some p →
        p.head ≤ d.head) := by
  obtain ⟨d,hsegment,hrep',hhead⟩ :=
    physical_odd_alternating_return m q tail c hrep
  refine ⟨d,?_,hrep',hhead,?_⟩
  · rw [show n+4*m+14*q+21=n+(4*m+14*q+21) by omega,
      physical_run_add,hroot]
    exact hsegment
  · intro t p ht hp
    by_cases hle : t ≤ n
    · have h := hprior t p hle hp
      omega
    · have hsplit : t = n+(t-n) := by omega
      have hremain : t-n ≤ 4*m+14*q+21 := by omega
      obtain ⟨p',hp',hbound⟩ :=
        physical_odd_alternating_all_prefix_bound m q (t-n)
          tail c hrep hremain
      have hqp : BB6Coverage.run target429 t BB6Coverage.blank = some p' := by
        rw [hsplit,physical_run_add,hroot]
        exact hp'
      have heq : p'=p := Option.some.inj (hqp.symm.trans hp)
      subst p
      omega

#print axioms authentic_odd_alternating_record_extension

end BB429OddAlternatingRoot
