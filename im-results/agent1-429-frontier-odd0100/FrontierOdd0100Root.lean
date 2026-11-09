import FrontierOdd0100Physical
import CZeroHeadPrefix
import Lean.Elab.Tactic.Omega

namespace BB429Odd0100Root

open BB6Coverage BB429PhysicalFrontier BB429PhysicalBridge
open BB429OddExcursion BB429CZeroEvenReturn
open BB429Odd0100Physical

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

/-- At every genuine blank-root right-record C/0 whose complete tape has
    left shape 1^(2m)10100 gamma and blank right suffix, the NEXT C/0 section
    ends at the NEW global right head record +3; every primitive instruction
    of the section remains at or before that new record. The hypothesis is
    an authentic root condition, not a claim that every root entry has the
    stated finite chart. -/
theorem authentic_odd_0100_record_extension (n m : Nat) (tail : List Bool)
    (c : Config)
    (hroot : BB6Coverage.run target429 n BB6Coverage.blank = some c)
    (hrep : Represents
      (z 2 (ones (2*m) ++ [true,false,true,false,false] ++ tail) false []) c)
    (hprior : ∀ t (d : Config), t ≤ n →
      BB6Coverage.run target429 t BB6Coverage.blank = some d →
      d.head ≤ c.head) :
    ∃ d, BB6Coverage.run target429 (n+4*m+21) BB6Coverage.blank = some d ∧
      Represents (z 2 ([true,false] ++ ones (2*m+6) ++ tail) false []) d ∧
      d.head = c.head + 3 ∧
      (∀ t (p : Config), t ≤ n+4*m+21 →
        BB6Coverage.run target429 t BB6Coverage.blank = some p →
        p.head ≤ d.head) := by
  obtain ⟨d,hsegment,hrep',hhead⟩ :=
    physical_odd_0100_return m tail c hrep
  refine ⟨d,?_,hrep',hhead,?_⟩
  · rw [show n+4*m+21=n+(4*m+21) by omega,
      physical_run_add,hroot]
    exact hsegment
  · intro t p ht hp
    by_cases hle : t ≤ n
    · have h := hprior t p hle hp
      omega
    · have hsplit : t = n+(t-n) := by omega
      have hremain : t-n ≤ 4*m+21 := by omega
      obtain ⟨q,hq,hqbound⟩ :=
        physical_odd_0100_all_prefix_bound m (t-n) tail c hrep hremain
      have hqp : BB6Coverage.run target429 t BB6Coverage.blank = some q := by
        rw [hsplit,physical_run_add,hroot]
        exact hq
      have heq : q=p := Option.some.inj (hqp.symm.trans hp)
      subst p
      omega

#print axioms authentic_odd_0100_record_extension
end BB429Odd0100Root
