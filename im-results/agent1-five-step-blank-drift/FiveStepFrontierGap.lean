import Std.Tactic
import FiveStepBlankFamily
import LassoTraceAudit

set_option maxRecDepth 16000
set_option maxHeartbeats 0

namespace BB6Coverage
namespace FiveStepBlankFamily

/-!
  Source-level exact depth-four old-frontier gap for all 1200 five-step
  translated-blank cylinders. The finite checks are original Lean
  lassoDecisionOracle/firstUnknownPhysical, not a JS simulator port.
  Compile and axiom-audit before any open-set/mass promotion.
-/

/-- Every legal parameter tuple has five old-oracle-negative proper
    prefixes, from emptyTable through the four-row E/0 parent. -/
theorem all_prefix_oracles :
    ∀ (b c d e : Fin 6) (right : Bool),
      b ≠ 0 → d ≠ c → e ≠ 0 → e ≠ b →
      lassoDecisionOracle emptyTable 6 6 12 2 4 = false ∧
      lassoDecisionOracle (p1 b right) 6 6 12 2 4 = false ∧
      lassoDecisionOracle (p2 b c right) 6 6 12 2 4 = false ∧
      lassoDecisionOracle (p3 b c d right) 6 6 12 2 4 = false ∧
      lassoDecisionOracle (p4 b c d e right) 6 6 12 2 4 = false := by
  let P : Fin 6 → Fin 6 → Fin 6 → Fin 6 → Bool → Prop :=
    fun b c d e right =>
        lassoDecisionOracle emptyTable 6 6 12 2 4 = false ∧
        lassoDecisionOracle (p1 b right) 6 6 12 2 4 = false ∧
        lassoDecisionOracle (p2 b c right) 6 6 12 2 4 = false ∧
        lassoDecisionOracle (p3 b c d right) 6 6 12 2 4 = false ∧
        lassoDecisionOracle (p4 b c d e right) 6 6 12 2 4 = false
  have hall :
      (List.finRange 6).all (fun (b : Fin 6) =>
        (List.finRange 6).all (fun (c : Fin 6) =>
          (List.finRange 6).all (fun (d : Fin 6) =>
            (List.finRange 6).all (fun (e : Fin 6) =>
              ([false, true] : List Bool).all (fun right =>
                decide (b ≠ 0 → d ≠ c → e ≠ 0 → e ≠ b → P b c d e right)))))) = true := by
    decide
  intro b c d e right hb hd he0 heb
  have h1 := (List.all_eq_true.mp hall) b (List.mem_finRange b)
  have h2 := (List.all_eq_true.mp h1) c (List.mem_finRange c)
  have h3 := (List.all_eq_true.mp h2) d (List.mem_finRange d)
  have h4 := (List.all_eq_true.mp h3) e (List.mem_finRange e)
  have hright : right ∈ ([false, true] : List Bool) := by
    cases right <;> decide
  have h5 := (List.all_eq_true.mp h4) right hright
  exact (of_decide_eq_true h5) hb hd he0 heb

/-- The exact physical first-unknown path reaches E/0 at depth four
    for every legal parameter tuple. -/
theorem all_prefix_unknowns :
    ∀ (b c d e : Fin 6) (right : Bool),
      b ≠ 0 → d ≠ c → e ≠ 0 → e ≠ b →
      firstUnknownPhysical emptyTable 12 finiteBlank = some a0 ∧
      firstUnknownPhysical (p1 b right) 12 finiteBlank = some (zeroSlot b) ∧
      firstUnknownPhysical (p2 b c right) 12 finiteBlank = some (oneSlot c) ∧
      firstUnknownPhysical (p3 b c d right) 12 finiteBlank = some (oneSlot d) ∧
      firstUnknownPhysical (p4 b c d e right) 12 finiteBlank = some (zeroSlot e) := by
  let P : Fin 6 → Fin 6 → Fin 6 → Fin 6 → Bool → Prop :=
    fun b c d e right =>
        firstUnknownPhysical emptyTable 12 finiteBlank = some a0 ∧
        firstUnknownPhysical (p1 b right) 12 finiteBlank = some (zeroSlot b) ∧
        firstUnknownPhysical (p2 b c right) 12 finiteBlank = some (oneSlot c) ∧
        firstUnknownPhysical (p3 b c d right) 12 finiteBlank = some (oneSlot d) ∧
        firstUnknownPhysical (p4 b c d e right) 12 finiteBlank = some (zeroSlot e)
  have hall :
      (List.finRange 6).all (fun (b : Fin 6) =>
        (List.finRange 6).all (fun (c : Fin 6) =>
          (List.finRange 6).all (fun (d : Fin 6) =>
            (List.finRange 6).all (fun (e : Fin 6) =>
              ([false, true] : List Bool).all (fun right =>
                decide (b ≠ 0 → d ≠ c → e ≠ 0 → e ≠ b → P b c d e right)))))) = true := by
    decide
  intro b c d e right hb hd he0 heb
  have h1 := (List.all_eq_true.mp hall) b (List.mem_finRange b)
  have h2 := (List.all_eq_true.mp h1) c (List.mem_finRange c)
  have h3 := (List.all_eq_true.mp h2) d (List.mem_finRange d)
  have h4 := (List.all_eq_true.mp h3) e (List.mem_finRange e)
  have hright : right ∈ ([false, true] : List Bool) := by
    cases right <;> decide
  have h5 := (List.all_eq_true.mp h4) right hright
  exact (of_decide_eq_true h5) hb hd he0 heb

private theorem open_step (p : PartialMachine) (depth : Nat)
    (s : Slot) (hf : lassoDecisionOracle p 6 6 12 2 4 = false)
    (hs : firstUnknownPhysical p 12 finiteBlank = some s)
    (m : Machine) :
    (lassoPhysicalTraceAudit p 6 6 12 12 2 4 (depth+1)).open m ↔
      (lassoPhysicalTraceAudit (refine p s (m s))
         6 6 12 12 2 4 depth).open m := by
  have hn : ¬ lassoDecisionOracle p 6 6 12 2 4 = true := by
    simp [hf]
  simp only [lassoPhysicalTraceAudit, dif_neg hn]
  split
  · rename_i hnone
    simp [hnone] at hs
  · rename_i actual hsome
    have heq : actual = s := Option.some.inj (hsome.symm.trans hs)
    subst actual
    rfl

/-- Every completion of each five-row translated-blank source cylinder
    is open in the exact depth-four lasso physical audit. No claim about
    an independent translated-oracle or a deeper audit is needed. -/
theorem all_members_open_depth4
    (b c d e : Fin 6) (right : Bool)
    (hb : b ≠ 0) (hd : d ≠ c) (he0 : e ≠ 0) (heb : e ≠ b)
    (m : Machine) (hm : compatible (table b c d e right) m) :
    (lassoPhysicalTraceAudit emptyTable 6 6 12 12 2 4 4).open m := by
  have hcd : c ≠ d := Ne.symm hd
  have hbe : b ≠ e := Ne.symm heb
  have h0b : (0 : Fin 6) ≠ b := Ne.symm hb
  have h0e : (0 : Fin 6) ≠ e := Ne.symm he0
  have hA : m a0 = act true right b :=
    hm a0 (act true right b) (by
      simp [table, p4, p3, p2, p1, refine, a0,
        zeroSlot, oneSlot, hb, h0b, hd, hcd, he0, h0e, heb, hbe])
  have hB : m (zeroSlot b) = act true (!right) c :=
    hm (zeroSlot b) (act true (!right) c) (by
      simp [table, p4, p3, p2, p1, refine, a0,
        zeroSlot, oneSlot, hb, h0b, hd, hcd, he0, h0e, heb, hbe])
  have hC : m (oneSlot c) = act false right d :=
    hm (oneSlot c) (act false right d) (by
      simp [table, p4, p3, p2, p1, refine, a0,
        zeroSlot, oneSlot, hb, h0b, hd, hcd, he0, h0e, heb, hbe])
  have hD : m (oneSlot d) = act false (!right) e :=
    hm (oneSlot d) (act false (!right) e) (by
      simp [table, p4, p3, p2, p1, refine, a0,
        zeroSlot, oneSlot, hb, h0b, hd, hcd, he0, h0e, heb, hbe])
  have ho := all_prefix_oracles b c d e right hb hd he0 heb
  have hu := all_prefix_unknowns b c d e right hb hd he0 heb
  have h4 :
      (lassoPhysicalTraceAudit (p4 b c d e right)
        6 6 12 12 2 4 0).open m := by
    simp [lassoPhysicalTraceAudit, ho.2.2.2.2, FrontierAudit.open]
  have h3 :
      (lassoPhysicalTraceAudit (p3 b c d right)
        6 6 12 12 2 4 1).open m := by
    have h4' :
        (lassoPhysicalTraceAudit
           (refine (p3 b c d right) (oneSlot d) (act false (!right) e))
           6 6 12 12 2 4 0).open m := by
      simpa [p4] using h4
    rw [← hD] at h4'
    exact (open_step (p3 b c d right) 0 (oneSlot d)
      ho.2.2.2.1 hu.2.2.2.1 m).2 h4'
  have h2 :
      (lassoPhysicalTraceAudit (p2 b c right)
        6 6 12 12 2 4 2).open m := by
    have h3' :
        (lassoPhysicalTraceAudit
           (refine (p2 b c right) (oneSlot c) (act false right d))
           6 6 12 12 2 4 1).open m := by
      simpa [p3] using h3
    rw [← hC] at h3'
    exact (open_step (p2 b c right) 1 (oneSlot c)
      ho.2.2.1 hu.2.2.1 m).2 h3'
  have h1 :
      (lassoPhysicalTraceAudit (p1 b right)
        6 6 12 12 2 4 3).open m := by
    have h2' :
        (lassoPhysicalTraceAudit
           (refine (p1 b right) (zeroSlot b) (act true (!right) c))
           6 6 12 12 2 4 2).open m := by
      simpa [p2] using h2
    rw [← hB] at h2'
    exact (open_step (p1 b right) 2 (zeroSlot b)
      ho.2.1 hu.2.1 m).2 h2'
  have h0 :
      (lassoPhysicalTraceAudit emptyTable
        6 6 12 12 2 4 4).open m := by
    have h1' :
        (lassoPhysicalTraceAudit
           (refine emptyTable a0 (act true right b))
           6 6 12 12 2 4 3).open m := by
      simpa [p1] using h1
    rw [← hA] at h1'
    exact (open_step emptyTable 3 a0 ho.1 hu.1 m).2 h1'
  exact h0

#print axioms all_prefix_oracles
#print axioms all_prefix_unknowns
#print axioms all_members_open_depth4

end FiveStepBlankFamily
end BB6Coverage
