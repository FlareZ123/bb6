import RegularRayInvariant
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29FastRegularRay
open BB6Coverage BB6.Agent29RegularRay

/-- Superset predecessor table. A linear check on the DFA transition table
    verifies all incoming edges once, instead of rescanning them for each
    reachable pair. Extra predecessors only strengthen the closure check. -/
structure PredTable where
  rows : Array (List Nat × List Nat)

def PredTable.get (P : PredTable) (s : Nat) (b : Bool) : List Nat :=
  let ab := P.rows[s]?.getD ([],[])
  if b then ab.2 else ab.1

def PredTable.valid (P : PredTable) (d : RayDFA) : Bool :=
  (P.get 0 false).contains 0 && (List.range d.trans.size).all (fun s =>
    (P.get (d.push s false) false).contains s &&
    (P.get (d.push s true) true).contains s)

theorem PredTable.includes (P : PredTable) (d : RayDFA) (h : P.valid d = true)
    (s : Nat) (b : Bool) (i : Nat) (hi : i ∈ d.pred s b) : i ∈ P.get s b := by
  simp only [PredTable.valid,Bool.and_eq_true] at h
  unfold RayDFA.pred at hi
  rcases List.mem_append.mp hi with h0 | h1
  · by_cases he : (s == 0 && !b) = true
    · simp only [he,ite_true,List.mem_singleton] at h0
      have he' : s = 0 ∧ b = false := by simpa using he
      clear he
      rcases he' with ⟨rfl,rfl⟩
      subst i
      exact List.contains_iff_mem.mp h.1
    · have hf : (s == 0 && !b) = false := Bool.eq_false_iff.mpr he
      simp [hf] at h0
  · simp only [List.mem_filter,List.mem_range,beq_iff_eq] at h1
    have hs := List.all_eq_true.mp h.2 i (List.mem_range.mpr h1.1)
    simp only [Bool.and_eq_true] at hs
    rw [← h1.2]
    cases b
    · exact List.contains_iff_mem.mp hs.1
    · exact List.contains_iff_mem.mp hs.2

structure Certificate where
  base : BB6.Agent29RegularRay.Certificate
  leftPred : PredTable
  rightPred : PredTable

def Certificate.closedAt (c : Certificate) (p : PartialMachine) (q : Fin 6) (l r : Nat) : Bool :=
  [false,true].all fun a => (c.leftPred.get l a).all fun ll =>
    match p (q,a) with
    | some (some mv) =>
      if mv.right then
        [false,true].all fun b => (c.rightPred.get r b).all fun rr =>
          c.base.mem mv.next (c.base.left.push (c.base.left.push ll mv.write) b) rr
      else c.base.mem mv.next ll (c.base.right.push r mv.write)
    | _ => false

def Certificate.check (c : Certificate) (p : PartialMachine) : Bool :=
  c.base.left.valid && c.base.right.valid &&
  c.leftPred.valid c.base.left && c.rightPred.valid c.base.right && c.base.mem 0 0 0 &&
    (List.finRange 6).all (fun q => (List.range c.base.left.trans.size).all (fun l =>
      (c.base.row q l).all (fun r => c.closedAt p q l r)))

theorem Certificate.closedAt_sound (c : Certificate) (p : PartialMachine)
    (hl : c.leftPred.valid c.base.left = true) (hr : c.rightPred.valid c.base.right = true)
    (q : Fin 6) (l r : Nat) (h : c.closedAt p q l r = true) : c.base.closedAt p q l r = true := by
  unfold BB6.Agent29RegularRay.Certificate.closedAt Certificate.closedAt at *
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro ll hll
  have hh := List.all_eq_true.mp (List.all_eq_true.mp h a ha) ll (c.leftPred.includes c.base.left hl l a ll hll)
  cases hp : p (q,a) with
  | none => simpa [hp] using hh
  | some tr =>
    cases tr with
    | none => simpa [hp] using hh
    | some mv =>
      cases hd : mv.right with
      | false => simpa [hp,hd] using hh
      | true =>
        simp only [hp,hd,ite_true] at hh ⊢
        apply List.all_eq_true.mpr
        intro b hb
        apply List.all_eq_true.mpr
        intro rr hrr
        exact List.all_eq_true.mp (List.all_eq_true.mp hh b hb) rr (c.rightPred.includes c.base.right hr r b rr hrr)

theorem Certificate.sound (c : Certificate) (p : PartialMachine) (h : c.check p = true) :
    ∀ m, compatible p m → NeverHalts m := by
  simp only [Certificate.check,Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hl,hr⟩,hpl⟩,hpr⟩,h0⟩,hc⟩ := h
  apply c.base.sound p
  simp only [BB6.Agent29RegularRay.Certificate.check,Bool.and_eq_true]
  refine ⟨⟨⟨hl,hr⟩,h0⟩,?_⟩
  apply List.all_eq_true.mpr
  intro q hq
  apply List.all_eq_true.mpr
  intro l hl
  apply List.all_eq_true.mpr
  intro r hr
  exact c.closedAt_sound p hpl hpr q l r (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hc q hq) l hl) r hr)
#print axioms Certificate.sound
end BB6.Agent29FastRegularRay
