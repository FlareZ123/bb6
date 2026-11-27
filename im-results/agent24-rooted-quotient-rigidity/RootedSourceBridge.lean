import RootedLiveQuotient
import Symmetry

namespace Agent24RootedSourceBridge
open BB6Coverage


/-- Translate original primitive moves without changing writing, direction or target. -/
def moveOf (t : BB6Coverage.Move) : RootedLiveQuotient.Move (Fin 6) :=
  ⟨t.write, t.right, t.next⟩

def moveTo (t : RootedLiveQuotient.Move (Fin 6)) : BB6Coverage.Move :=
  ⟨t.write, t.right, t.next⟩

theorem moveToOf (t : BB6Coverage.Move) : moveTo (moveOf t) = t := by cases t; rfl
theorem moveOfTo (t : RootedLiveQuotient.Move (Fin 6)) : moveOf (moveTo t) = t := by cases t; rfl

def partialOf (p : BB6Coverage.PartialMachine) : RootedLiveQuotient.PartialTable (Fin 6) :=
  fun s b => (p (s,b)).map (fun mt => mt.map moveOf)

def machineOf (m : BB6Coverage.Machine) : RootedLiveQuotient.Machine (Fin 6) :=
  fun s b => (m (s,b)).map moveOf

def permOf (e : BB6Coverage.StatePerm) : RootedLiveQuotient.Perm (Fin 6) where
  forward := e.forward
  backward := e.backward
  leftInverse := e.leftInverse
  rightInverse := e.rightInverse

-- A direct unification lemma: source renaming commutes with the encoding.
theorem machineOf_rename (m : BB6Coverage.Machine) (e : BB6Coverage.StatePerm)
    (s : Fin 6) (b : Bool) :
    machineOf (BB6Coverage.renameTable e m) s b =
      (machineOf m (e.backward s) b).map (RootedLiveQuotient.renameMove (permOf e)) := by
  unfold machineOf BB6Coverage.renameTable
  cases h : m (e.backward s,b) with
  | none => simp [h]
  | some mv =>
      cases mv
      rfl

-- Convert original source compatibility to self-contained source compatibility.
theorem sourceCompatible_iff (p : BB6Coverage.PartialMachine)
    (m : BB6Coverage.Machine) (e : BB6Coverage.StatePerm) :
    RootedLiveQuotient.SourceCompatible (partialOf p) (machineOf m) (permOf e) ↔
      BB6Coverage.compatible p (BB6Coverage.renameTable e m) := by
  constructor
  · intro h ⟨s,b⟩ out hs
    have h' := h s b (out.map moveOf) (by simpa [partialOf, hs])
    change (machineOf m (e.backward s) b).map
      (RootedLiveQuotient.renameMove (permOf e)) = out.map moveOf at h'
    rw [← machineOf_rename] at h'
    cases hout : BB6Coverage.renameTable e m (s,b) with
    | none =>
        cases out with
        | none => rfl
        | some t => simp [machineOf, hout] at h'
    | some mv =>
        cases out with
        | none => simp [machineOf, hout] at h'
        | some t =>
            have hEq : moveOf mv = moveOf t := by
              simpa [machineOf, hout] using h'
            have hmv : mv = t := by
              exact (moveToOf mv).symm.trans ((congrArg moveTo hEq).trans (moveToOf t))
            exact congrArg some hmv
  · intro h s b out hs
    have hrow : BB6Coverage.compatible p (BB6Coverage.renameTable e m) := h
    have h_src : p (s,b) = some (out.map moveTo) := by
      cases hp : p (s,b) with
      | none => simp [partialOf,hp] at hs
      | some t =>
          have hh : t.map moveOf = out := by
            simpa [partialOf,hp] using hs
          have hv : t = out.map moveTo := by
            rw [← hh]
            cases t with
            | none => rfl
            | some mv => simp [moveToOf]
          simpa [hp] using hv
    have hEq := hrow (s,b) (out.map moveTo) h_src
    change (machineOf m (e.backward s) b).map
      (RootedLiveQuotient.renameMove (permOf e)) = out
    rw [← machineOf_rename]
    unfold machineOf
    rw [hEq]
    cases out with
    | none => rfl
    | some mv => simp [moveOfTo]

/-- Translate a total machine in the opposite direction. -/
def machineTo (m : RootedLiveQuotient.Machine (Fin 6)) : BB6Coverage.Machine :=
  fun s => (m s.1 s.2).map moveTo

theorem machineOfTo (m : RootedLiveQuotient.Machine (Fin 6)) :
    machineOf (machineTo m) = m := by
  funext s b
  unfold machineOf machineTo
  cases h : m s b with
  | none => rfl
  | some mv => simp [moveOfTo]

def permTo (e : RootedLiveQuotient.Perm (Fin 6)) : BB6Coverage.StatePerm where
  forward := e.forward
  backward := e.backward
  leftInverse := e.leftInverse
  rightInverse := e.rightInverse

/-- This is definitionally identical to the repository's
    `BB6.Agent13BlankDelay.TNFQuotientCompatible` once imported. -/
def SourceQuotientCompatible (p : BB6Coverage.PartialMachine)
    (m : BB6Coverage.Machine) : Prop :=
  ∃ e : BB6Coverage.StatePerm, e.forward 0 = 0 ∧
    BB6Coverage.compatible p (BB6Coverage.renameTable e m)

theorem sourceQuotient_iff (p : BB6Coverage.PartialMachine)
    (m : BB6Coverage.Machine) :
    RootedLiveQuotient.QuotientCompatible (partialOf p) (machineOf m) 0 ↔
      SourceQuotientCompatible p m := by
  constructor
  · rintro ⟨e,he0,he⟩
    refine ⟨permTo e, he0, ?_⟩
    apply (sourceCompatible_iff p m (permTo e)).mp
    simpa [permOf, permTo] using he
  · rintro ⟨e,he0,he⟩
    refine ⟨permOf e, he0, ?_⟩
    exact (sourceCompatible_iff p m e).mpr he

theorem source_sixTailCheck_exact (r p q : BB6Coverage.PartialMachine)
    (hr1 : RootedLiveQuotient.NamedReach (partialOf r) 0 1)
    (hr2 : RootedLiveQuotient.NamedReach (partialOf r) 0 2)
    (hpe : RootedLiveQuotient.Extends (partialOf r) (partialOf p))
    (hqf : RootedLiveQuotient.Extends (partialOf r) (partialOf q)) :
    RootedLiveQuotient.sixTailCheck (partialOf p) (partialOf q) = true ↔
      ∃ m : BB6Coverage.Machine,
        SourceQuotientCompatible p m ∧ SourceQuotientCompatible q m := by
  have core := RootedLiveQuotient.sixTailCheck_exact
    (partialOf r) (partialOf p) (partialOf q) hr1 hr2 hpe hqf
  constructor
  · intro h
    obtain ⟨m, hp, hq⟩ := core.mp h
    refine ⟨machineTo m, ?_, ?_⟩
    · apply (sourceQuotient_iff p (machineTo m)).mp
      simpa [machineOfTo] using hp
    · apply (sourceQuotient_iff q (machineTo m)).mp
      simpa [machineOfTo] using hq
  · rintro ⟨m, hp, hq⟩
    apply core.mpr
    refine ⟨machineOf m, ?_, ?_⟩
    · exact (sourceQuotient_iff p m).mpr hp
    · exact (sourceQuotient_iff q m).mpr hq

/-- Exact six-state Raw11 root, in native `BB6Coverage` representation. -/
def raw11ParentSource : BB6Coverage.PartialMachine :=
  fun s => match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 2, false => some (some ⟨false, false, 0⟩)
  | _, _ => none

theorem raw11Source_roundtrip :
    partialOf raw11ParentSource = RootedLiveQuotient.raw11Parent := by
  funext s b
  have hs : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by
    have hi := s.isLt
    omega
  rcases hs with h | h | h | h | h | h <;> subst s <;>
    cases b <;> decide

/-- Source-native exact quotient collision criterion, no literal JSON/indices. -/
theorem raw11_source_sixTail_exact (p q : BB6Coverage.PartialMachine)
    (hp : RootedLiveQuotient.Extends (partialOf raw11ParentSource) (partialOf p))
    (hq : RootedLiveQuotient.Extends (partialOf raw11ParentSource) (partialOf q)) :
    RootedLiveQuotient.sixTailCheck (partialOf p) (partialOf q) = true ↔
      ∃ m : BB6Coverage.Machine,
        SourceQuotientCompatible p m ∧ SourceQuotientCompatible q m := by
  apply source_sixTailCheck_exact raw11ParentSource p q
  · simpa only [raw11Source_roundtrip] using RootedLiveQuotient.raw11Reach1
  · simpa only [raw11Source_roundtrip] using RootedLiveQuotient.raw11Reach2
  · exact hp
  · exact hq

/-- Machine-independent exclusion for an original-source pair with a false
    six-tail overlap check, even allowing different rooted relabelings. -/
theorem raw11_source_no_common (p q : BB6Coverage.PartialMachine)
    (hp : RootedLiveQuotient.Extends (partialOf raw11ParentSource) (partialOf p))
    (hq : RootedLiveQuotient.Extends (partialOf raw11ParentSource) (partialOf q))
    (hfalse : RootedLiveQuotient.sixTailCheck (partialOf p) (partialOf q) = false) :
    ¬ ∃ m : BB6Coverage.Machine,
       SourceQuotientCompatible p m ∧ SourceQuotientCompatible q m := by
  intro h
  have htrue := (raw11_source_sixTail_exact p q hp hq).mpr h
  rw [hfalse] at htrue
  contradiction

#print axioms raw11_source_sixTail_exact
#print axioms raw11_source_no_common

#print axioms source_sixTailCheck_exact

#print axioms sourceCompatible_iff
end Agent24RootedSourceBridge