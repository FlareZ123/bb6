import TranslatedCycle
import RayFinite
import Lean.Elab.Tactic.Omega

namespace BB6Coverage

/-- Finite-support configurations coincide after translating their heads and marked cells. -/
def shiftedFiniteEq (c d : FinRayCfg) : Bool :=
  let delta := d.head - c.head
  decide (c.state = d.state) &&
    c.ones.all (fun x => d.ones.contains (x + delta)) &&
    d.ones.all (fun y => c.ones.contains (y - delta))

theorem shiftedFiniteEq_sound (c d : FinRayCfg)
    (h : shiftedFiniteEq c d = true) :
    embedFinRay d = shiftConfig (d.head - c.head) (embedFinRay c) := by
  have hboth : (decide (c.state=d.state) &&
    c.ones.all (fun x => d.ones.contains (x+(d.head-c.head)))) = true ∧
    d.ones.all (fun y => c.ones.contains (y-(d.head-c.head)))=true := by
    simpa only [shiftedFiniteEq, Bool.and_eq_true] using h
  have hpair : decide (c.state=d.state)=true ∧
    c.ones.all (fun x=>d.ones.contains (x+(d.head-c.head)))=true :=
    (Bool.and_eq_true _ _).mp hboth.1
  have hs : c.state=d.state := of_decide_eq_true hpair.1
  have hl (x:Int) (hx:x∈c.ones) : x+(d.head-c.head)∈d.ones := by
    have hflag := (List.all_eq_true.mp hpair.2) x hx
    exact List.contains_iff_mem.mp hflag
  have hr (y:Int) (hy:y∈d.ones) : y-(d.head-c.head)∈c.ones := by
    have hflag := (List.all_eq_true.mp hboth.2) y hy
    exact List.contains_iff_mem.mp hflag
  have ht (x:Int) : d.ones.contains x = c.ones.contains (x-(d.head-c.head)) := by
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      exact List.contains_iff_mem.mpr (hr x (List.contains_iff_mem.mp hx))
    · intro hx
      have hmem:=hl (x-(d.head-c.head)) (List.contains_iff_mem.mp hx)
      have heq:x-(d.head-c.head)+(d.head-c.head)=x:=by omega
      simpa only [heq] using (List.contains_iff_mem.mpr hmem)
  cases c with
  | mk cs ch co =>
    cases d with
    | mk ds dh dsupp =>
      change cs=ds at hs
      change (∀ x, dsupp.contains x = co.contains (x-(dh-ch))) at ht
      have hh : dh=ch+(dh-ch):=by omega
      cases hs
      have teq : (fun x=>dsupp.contains x) = (fun x=>co.contains (x-(dh-ch))) := funext ht
      simp only [embedFinRay, finiteTape, shiftConfig]
      congr 1

/-- A finite observed blank-root prefix followed by a positive-length translated cycle. -/
def finiteTranslatedCheck (p : PartialMachine) (entry period : Nat) : Bool :=
  match finitePartialRun p entry finiteBlank with
  | none => false
  | some c =>
    match finitePartialRun p period c with
    | none => false
    | some d => shiftedFiniteEq c d

theorem finiteTranslatedCheck_sound (p : PartialMachine) (entry period bound : Nat)
    (hp : 0 < period) (h : finiteTranslatedCheck p entry period = true) :
    Cover (DecidedBelow bound) p := by
  cases he : finitePartialRun p entry finiteBlank with
  | none => simp [finiteTranslatedCheck, he] at h
  | some c =>
    cases hc : finitePartialRun p period c with
    | none => simp [finiteTranslatedCheck, he, hc] at h
    | some d =>
      have ht : shiftedFiniteEq c d = true := by
        simpa [finiteTranslatedCheck, he, hc] using h
      have hshift := shiftedFiniteEq_sound c d ht
      apply Cover.leaf
      intro m hm
      left
      have hstart : run m entry blank = some (embedFinRay c) := by
        simpa only [embedFinRay_blank] using
          (finitePartialRun_sound p m hm finiteBlank c entry he)
      have hloop : run m period (embedFinRay c) =
          some (shiftConfig (d.head-c.head) (embedFinRay c)) := by
        rw [← hshift]
        exact finitePartialRun_sound p m hm c d period hc
      exact translated_prefix_never m (embedFinRay c) entry period hp
        (d.head-c.head) hstart hloop

/-- Write a marker, then translate it one cell right after five moves. -/
def movingMarkerTable : PartialMachine := fun s =>
  if s = (0,false) then some (some ⟨true,true,5⟩)
  else if s = (5,false) then some (some ⟨false,false,1⟩)
  else if s = (1,true) then some (some ⟨false,true,2⟩)
  else if s = (2,false) then some (some ⟨true,true,3⟩)
  else if s = (3,false) then some (some ⟨false,false,4⟩)
  else if s = (4,true) then some (some ⟨true,true,5⟩)
  else none

theorem movingMarker_check : finiteTranslatedCheck movingMarkerTable 2 5 = true := by decide

theorem movingMarker_never (bound : Nat) : Cover (DecidedBelow bound) movingMarkerTable :=
  finiteTranslatedCheck_sound movingMarkerTable 2 5 bound (by decide) movingMarker_check

/-- A genuine translated convoy: a pair of ones moves right, while the head
    visits both ends of the pair. The tape is never entirely blank after entry. -/
def movingPairTable : PartialMachine := fun s =>
  if s = (0,false) then some (some ⟨true,true,5⟩)
  else if s = (5,false) then some (some ⟨true,false,1⟩)
  else if s = (1,true) then some (some ⟨false,true,2⟩)
  else if s = (2,true) then some (some ⟨true,true,3⟩)
  else if s = (3,false) then some (some ⟨true,false,4⟩)
  else if s = (4,true) then some (some ⟨true,true,5⟩)
  else if s = (5,true) then some (some ⟨true,false,1⟩)
  else none

theorem movingPair_check : finiteTranslatedCheck movingPairTable 2 5 = true := by decide

theorem movingPair_never (bound : Nat) : Cover (DecidedBelow bound) movingPairTable :=
  finiteTranslatedCheck_sound movingPairTable 2 5 bound (by decide) movingPair_check

#print axioms movingPair_never

#print axioms shiftedFiniteEq_sound
#print axioms finiteTranslatedCheck_sound
#print axioms movingMarker_never
end BB6Coverage
