import SweepPumping
import FAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw47Binary932937
open BB6Coverage BB6Coverage.Agent31Pump

/-- Two partial tables differing only in the intermediate control state of the
    two-step A1-to-E0 path. -/
def ctr (v : Bool) : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,if v then 1 else 4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => if v then some (some ⟨false,false,4⟩) else none
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => if v then none else some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨false,true,3⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

def zz : List Bool := [false,false]
def oo : List Bool := [true,true]
def zo : List Bool := [false,true]
def frame (s : List Bool) : Z0 := ⟨5,[true],[false,false,true]++s⟩
def carry (k : Nat) (s : List Bool) : Z0 :=
  ⟨2,s.headD false :: (rep zz (k+1) ++ [true,true]),s.tail⟩
def dframe (k : Nat) (s : List Bool) : Z0 := ⟨3,rep zz k++[true,true],s⟩

theorem entry (v : Bool) : run0 (ctr v) 10 ⟨0,[],[]⟩ = some (frame []) := by cases v <;> rfl

theorem beginCarry (v : Bool) (s : List Bool) :
    run0 (ctr v) 4 (frame s) = some (carry 0 s) := rfl

theorem carryZero (v : Bool) (k : Nat) (s : List Bool) :
    run0 (ctr v) 2 (carry k (zo++s)) = some (carry (k+1) s) := rfl

theorem carryOne (v : Bool) (k : Nat) (s : List Bool) :
    run0 (ctr v) 5 (carry k (oo++s)) = some (dframe (k+1) (zo++s)) := by cases v <;> rfl

theorem carryEmpty (v : Bool) (k : Nat) :
    run0 (ctr v) 1 (carry k []) = some (dframe (k+2) []) := rfl

theorem dblock (v : Bool) (L R : List Bool) :
    run0 (ctr v) 2 ⟨3,zz++L,R⟩ = some ⟨3,L,oo++R⟩ := rfl

theorem dsweep (v : Bool) (k : Nat) (s : List Bool) :
    run0 (ctr v) (2*k) (dframe k s) = some ⟨3,[true,true],rep oo k++s⟩ := by
  simpa only [dframe,List.nil_append] using sweepL (ctr v) 3 [] [] zz oo 2
    (by intro L R; simpa only [List.nil_append] using dblock v L R) k [true,true] s

theorem reset (v : Bool) (s : List Bool) :
    run0 (ctr v) 5 ⟨3,[true,true],oo++s⟩ = some (frame s) := by cases v <;> rfl

theorem finish (v : Bool) (k : Nat) (s : List Bool) :
    run0 (ctr v) (2*(k+1)+5) (dframe (k+1) s) = some (frame (rep oo k++s)) := by
  exact join0 (dsweep v (k+1) s) (by simpa only [rep,List.append_assoc] using reset v (rep oo k++s))

theorem oneReturn (v : Bool) (k : Nat) (s : List Bool) :
    run0 (ctr v) (5+(2*(k+1)+5)) (carry k (oo++s)) = some (frame (rep oo k++zo++s)) := by
  simpa only [List.append_assoc] using join0 (carryOne v k s) (finish v k (zo++s))

theorem emptyReturn (v : Bool) (k : Nat) :
    run0 (ctr v) (1+(2*(k+2)+5)) (carry k []) = some (frame (rep oo (k+1))) := by
  simpa only [List.append_nil] using join0 (carryEmpty v k) (finish v (k+1) [])

inductive Good : List Bool → Prop where
  | empty : Good []
  | zero {s} : Good s → Good (zo++s)
  | one {s} : Good s → Good (oo++s)

theorem goodPad (k : Nat) {s : List Bool} (h : Good s) : Good (rep oo k++s) := by
  induction k with
  | zero => simpa [rep] using h
  | succ k ih => simpa only [rep,List.append_assoc] using Good.one ih

inductive Inv : Z0 → Prop where
  | base {s} : Good s → Inv (frame s)
  | carrying {k s} : Good s → Inv (carry k s)

theorem progress (v : Bool) {c : Z0} (h : Inv c) :
    ∃ c' d, 0<d ∧ Inv c' ∧ run0 (ctr v) d c = some c' := by
  cases h with
  | base hg => exact ⟨_,4,by decide,Inv.carrying hg,beginCarry v _⟩
  | @carrying k s hg =>
    cases hg with
    | empty => exact ⟨_,_,by omega,Inv.base (by simpa only [List.append_nil] using goodPad (k+1) Good.empty),emptyReturn v k⟩
    | zero h => exact ⟨_,2,by decide,Inv.carrying h,carryZero v k _⟩
    | one h => exact ⟨_,_,by omega,Inv.base (by simpa only [List.append_assoc] using goodPad k (Good.zero h)),oneReturn v k _⟩

theorem arbitrarilyLive (v : Bool) (n : Nat) :
    ∃ c t, n ≤ t ∧ Inv c ∧ run0 (ctr v) t ⟨0,[],[]⟩ = some c := by
  induction n with
  | zero => exact ⟨_,10,by decide,Inv.base Good.empty,entry v⟩
  | succ n ih =>
    obtain ⟨c,t,ht,hg,hr⟩ := ih
    obtain ⟨c',d,hd,hg',hs⟩ := progress v hg
    exact ⟨c',t+d,by omega,hg',join0 hr hs⟩

theorem never (v : Bool) (m : Machine) (hm : compatible (ctr v) m) : NeverHalts m := by
  intro n
  obtain ⟨c,t,ht,_,hr⟩ := arbitrarilyLive v n
  have hz : (Agent50Zipper.zrun (ctr v) t start).map project = some c :=
    (run_project (ctr v) t start).trans hr
  cases h : Agent50Zipper.zrun (ctr v) t start with
  | none => simp [h] at hz
  | some z =>
    have H := Agent50Zipper.zrun_sound (ctr v) m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms progress
#print axioms never
end BB6.Agent2Raw47Binary932937
