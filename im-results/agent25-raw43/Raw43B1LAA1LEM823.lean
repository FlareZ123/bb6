import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B1LAA1LEM823
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,false,2⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

def P : List Bool := [false,false,true]
def T : List Bool := [true,true,true]
def A (L R : List Bool) : Z0 := ⟨0,L,R⟩
def D (L R : List Bool) : Z0 := ⟨3,[true,false]++L,R⟩
inductive Right : List Bool → Prop where
  | base : Right T
  | push {R} : Right R → Right (P++R)
inductive Left : List Bool → Prop where
  | nil : Left []
  | last (b : Bool) : Left [b,true]
  | digit (b c : Bool) {L} : Left L → Left ([b,c,false]++L)
inductive Inv : Z0 → Prop where
  | empty R : Right R → Inv (A [] R)
  | single R : Right R → Inv (A [true] R)
  | stack b L R : Left L → Right R → Inv (A ([b,false]++L) R)
  | down L R : Left L → Right R → Inv (D L R)

private theorem first : run0 table 14 ⟨0,[],[]⟩ = some (A [false,false] T) := by rfl
private theorem emptyEnd : run0 table 2 (A [] T) = some (A [true] T) := by rfl
private theorem emptyPush (R : List Bool) :
    run0 table 3 (A [] (P++R)) = some (D [true,true] R) := by rfl
private theorem zeroEnd (L : List Bool) :
    run0 table 2 (A ([false,false]++L) T) = some (A ([true,false]++L) T) := by rfl
private theorem zeroPush (L R : List Bool) :
    run0 table 3 (A ([false,false]++L) (P++R)) =
      some (D ([true,true,false]++L) R) := by rfl
private theorem singlePop (R : List Bool) :
    run0 table 3 (A [true] R) = some (A [] (P++R)) := by rfl
private theorem oneNil (R : List Bool) :
    run0 table 3 (A [true,false] R) = some (A [] (P++R)) := by rfl
private theorem oneLast0 (R : List Bool) :
    run0 table 3 (A [true,false,false,true] R) =
      some (A [true] (P++R)) := by rfl
private theorem oneDigit0 (c : Bool) (L R : List Bool) :
    run0 table 3 (A ([true,false,false,c,false]++L) R) =
      some (A ([c,false]++L) (P++R)) := by rfl
private theorem oneLast1 (R : List Bool) :
    run0 table 4 (A [true,false,true,true] R) =
      some (D [false,true] R) := by rfl
private theorem oneDigit1 (c : Bool) (L R : List Bool) :
    run0 table 4 (A ([true,false,true,c,false]++L) R) =
      some (D ([false,c,false]++L) R) := by rfl
private theorem downPush (L R : List Bool) :
    run0 table 3 (D L (P++R)) = some (D ([true,false,false]++L) R) := by rfl
private theorem downEnd (L : List Bool) :
    run0 table 2 (D L T) = some (A ([false,false]++L) T) := by rfl

private theorem advance (z : Z0) (h : Inv z) :
    ∃ k z', 0 < k ∧ run0 table k z = some z' ∧ Inv z' := by
  cases h with
  | empty R g =>
    cases g with
    | base => exact ⟨2,_,by decide,emptyEnd,.single _ .base⟩
    | push g => exact ⟨3,_,by decide,emptyPush _,.down _ _ (.last true) g⟩
  | single R g => exact ⟨3,_,by decide,singlePop R,.empty _ (.push g)⟩
  | stack b L R s g =>
    cases b with
    | false =>
      cases g with
      | base => exact ⟨2,_,by decide,zeroEnd L,.stack true _ _ s .base⟩
      | push g => exact ⟨3,_,by decide,zeroPush L _,.down _ _ (.digit true true s) g⟩
    | true =>
      cases s with
      | nil => exact ⟨3,_,by decide,oneNil R,.empty _ (.push g)⟩
      | last b =>
        cases b with
        | false => exact ⟨3,_,by decide,oneLast0 R,.single _ (.push g)⟩
        | true => exact ⟨4,_,by decide,oneLast1 R,.down _ _ (.last false) g⟩
      | digit b c s =>
        cases b with
        | false => exact ⟨3,_,by decide,oneDigit0 c _ R,.stack c _ _ s (.push g)⟩
        | true => exact ⟨4,_,by decide,oneDigit1 c _ R,.down _ _ (.digit false c s) g⟩
  | down L R s g =>
    cases g with
    | base => exact ⟨2,_,by decide,downEnd L,.stack false _ _ s .base⟩
    | push g => exact ⟨3,_,by decide,downPush L _,.down _ _ (.digit true false s) g⟩

theorem live_prefix (n : Nat) :
    ∃ t z, n≤t ∧ run0 table t ⟨0,[],[]⟩=some z ∧ Inv z := by
  induction n with
  | zero => exact ⟨_,_,by omega,first,.stack false _ _ .nil .base⟩
  | succ n ih =>
    obtain ⟨t,z,ht,hr,hi⟩ := ih
    obtain ⟨k,z',hk,h,hi'⟩ := advance z hi
    exact ⟨t+k,z',by omega,join0 hr h,hi'⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr,hi⟩ := live_prefix n
  have hz : (zrun table t start).map project = some z :=
    (run_project table t start).trans hr
  cases hZ : zrun table t start with
  | none => simp [hZ] at hz
  | some z' =>
    have H := zrun_sound table m hm t start z' hZ
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl
#print axioms live_prefix
#print axioms never
end BB6.Agent25Raw43B1LAA1LEM823
