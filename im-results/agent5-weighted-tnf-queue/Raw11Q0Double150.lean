import Agent5Pair143
import Agent5TailPump
import Root56Coverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6Coverage.Agent31Pump.Raw11Q0Double150
open BB6Coverage Agent31Pump BB6.Agent13BlankDelay
open Pair143 (Reach PosReach U Uadd)

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,false,3⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => none
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none

def E (l r : List Bool) : Z0 := ⟨4,l,r⟩
def A (r : List Bool) : Z0 := ⟨0,[],r⟩
theorem reach_refl (s : Z0) : Reach table s s := ⟨0,rfl⟩

theorem triple (n : Nat) : rep [true,true,true] n = U (3*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rep,ih,show 3*(n+1) = 3+3*n by omega,Uadd]
    rfl

def advanceCert : Tails.Cert := ⟨⟨4,(.tail [true,false,true] false),(.periodic [true,true,true,true] [true,true,true] false (.tail [false] true))⟩,⟨4,(.tail [true,false,true,true] false),(.periodic [true] [true,true,true] false (.tail [false,true,true] true))⟩,
  [.right [true] [true,true,true,true] [true,true,true] [true,true,false] false (.tail [false,true] false) (.tail [false] true) 3,
   .steps 8,
   .left [true,true,false] [] [true,true,false] [true,true,true] false (.tail [false,true] false) (.tail [false,true,true] true) 3,
   .steps 5],6,0,13⟩
theorem advanceChecked : Tails.check table advanceCert = true := by decide +kernel
theorem advanceRun (n : Nat) (X Y : List Bool) :
    Reach table (advanceCert.source.eval n 0 X Y) (advanceCert.target.eval n 0 X Y) :=
  ⟨_,Tails.check_sound table advanceCert advanceChecked n 0 X Y⟩

def mergeCert : Tails.Cert := ⟨⟨4,(.tail [true,false,true] false),(.tail [true,false] true)⟩,⟨4,(.tail [true,true,true,true] false),(.tail [true] true)⟩,
  [.steps 9],0,0,9⟩
theorem mergeChecked : Tails.check table mergeCert = true := by decide +kernel
theorem mergeRun (n : Nat) (X Y : List Bool) :
    Reach table (mergeCert.source.eval n 0 X Y) (mergeCert.target.eval n 0 X Y) :=
  ⟨_,Tails.check_sound table mergeCert mergeChecked n 0 X Y⟩

def firstICert : Tails.Cert := ⟨⟨4,(.tail [true,true,true,true] false),(.periodic [true,true,true,true,true,true,true,true,true] [true,true,true] false (.lit []))⟩,⟨4,(.tail [true,true] false),(.periodic [true,true,true,true,true,true,true,true,true,true] [true,true,true] false (.lit [false,true]))⟩,
  [.right [true] [true,true,true,true,true,true,true,true,true] [true,true,true] [true,true,false] false (.tail [true,true,true] false) (.lit []) 3,
   .steps 12,
   .left [true,true,false,true,true,false,true,true,false] [] [true,true,false] [true,true,true] false (.tail [true,true,true] false) (.lit [false,true]) 3,
   .steps 12],6,0,24⟩
theorem firstIChecked : Tails.check table firstICert = true := by decide +kernel
theorem firstIRun (n : Nat) (X Y : List Bool) :
    Reach table (firstICert.source.eval n 0 X Y) (firstICert.target.eval n 0 X Y) :=
  ⟨_,Tails.check_sound table firstICert firstIChecked n 0 X Y⟩

def firstIICert : Tails.Cert := ⟨⟨4,(.tail [true,true,true,true] false),(.periodic [true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true] false (.lit []))⟩,⟨4,(.tail [true,true] false),(.periodic [true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true] false (.lit [false,true,true]))⟩,
  [.right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true] [true,true,false] false (.tail [true,true,true] false) (.lit []) 3,
   .steps 17,
   .left [true,true,false,true,true,false,true,true,false,true,true,false] [] [true,true,false] [true,true,true] false (.tail [true,true,true] false) (.lit [false,true,true]) 3,
   .steps 15],6,0,32⟩
theorem firstIIChecked : Tails.check table firstIICert = true := by decide +kernel
theorem firstIIRun (n : Nat) (X Y : List Bool) :
    Reach table (firstIICert.source.eval n 0 X Y) (firstIICert.target.eval n 0 X Y) :=
  ⟨_,Tails.check_sound table firstIICert firstIIChecked n 0 X Y⟩

def drainCert : Tails.Cert := ⟨⟨4,(.tail [true,true,true,true] false),(.periodic [true,true,true,true,true,true,true,true,true,true] [true,true,true] false (.tail [false,true] true))⟩,⟨4,(.tail [true,true] false),(.periodic [true,true,true,true,true,true,true,true,true,true] [true,true,true] false (.tail [false,true,true,true] true))⟩,
  [.right [true] [true,true,true,true,true,true,true,true,true,true] [true,true,true] [true,true,false] false (.tail [true,true,true] false) (.tail [false,true] true) 3,
   .steps 14,
   .left [true,true,false,true,true,false,true,true,false] [] [true,true,false] [true,true,true] false (.tail [true,true,true] false) (.tail [false,true,true,true] true) 3,
   .steps 12],6,0,26⟩
theorem drainChecked : Tails.check table drainCert = true := by decide +kernel
theorem drainRun (n : Nat) (X Y : List Bool) :
    Reach table (drainCert.source.eval n 0 X Y) (drainCert.target.eval n 0 X Y) :=
  ⟨_,Tails.check_sound table drainCert drainChecked n 0 X Y⟩

def endICert : Tails.Cert := ⟨⟨4,(.lit [true,true]),(.periodic [true,true,true,true,true,true,true,true,true,true] [true,true,true] false (.tail [false,true] true))⟩,⟨0,(.lit []),(.periodic [true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true] false (.tail [false,true,true,true,true] true))⟩,
  [.right [true] [true,true,true,true,true,true,true,true,true,true] [true,true,true] [true,true,false] false (.lit [true]) (.tail [false,true] true) 3,
   .steps 14,
   .left [true,true,false,true,true,false,true,true,false] [] [true,true,false] [true,true,true] false (.lit [true]) (.tail [false,true,true,true] true) 3,
   .steps 14,
   .right [true] [true,true,true,true,true,true,true,true,true,true] [true,true,true] [true,false,true] false (.lit [true]) (.tail [false,true,true,true] true) 3,
   .steps 13,
   .left [true,true,false,true,true,false,true,true,false,true] [] [true,false,true] [true,true,true] false (.lit [true]) (.tail [false,true,true,true,true] true) 3,
   .steps 12],12,0,53⟩
theorem endIChecked : Tails.check table endICert = true := by decide +kernel
theorem endIRun (n : Nat) (X Y : List Bool) :
    Reach table (endICert.source.eval n 0 X Y) (endICert.target.eval n 0 X Y) :=
  ⟨_,Tails.check_sound table endICert endIChecked n 0 X Y⟩

def endIICert : Tails.Cert := ⟨⟨4,(.lit [true,true,true]),(.periodic [true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true] false (.tail [false,true] true))⟩,⟨0,(.lit []),(.periodic [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true] false (.tail [false,true,true,true] true))⟩,
  [.right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true] [true,true,false] false (.lit [true,true]) (.tail [false,true] true) 3,
   .steps 17,
   .left [true,true,false,true,true,false,true,true,false,true,true,false] [] [true,true,false] [true,true,true] false (.lit [true,true]) (.tail [false,true,true,true] true) 3,
   .steps 15],6,0,32⟩
theorem endIIChecked : Tails.check table endIICert = true := by decide +kernel
theorem endIIRun (n : Nat) (X Y : List Bool) :
    Reach table (endIICert.source.eval n 0 X Y) (endIICert.target.eval n 0 X Y) :=
  ⟨_,Tails.check_sound table endIICert endIIChecked n 0 X Y⟩

def startCert : Tails.Cert := ⟨⟨0,(.lit []),(.tail [true,true,true] true)⟩,⟨4,(.lit [true,false,true]),(.tail [true] true)⟩,
  [.steps 2],0,0,2⟩
theorem startChecked : Tails.check table startCert = true := by decide +kernel
theorem startRun (n : Nat) (X Y : List Bool) :
    Reach table (startCert.source.eval n 0 X Y) (startCert.target.eval n 0 X Y) :=
  ⟨_,Tails.check_sound table startCert startChecked n 0 X Y⟩

/-- Shift a constant prefix of ones past an arbitrary run length. -/
theorem prefix (a n : Nat) : U (a+n) = U a ++ U n := Uadd a n

theorem advance (n : Nat) (X Y : List Bool) :
    Reach table (E ([true,false,true]++X) (U (3*n+4)++false::Y))
      (E ([true,false,true,true]++X) (U (3*n+1)++false::true::true::Y)) := by
  rw [show 3*n+4=4+3*n by omega,show 3*n+1=1+3*n by omega,Uadd 4,Uadd 1]
  simpa only [advanceCert,Tails.PZ.eval,Tails.Word.eval,triple,List.append_assoc] using advanceRun n X Y

theorem merge (X Y : List Bool) :
    Reach table (E ([true,false,true]++X) (true::false::Y))
      (E ([true,true,true,true]++X) (true::Y)) :=
  mergeRun 0 X Y

theorem firstI (n : Nat) (X : List Bool) :
    Reach table (E (U 4++X) (U (9+3*n)))
      (E (U 2++X) (U (10+3*n)++[false,true])) := by
  rw [Uadd 9,Uadd 10]
  simpa only [firstICert,Tails.PZ.eval,Tails.Word.eval,triple,List.append_assoc,List.append_nil] using firstIRun n X []

theorem firstII (n : Nat) (X : List Bool) :
    Reach table (E (U 4++X) (U (13+3*n)))
      (E (U 2++X) (U (13+3*n)++[false,true,true])) := by
  rw [Uadd 13]
  simpa only [firstIICert,Tails.PZ.eval,Tails.Word.eval,triple,List.append_assoc,List.append_nil] using firstIIRun n X []

theorem drainOne (n : Nat) (X Y : List Bool) :
    Reach table (E (U 4++X) (U (10+3*n)++false::true::Y))
      (E (U 2++X) (U (10+3*n)++false::true::true::true::Y)) := by
  rw [Uadd 10]
  simpa only [drainCert,Tails.PZ.eval,Tails.Word.eval,triple,List.append_assoc] using drainRun n X Y

theorem finishI (n : Nat) (Y : List Bool) :
    Reach table (E (U 2) (U (10+3*n)++false::true::Y))
      (A (U (12+3*n)++false::true::true::true::true::Y)) := by
  rw [Uadd 10,Uadd 12]
  simpa only [endICert,Tails.PZ.eval,Tails.Word.eval,triple,List.append_assoc] using endIRun n [] Y

theorem finishII (n : Nat) (Y : List Bool) :
    Reach table (E (U 3) (U (13+3*n)++false::true::Y))
      (A (U (15+3*n)++false::true::true::true::Y)) := by
  rw [Uadd 13,Uadd 15]
  simpa only [endIICert,Tails.PZ.eval,Tails.Word.eval,triple,List.append_assoc] using endIIRun n [] Y

theorem startE (n : Nat) (Y : List Bool) :
    PosReach table (A (U (3*n+3)++false::Y))
      (E [true,false,true] (U (3*n+1)++false::Y)) := by
  rw [show 3*n+3=3+3*n by omega,show 3*n+1=1+3*n by omega,Uadd 3,Uadd 1]
  exact ⟨2,by decide,Tails.check_sound table startCert startChecked 0 0 [] (U (3*n)++false::Y)⟩

def collectState (j k : Nat) (Y : List Bool) :=
  E ([true,false,true]++U k) (U (3*j+1)++false::Y)
def collectEnd (k : Nat) (Y : List Bool) := E (U (4+k)) (true::Y)

theorem collect (j k : Nat) (Y : List Bool) :
    Reach table (collectState j k Y) (collectEnd (k+j) (U (2*j)++Y)) := by
  induction j generalizing k Y with
  | zero =>
    rw [Nat.add_zero]
    simpa only [collectState,collectEnd,Uadd 4,Nat.mul_zero,Nat.zero_add,List.nil_append] using merge (U k) Y
  | succ j ih =>
    have h := advance j (U k) Y
    have h' : Reach table (collectState (j+1) k Y)
        (collectState j (k+1) (true::true::Y)) := by
      simpa only [collectState,Nat.mul_succ,show 3*j+3+1=3*j+4 by omega,U,rep,List.append_assoc] using h
    have g := ih (k+1) (true::true::Y)
    have eq : U (2*(j+1))++Y = U (2*j)++true::true::Y := by
      rw [show 2*(j+1)=2*j+2 by omega,Uadd]
      simp only [List.append_assoc]
      rfl
    rw [show k+1+j=k+(j+1) by omega] at g
    rw [eq]
    exact h'.trans g

theorem initCollect (j : Nat) (Y : List Bool) :
    PosReach table (A (U (3*j+3)++false::Y)) (collectEnd j (U (2*j)++Y)) := by
  exact (startE j Y).trans (by simpa only [collectState,Nat.zero_add,List.append_nil] using collect j 0 Y)

def drainState (n l : Nat) (Y : List Bool) :=
  E (U l) (U (10+3*n)++false::true::Y)

theorem drainAll (n k l : Nat) (Y : List Bool) :
    Reach table (drainState n (2*k+2+l) Y)
      (drainState n (2+l) (U (2*k)++Y)) := by
  induction k generalizing Y with
  | zero => exact reach_refl _
  | succ k ih =>
    have h := drainOne n (U (2*k+l)) Y
    have h' : Reach table (drainState n (2*(k+1)+2+l) Y)
        (drainState n (2*k+2+l) (true::true::Y)) := by
      rw [show 2*(k+1)+2+l=4+(2*k+l) by omega,show 2*k+2+l=2+(2*k+l) by omega]
      simpa only [drainState,Uadd 4,Uadd 2] using h
    have eq : U (2*(k+1))++Y = U (2*k)++true::true::Y := by
      rw [show 2*(k+1)=2*k+2 by omega,Uadd]
      simp only [List.append_assoc]
      rfl
    rw [eq]
    exact h'.trans (ih (true::true::Y))

def even (n : Nat) := A (U (9+6*n)++false::U (4+2*n))
def odd (n : Nat) := A (U (12+6*n)++false::U (6+2*n))

theorem evenToOdd (n : Nat) : PosReach table (even n) (odd n) := by
  have h := initCollect (2+2*n) (U (4+2*n))
  have h' : PosReach table (even n) (E (U (6+2*n)) (U (9+6*n))) := by
    have ha : 3*(2+2*n)+3=9+6*n := by omega
    have hb : 4+(2+2*n)=6+2*n := by omega
    have hc : 9+6*n=1+(2*(2+2*n)+(4+2*n)) := by omega
    rw [ha] at h
    unfold collectEnd at h
    rw [hb] at h
    rw [hc,Uadd 1,Uadd]
    simpa only [even,List.append_assoc] using h
  have g := firstI (2*n) (U (2+2*n))
  have g' : Reach table (E (U (6+2*n)) (U (9+6*n))) (drainState (2*n) (4+2*n) []) := by
    rw [show 6+2*n=4+(2+2*n) by omega,show 4+2*n=2+(2+2*n) by omega,Uadd 4,Uadd 2,show 9+6*n=9+3*(2*n) by omega]
    exact g
  have d := drainAll (2*n) (n+1) 0 []
  have d' : Reach table (drainState (2*n) (4+2*n) []) (drainState (2*n) 2 (U (2*(n+1)))) := by
    simpa only [show 2*(n+1)+2+0=4+2*n by omega,Nat.add_zero,List.append_nil] using d
  have f := finishI (2*n) (U (2*(n+1)))
  have f' : Reach table (drainState (2*n) 2 (U (2*(n+1)))) (odd n) := by
    unfold odd
    rw [show 12+6*n=12+3*(2*n) by omega,show 6+2*n=4+2*(n+1) by omega,Uadd 4]
    exact f
  exact ((h'.trans g').trans d').trans f'

theorem oddToEven (n : Nat) : PosReach table (odd n) (even (n+1)) := by
  have h := initCollect (3+2*n) (U (6+2*n))
  have h' : PosReach table (odd n) (E (U (7+2*n)) (U (13+6*n))) := by
    have ha : 3*(3+2*n)+3=12+6*n := by omega
    have hb : 4+(3+2*n)=7+2*n := by omega
    have hc : 13+6*n=1+(2*(3+2*n)+(6+2*n)) := by omega
    rw [ha] at h
    unfold collectEnd at h
    rw [hb] at h
    rw [hc,Uadd 1,Uadd]
    simpa only [odd,List.append_assoc] using h
  have g := firstII (2*n) (U (3+2*n))
  have g' : Reach table (E (U (7+2*n)) (U (13+6*n))) (drainState (2*n+1) (5+2*n) [true]) := by
    rw [show 7+2*n=4+(3+2*n) by omega,show 5+2*n=2+(3+2*n) by omega,Uadd 4,Uadd 2,show 13+6*n=13+3*(2*n) by omega]
    unfold drainState
    rw [show 10+3*(2*n+1)=13+3*(2*n) by omega]
    exact g
  have d := drainAll (2*n+1) (n+1) 1 [true]
  have d' : Reach table (drainState (2*n+1) (5+2*n) [true]) (drainState (2*n+1) 3 (U (2*(n+1)+1))) := by
    rw [show 2*(n+1)+1=2*(n+1)+1 by rfl,Uadd]
    simpa only [show 2*(n+1)+2+1=5+2*n by omega] using d
  have f := finishII (2*n) (U (2*(n+1)+1))
  have f' : Reach table (drainState (2*n+1) 3 (U (2*(n+1)+1))) (even (n+1)) := by
    unfold drainState even
    rw [show 10+3*(2*n+1)=13+3*(2*n) by omega,show 9+6*(n+1)=15+3*(2*n) by omega,show 4+2*(n+1)=3+(2*(n+1)+1) by omega,Uadd 3]
    exact f
  exact ((h'.trans g').trans d').trans f'

theorem seed : run0 table 112 ⟨0,[],[]⟩ = some (even 0) := by decide +kernel
def region (s : Z0) : Prop := (∃ n, s=even n) ∨ (∃ n,s=odd n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply Multi.never_of_region table region 112 (even 0) seed (Or.inl ⟨0,rfl⟩) _ m hm
  intro s hs
  rcases hs with ⟨n,rfl⟩ | ⟨n,rfl⟩
  · obtain ⟨k,hk,hr⟩ := evenToOdd n
    exact ⟨k,odd n,hk,Or.inr ⟨n,rfl⟩,hr⟩
  · obtain ⟨k,hk,hr⟩ := oddToEven n
    exact ⟨k,even (n+1),hk,Or.inl ⟨n+1,rfl⟩,hr⟩
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)
#print axioms cover
end BB6Coverage.Agent31Pump.Raw11Q0Double150
