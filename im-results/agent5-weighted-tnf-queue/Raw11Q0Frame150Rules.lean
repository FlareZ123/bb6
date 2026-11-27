import Agent5Frame150
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6Coverage.Agent31Pump.Frame150.Raw11
open BB6Coverage Agent31Pump BB6.Agent13BlankDelay

namespace M0
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,false,3⟩)
  | 3,false => some (some ⟨false,true,1⟩)
  | 3,true => some (some ⟨true,false,2⟩)
  | 4,false => none
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem rules : Rules table false where
  big L R := by
    have h := Auto.knownRun_sound table 3
      (show Auto.knownRun table 3 ⟨4,[true],[true,true,true]⟩ = some ⟨4,[true,false,true,true],[]⟩ from by decide +kernel) L R
    exact RE.ofRun h (by decide) (ZEq.refl _) (ZEq.refl _)
  small c d X Y := by
    cases c <;> cases d
    · have h := Auto.knownRun_sound table 11
        (show Auto.knownRun table 11 ⟨4,[true,false,false,false,false,false,false,false,false],[false,true]⟩ = some ⟨4,[true,false,false,false,false,false,false,false],[true,false,true]⟩ from by decide +kernel) [] Y
      exact RE.ofRun h (by decide) ⟨rfl,(WEq.pad [true,false] 7).symm,WEq.refl _⟩ ⟨rfl,WEq.pad [true,false] 6,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 15
        (show Auto.knownRun table 15 ⟨4,[true,false,false,false,false,false,false,false,false],[true,false,true]⟩ = some ⟨4,[true,false,false,false,false,false,false,false],[true,true,true,true]⟩ from by decide +kernel) [] Y
      exact RE.ofRun h (by decide) ⟨rfl,(WEq.pad [true,false] 7).symm,WEq.refl _⟩ ⟨rfl,WEq.pad [true,false] 6,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 11
        (show Auto.knownRun table 11 ⟨4,[true,false,false,false,false,false,false,false,false],[false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false,false,false,false,false,false],[true,false,false,false,false,false,false,false,false]⟩ from by decide +kernel) [] []
      exact RE.ofRun h (by decide) ⟨rfl,(WEq.pad [true,false] 7).symm,(WEq.pad [] 8).symm⟩ ⟨rfl,WEq.pad [true,false] 6,WEq.pad [true] 8⟩
    · have h := Auto.knownRun_sound table 15
        (show Auto.knownRun table 15 ⟨4,[true,false,false,false,false,false,false,false,false],[true,false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false,false,false,false,false,false],[true,true,true,false,false,false,false,false,false,false]⟩ from by decide +kernel) [] []
      exact RE.ofRun h (by decide) ⟨rfl,(WEq.pad [true,false] 7).symm,(WEq.pad [true] 8).symm⟩ ⟨rfl,WEq.pad [true,false] 6,WEq.pad [true,true,true] 7⟩
    · have h := Auto.knownRun_sound table 8
        (show Auto.knownRun table 8 ⟨4,[true,false,true,true,false],[false,true]⟩ = some ⟨4,[true,false,false],[false,true,false,true]⟩ from by decide +kernel) X Y
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,WEq.refl _⟩ ⟨rfl,WEq.refl _,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 12
        (show Auto.knownRun table 12 ⟨4,[true,false,true,true,false],[true,false,true]⟩ = some ⟨4,[true,false,false],[false,true,true,true,true]⟩ from by decide +kernel) X Y
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,WEq.refl _⟩ ⟨rfl,WEq.refl _,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 8
        (show Auto.knownRun table 8 ⟨4,[true,false,true,true,false],[false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false],[false,true,false,false,false,false,false,false,false,false]⟩ from by decide +kernel) X []
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,(WEq.pad [] 8).symm⟩ ⟨rfl,WEq.refl _,WEq.pad [false,true] 8⟩
    · have h := Auto.knownRun_sound table 12
        (show Auto.knownRun table 12 ⟨4,[true,false,true,true,false],[true,false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false],[false,true,true,true,false,false,false,false,false,false,false]⟩ from by decide +kernel) X []
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,(WEq.pad [true] 8).symm⟩ ⟨rfl,WEq.refl _,WEq.pad [false,true,true,true] 7⟩
    · have h := Auto.knownRun_sound table 13
        (show Auto.knownRun table 13 ⟨4,[true,false,false,true,true,false],[false,true]⟩ = some ⟨4,[true,false,false],[true,true,true,false,true]⟩ from by decide +kernel) X Y
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,WEq.refl _⟩ ⟨rfl,WEq.refl _,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 17
        (show Auto.knownRun table 17 ⟨4,[true,false,false,true,true,false],[true,false,true]⟩ = some ⟨4,[true,false,false],[true,true,true,true,true,true]⟩ from by decide +kernel) X Y
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,WEq.refl _⟩ ⟨rfl,WEq.refl _,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 13
        (show Auto.knownRun table 13 ⟨4,[true,false,false,true,true,false],[false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false],[true,true,true,false,false,false,false,false,false,false,false]⟩ from by decide +kernel) X []
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,(WEq.pad [] 8).symm⟩ ⟨rfl,WEq.refl _,WEq.pad [true,true,true] 8⟩
    · have h := Auto.knownRun_sound table 17
        (show Auto.knownRun table 17 ⟨4,[true,false,false,true,true,false],[true,false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false],[true,true,true,true,true,false,false,false,false,false,false,false]⟩ from by decide +kernel) X []
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,(WEq.pad [true] 8).symm⟩ ⟨rfl,WEq.refl _,WEq.pad [true,true,true,true,true] 7⟩
    · have h := Auto.knownRun_sound table 11
        (show Auto.knownRun table 11 ⟨4,[true,false,false,false],[false,true]⟩ = some ⟨4,[true,false,false],[true,false,true]⟩ from by decide +kernel) X Y
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,WEq.refl _⟩ ⟨rfl,WEq.refl _,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 15
        (show Auto.knownRun table 15 ⟨4,[true,false,false,false],[true,false,true]⟩ = some ⟨4,[true,false,false],[true,true,true,true]⟩ from by decide +kernel) X Y
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,WEq.refl _⟩ ⟨rfl,WEq.refl _,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 11
        (show Auto.knownRun table 11 ⟨4,[true,false,false,false],[false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false],[true,false,false,false,false,false,false,false,false]⟩ from by decide +kernel) X []
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,(WEq.pad [] 8).symm⟩ ⟨rfl,WEq.refl _,WEq.pad [true] 8⟩
    · have h := Auto.knownRun_sound table 15
        (show Auto.knownRun table 15 ⟨4,[true,false,false,false],[true,false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false],[true,true,true,false,false,false,false,false,false,false]⟩ from by decide +kernel) X []
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,(WEq.pad [true] 8).symm⟩ ⟨rfl,WEq.refl _,WEq.pad [true,true,true] 7⟩
theorem seed : run0 table 7 ⟨0,[],[]⟩ = some ⟨4,[true,false,false],[false]⟩ := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Frame150.never rules seed m hm
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)
#print axioms cover
end M0

namespace M1
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,false,3⟩)
  | 3,false => some (some ⟨false,true,1⟩)
  | 3,true => some (some ⟨true,false,2⟩)
  | 4,false => none
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,false,3⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem rules : Rules table false where
  big L R := by
    have h := Auto.knownRun_sound table 3
      (show Auto.knownRun table 3 ⟨4,[true],[true,true,true]⟩ = some ⟨4,[true,false,true,true],[]⟩ from by decide +kernel) L R
    exact RE.ofRun h (by decide) (ZEq.refl _) (ZEq.refl _)
  small c d X Y := by
    cases c <;> cases d
    · have h := Auto.knownRun_sound table 11
        (show Auto.knownRun table 11 ⟨4,[true,false,false,false,false,false,false,false,false],[false,true]⟩ = some ⟨4,[true,false,false,false,false,false,false,false],[true,false,true]⟩ from by decide +kernel) [] Y
      exact RE.ofRun h (by decide) ⟨rfl,(WEq.pad [true,false] 7).symm,WEq.refl _⟩ ⟨rfl,WEq.pad [true,false] 6,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 15
        (show Auto.knownRun table 15 ⟨4,[true,false,false,false,false,false,false,false,false],[true,false,true]⟩ = some ⟨4,[true,false,false,false,false,false,false,false],[true,true,true,true]⟩ from by decide +kernel) [] Y
      exact RE.ofRun h (by decide) ⟨rfl,(WEq.pad [true,false] 7).symm,WEq.refl _⟩ ⟨rfl,WEq.pad [true,false] 6,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 11
        (show Auto.knownRun table 11 ⟨4,[true,false,false,false,false,false,false,false,false],[false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false,false,false,false,false,false],[true,false,false,false,false,false,false,false,false]⟩ from by decide +kernel) [] []
      exact RE.ofRun h (by decide) ⟨rfl,(WEq.pad [true,false] 7).symm,(WEq.pad [] 8).symm⟩ ⟨rfl,WEq.pad [true,false] 6,WEq.pad [true] 8⟩
    · have h := Auto.knownRun_sound table 15
        (show Auto.knownRun table 15 ⟨4,[true,false,false,false,false,false,false,false,false],[true,false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false,false,false,false,false,false],[true,true,true,false,false,false,false,false,false,false]⟩ from by decide +kernel) [] []
      exact RE.ofRun h (by decide) ⟨rfl,(WEq.pad [true,false] 7).symm,(WEq.pad [true] 8).symm⟩ ⟨rfl,WEq.pad [true,false] 6,WEq.pad [true,true,true] 7⟩
    · have h := Auto.knownRun_sound table 8
        (show Auto.knownRun table 8 ⟨4,[true,false,true,true,false],[false,true]⟩ = some ⟨4,[true,false,false],[false,true,false,true]⟩ from by decide +kernel) X Y
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,WEq.refl _⟩ ⟨rfl,WEq.refl _,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 12
        (show Auto.knownRun table 12 ⟨4,[true,false,true,true,false],[true,false,true]⟩ = some ⟨4,[true,false,false],[false,true,true,true,true]⟩ from by decide +kernel) X Y
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,WEq.refl _⟩ ⟨rfl,WEq.refl _,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 8
        (show Auto.knownRun table 8 ⟨4,[true,false,true,true,false],[false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false],[false,true,false,false,false,false,false,false,false,false]⟩ from by decide +kernel) X []
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,(WEq.pad [] 8).symm⟩ ⟨rfl,WEq.refl _,WEq.pad [false,true] 8⟩
    · have h := Auto.knownRun_sound table 12
        (show Auto.knownRun table 12 ⟨4,[true,false,true,true,false],[true,false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false],[false,true,true,true,false,false,false,false,false,false,false]⟩ from by decide +kernel) X []
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,(WEq.pad [true] 8).symm⟩ ⟨rfl,WEq.refl _,WEq.pad [false,true,true,true] 7⟩
    · have h := Auto.knownRun_sound table 13
        (show Auto.knownRun table 13 ⟨4,[true,false,false,true,true,false],[false,true]⟩ = some ⟨4,[true,false,false],[true,true,true,false,true]⟩ from by decide +kernel) X Y
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,WEq.refl _⟩ ⟨rfl,WEq.refl _,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 17
        (show Auto.knownRun table 17 ⟨4,[true,false,false,true,true,false],[true,false,true]⟩ = some ⟨4,[true,false,false],[true,true,true,true,true,true]⟩ from by decide +kernel) X Y
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,WEq.refl _⟩ ⟨rfl,WEq.refl _,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 13
        (show Auto.knownRun table 13 ⟨4,[true,false,false,true,true,false],[false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false],[true,true,true,false,false,false,false,false,false,false,false]⟩ from by decide +kernel) X []
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,(WEq.pad [] 8).symm⟩ ⟨rfl,WEq.refl _,WEq.pad [true,true,true] 8⟩
    · have h := Auto.knownRun_sound table 17
        (show Auto.knownRun table 17 ⟨4,[true,false,false,true,true,false],[true,false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false],[true,true,true,true,true,false,false,false,false,false,false,false]⟩ from by decide +kernel) X []
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,(WEq.pad [true] 8).symm⟩ ⟨rfl,WEq.refl _,WEq.pad [true,true,true,true,true] 7⟩
    · have h := Auto.knownRun_sound table 11
        (show Auto.knownRun table 11 ⟨4,[true,false,false,false],[false,true]⟩ = some ⟨4,[true,false,false],[true,false,true]⟩ from by decide +kernel) X Y
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,WEq.refl _⟩ ⟨rfl,WEq.refl _,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 15
        (show Auto.knownRun table 15 ⟨4,[true,false,false,false],[true,false,true]⟩ = some ⟨4,[true,false,false],[true,true,true,true]⟩ from by decide +kernel) X Y
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,WEq.refl _⟩ ⟨rfl,WEq.refl _,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 11
        (show Auto.knownRun table 11 ⟨4,[true,false,false,false],[false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false],[true,false,false,false,false,false,false,false,false]⟩ from by decide +kernel) X []
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,(WEq.pad [] 8).symm⟩ ⟨rfl,WEq.refl _,WEq.pad [true] 8⟩
    · have h := Auto.knownRun_sound table 15
        (show Auto.knownRun table 15 ⟨4,[true,false,false,false],[true,false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false],[true,true,true,false,false,false,false,false,false,false]⟩ from by decide +kernel) X []
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,(WEq.pad [true] 8).symm⟩ ⟨rfl,WEq.refl _,WEq.pad [true,true,true] 7⟩
theorem seed : run0 table 7 ⟨0,[],[]⟩ = some ⟨4,[true,false,false],[false]⟩ := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Frame150.never rules seed m hm
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)
#print axioms cover
end M1

namespace M2
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,false,3⟩)
  | 3,false => some (some ⟨false,true,1⟩)
  | 3,true => some (some ⟨true,false,2⟩)
  | 4,false => none
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨false,true,3⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem rules : Rules table true where
  big L R := by
    have h := Auto.knownRun_sound table 3
      (show Auto.knownRun table 3 ⟨4,[true],[true,true,true]⟩ = some ⟨4,[true,false,true,true],[]⟩ from by decide +kernel) L R
    exact RE.ofRun h (by decide) (ZEq.refl _) (ZEq.refl _)
  small c d X Y := by
    cases c <;> cases d
    · have h := Auto.knownRun_sound table 13
        (show Auto.knownRun table 13 ⟨4,[true,false,false,false,false,false,false,false,false],[false,true]⟩ = some ⟨4,[true,false,false,false,false,false,false,false],[true,false,true]⟩ from by decide +kernel) [] Y
      exact RE.ofRun h (by decide) ⟨rfl,(WEq.pad [true,false] 7).symm,WEq.refl _⟩ ⟨rfl,WEq.pad [true,false] 6,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 15
        (show Auto.knownRun table 15 ⟨4,[true,false,false,false,false,false,false,false,false],[true,false,true]⟩ = some ⟨4,[true,false,false,false,false,false,false,false],[true,true,true,true]⟩ from by decide +kernel) [] Y
      exact RE.ofRun h (by decide) ⟨rfl,(WEq.pad [true,false] 7).symm,WEq.refl _⟩ ⟨rfl,WEq.pad [true,false] 6,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 21
        (show Auto.knownRun table 21 ⟨4,[true,false,false,false,false,false,false,false,false],[false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false,false,false,false,false,false],[true,true,true,true,false,false,false,false,false]⟩ from by decide +kernel) [] []
      exact RE.ofRun h (by decide) ⟨rfl,(WEq.pad [true,false] 7).symm,(WEq.pad [] 8).symm⟩ ⟨rfl,WEq.pad [true,false] 6,WEq.pad [true,true,true,true] 5⟩
    · have h := Auto.knownRun_sound table 15
        (show Auto.knownRun table 15 ⟨4,[true,false,false,false,false,false,false,false,false],[true,false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false,false,false,false,false,false],[true,true,true,false,false,false,false,false,false,false]⟩ from by decide +kernel) [] []
      exact RE.ofRun h (by decide) ⟨rfl,(WEq.pad [true,false] 7).symm,(WEq.pad [true] 8).symm⟩ ⟨rfl,WEq.pad [true,false] 6,WEq.pad [true,true,true] 7⟩
    · have h := Auto.knownRun_sound table 10
        (show Auto.knownRun table 10 ⟨4,[true,false,true,true,false],[false,true]⟩ = some ⟨4,[true,false,false],[false,true,false,true]⟩ from by decide +kernel) X Y
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,WEq.refl _⟩ ⟨rfl,WEq.refl _,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 12
        (show Auto.knownRun table 12 ⟨4,[true,false,true,true,false],[true,false,true]⟩ = some ⟨4,[true,false,false],[false,true,true,true,true]⟩ from by decide +kernel) X Y
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,WEq.refl _⟩ ⟨rfl,WEq.refl _,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 18
        (show Auto.knownRun table 18 ⟨4,[true,false,true,true,false],[false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false],[false,true,true,true,true,false,false,false,false,false]⟩ from by decide +kernel) X []
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,(WEq.pad [] 8).symm⟩ ⟨rfl,WEq.refl _,WEq.pad [false,true,true,true,true] 5⟩
    · have h := Auto.knownRun_sound table 12
        (show Auto.knownRun table 12 ⟨4,[true,false,true,true,false],[true,false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false],[false,true,true,true,false,false,false,false,false,false,false]⟩ from by decide +kernel) X []
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,(WEq.pad [true] 8).symm⟩ ⟨rfl,WEq.refl _,WEq.pad [false,true,true,true] 7⟩
    · have h := Auto.knownRun_sound table 15
        (show Auto.knownRun table 15 ⟨4,[true,false,false,true,true,false],[false,true]⟩ = some ⟨4,[true,false,false],[true,true,true,false,true]⟩ from by decide +kernel) X Y
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,WEq.refl _⟩ ⟨rfl,WEq.refl _,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 17
        (show Auto.knownRun table 17 ⟨4,[true,false,false,true,true,false],[true,false,true]⟩ = some ⟨4,[true,false,false],[true,true,true,true,true,true]⟩ from by decide +kernel) X Y
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,WEq.refl _⟩ ⟨rfl,WEq.refl _,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 23
        (show Auto.knownRun table 23 ⟨4,[true,false,false,true,true,false],[false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false],[true,true,true,true,true,true,false,false,false,false,false]⟩ from by decide +kernel) X []
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,(WEq.pad [] 8).symm⟩ ⟨rfl,WEq.refl _,WEq.pad [true,true,true,true,true,true] 5⟩
    · have h := Auto.knownRun_sound table 17
        (show Auto.knownRun table 17 ⟨4,[true,false,false,true,true,false],[true,false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false],[true,true,true,true,true,false,false,false,false,false,false,false]⟩ from by decide +kernel) X []
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,(WEq.pad [true] 8).symm⟩ ⟨rfl,WEq.refl _,WEq.pad [true,true,true,true,true] 7⟩
    · have h := Auto.knownRun_sound table 13
        (show Auto.knownRun table 13 ⟨4,[true,false,false,false],[false,true]⟩ = some ⟨4,[true,false,false],[true,false,true]⟩ from by decide +kernel) X Y
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,WEq.refl _⟩ ⟨rfl,WEq.refl _,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 15
        (show Auto.knownRun table 15 ⟨4,[true,false,false,false],[true,false,true]⟩ = some ⟨4,[true,false,false],[true,true,true,true]⟩ from by decide +kernel) X Y
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,WEq.refl _⟩ ⟨rfl,WEq.refl _,WEq.refl _⟩
    · have h := Auto.knownRun_sound table 21
        (show Auto.knownRun table 21 ⟨4,[true,false,false,false],[false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false],[true,true,true,true,false,false,false,false,false]⟩ from by decide +kernel) X []
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,(WEq.pad [] 8).symm⟩ ⟨rfl,WEq.refl _,WEq.pad [true,true,true,true] 5⟩
    · have h := Auto.knownRun_sound table 15
        (show Auto.knownRun table 15 ⟨4,[true,false,false,false],[true,false,false,false,false,false,false,false,false]⟩ = some ⟨4,[true,false,false],[true,true,true,false,false,false,false,false,false,false]⟩ from by decide +kernel) X []
      exact RE.ofRun h (by decide) ⟨rfl,WEq.refl _,(WEq.pad [true] 8).symm⟩ ⟨rfl,WEq.refl _,WEq.pad [true,true,true] 7⟩
theorem seed : run0 table 7 ⟨0,[],[]⟩ = some ⟨4,[true,false,false],[false]⟩ := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Frame150.never rules seed m hm
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)
#print axioms cover
end M2

end BB6Coverage.Agent31Pump.Frame150.Raw11
