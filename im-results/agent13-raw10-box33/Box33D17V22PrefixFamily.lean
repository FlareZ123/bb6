import Box33PrefixMacro

namespace BB6.Agent13.Box33D17V22PrefixFamily
open C9Pair
open BB6.Agent13.Box33PrefixMacro
open BB6.Agent13.Box33D14Growth (z word)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

namespace M9
inductive Mode where
  | m0 | m1 | m2
inductive L where
  | l0
inductive D where
  | d0 | d1 | d2 | d3
def shape : Mode → Shape
  | .m0 => ⟨.A,false,[],[]⟩
  | .m1 => ⟨.C,true,[],[]⟩
  | .m2 => ⟨.D,true,[],[]⟩
def leftWord : L → List Bool
  | .l0 => [false,true,true]
def rightWord : D → List Bool
  | .d0 => [false,false,false]
  | .d1 => [true,false,false]
  | .d2 => [false,false,true]
  | .d3 => [true,false,true]
def rule : Mode → Option L → D → Rule Mode L D
  | .m0,none,.d0 => ⟨8,.m0,[],[.d1]⟩
  | .m0,none,.d1 => ⟨5,.m0,[.l0],[]⟩
  | .m0,none,.d2 => ⟨8,.m0,[],[.d3]⟩
  | .m0,none,.d3 => ⟨12,.m0,[],[.d0]⟩
  | .m0,some .l0,.d0 => ⟨2,.m1,[.l0],[.d1]⟩
  | .m0,some .l0,.d1 => ⟨5,.m0,[.l0,.l0],[]⟩
  | .m0,some .l0,.d2 => ⟨2,.m1,[.l0],[.d3]⟩
  | .m0,some .l0,.d3 => ⟨6,.m2,[.l0],[.d0]⟩
  | .m1,none,.d0 => ⟨6,.m0,[],[.d0]⟩
  | .m1,none,.d1 => ⟨6,.m0,[],[.d1]⟩
  | .m1,none,.d2 => ⟨6,.m0,[],[.d2]⟩
  | .m1,none,.d3 => ⟨6,.m0,[],[.d3]⟩
  | .m1,some .l0,.d0 => ⟨7,.m2,[],[.d2,.d0]⟩
  | .m1,some .l0,.d1 => ⟨7,.m2,[],[.d2,.d1]⟩
  | .m1,some .l0,.d2 => ⟨7,.m2,[],[.d2,.d2]⟩
  | .m1,some .l0,.d3 => ⟨7,.m2,[],[.d2,.d3]⟩
  | .m2,none,.d0 => ⟨6,.m0,[],[.d0]⟩
  | .m2,none,.d1 => ⟨6,.m0,[],[.d1]⟩
  | .m2,none,.d2 => ⟨6,.m0,[],[.d2]⟩
  | .m2,none,.d3 => ⟨6,.m0,[],[.d3]⟩
  | .m2,some .l0,.d0 => ⟨7,.m2,[],[.d2,.d0]⟩
  | .m2,some .l0,.d1 => ⟨7,.m2,[],[.d2,.d1]⟩
  | .m2,some .l0,.d2 => ⟨7,.m2,[],[.d2,.d2]⟩
  | .m2,some .l0,.d3 => ⟨7,.m2,[],[.d2,.d3]⟩
def spec : Spec Mode L D := ⟨shape,leftWord,rightWord,.m0,.d0,rule⟩
def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .A false c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .F true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .D false c)
  | .E,false => some (right .F false c)
  | .E,true => some (right .A true c)
  | .F,false => some (right .C true c)
  | .F,true => none
theorem positive : Positive spec := by
  intro m a d
  cases a with
  | none => cases m <;> cases d <;> decide
  | some a => cases m <;> cases a <;> cases d <;> decide

theorem sound : Sound spec step := by
  intro m a d l r
  cases a with
  | none => cases m <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]
  | some a => cases m <;> cases a <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]

theorem zero_eq : word (spec.rightWord spec.zeroDigit) z = z := by
  simp [spec,rightWord,word]

open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,2,11,24,1,13,17,13,22,4,12,0]
def table : Machine := fun s => decode (codes.getD (index s).val 0)

theorem project_step (c : BB6Coverage.Config) :
    (rawStep table c).map project = step (project c) := by
  rw [map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl

theorem never : NeverHalts table := by
  apply sourceNever table step project_step
  intro n
  have hn := neverPhase spec step sound positive zero_eq n spec.initial [] []
  change Box33PrefixMacro.run step n ⟨.A,z,false,z⟩ ≠ none
  simpa [phase,spec,shape,atShape,blocks,word] using hn

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms compatible_never
end M9

namespace M17
inductive Mode where
  | m0 | m1 | m2
inductive L where
  | l0
inductive D where
  | d0 | d1 | d2 | d3
def shape : Mode → Shape
  | .m0 => ⟨.A,false,[],[]⟩
  | .m1 => ⟨.C,true,[],[]⟩
  | .m2 => ⟨.E,true,[],[]⟩
def leftWord : L → List Bool
  | .l0 => [false,true,true]
def rightWord : D → List Bool
  | .d0 => [false,false,false]
  | .d1 => [true,false,false]
  | .d2 => [false,false,true]
  | .d3 => [true,false,true]
def rule : Mode → Option L → D → Rule Mode L D
  | .m0,none,.d0 => ⟨6,.m0,[],[.d1]⟩
  | .m0,none,.d1 => ⟨3,.m0,[.l0],[]⟩
  | .m0,none,.d2 => ⟨6,.m0,[],[.d3]⟩
  | .m0,none,.d3 => ⟨10,.m0,[],[.d0]⟩
  | .m0,some .l0,.d0 => ⟨2,.m1,[.l0],[.d1]⟩
  | .m0,some .l0,.d1 => ⟨3,.m0,[.l0,.l0],[]⟩
  | .m0,some .l0,.d2 => ⟨2,.m1,[.l0],[.d3]⟩
  | .m0,some .l0,.d3 => ⟨6,.m1,[.l0],[.d0]⟩
  | .m1,none,.d0 => ⟨4,.m0,[],[.d0]⟩
  | .m1,none,.d1 => ⟨4,.m0,[],[.d1]⟩
  | .m1,none,.d2 => ⟨4,.m0,[],[.d2]⟩
  | .m1,none,.d3 => ⟨4,.m0,[],[.d3]⟩
  | .m1,some .l0,.d0 => ⟨9,.m2,[],[.d2,.d0]⟩
  | .m1,some .l0,.d1 => ⟨9,.m2,[],[.d2,.d1]⟩
  | .m1,some .l0,.d2 => ⟨9,.m2,[],[.d2,.d2]⟩
  | .m1,some .l0,.d3 => ⟨9,.m2,[],[.d2,.d3]⟩
  | .m2,none,.d0 => ⟨4,.m0,[],[.d0]⟩
  | .m2,none,.d1 => ⟨4,.m0,[],[.d1]⟩
  | .m2,none,.d2 => ⟨4,.m0,[],[.d2]⟩
  | .m2,none,.d3 => ⟨4,.m0,[],[.d3]⟩
  | .m2,some .l0,.d0 => ⟨9,.m2,[],[.d2,.d0]⟩
  | .m2,some .l0,.d1 => ⟨9,.m2,[],[.d2,.d1]⟩
  | .m2,some .l0,.d2 => ⟨9,.m2,[],[.d2,.d2]⟩
  | .m2,some .l0,.d3 => ⟨9,.m2,[],[.d2,.d3]⟩
def spec : Spec Mode L D := ⟨shape,leftWord,rightWord,.m0,.d0,rule⟩
def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (left .C false c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .F true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (right .F true c)
  | .E,false => some (right .F false c)
  | .E,true => some (left .D false c)
  | .F,false => some (right .A false c)
  | .F,true => none
theorem positive : Positive spec := by
  intro m a d
  cases a with
  | none => cases m <;> cases d <;> decide
  | some a => cases m <;> cases a <;> cases d <;> decide

theorem sound : Sound spec step := by
  intro m a d l r
  cases a with
  | none => cases m <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]
  | some a => cases m <;> cases a <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]

theorem zero_eq : word (spec.rightWord spec.zeroDigit) z = z := by
  simp [spec,rightWord,word]

open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,9,11,24,1,13,17,24,22,13,2,0]
def table : Machine := fun s => decode (codes.getD (index s).val 0)

theorem project_step (c : BB6Coverage.Config) :
    (rawStep table c).map project = step (project c) := by
  rw [map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl

theorem never : NeverHalts table := by
  apply sourceNever table step project_step
  intro n
  have hn := neverPhase spec step sound positive zero_eq n spec.initial [] []
  change Box33PrefixMacro.run step n ⟨.A,z,false,z⟩ ≠ none
  simpa [phase,spec,shape,atShape,blocks,word] using hn

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms compatible_never
end M17

namespace M18
inductive Mode where
  | m0 | m1 | m2 | m3 | m4
inductive L where
  | l0
inductive D where
  | d0 | d1 | d2 | d3
def shape : Mode → Shape
  | .m0 => ⟨.A,false,[],[]⟩
  | .m1 => ⟨.A,true,[],[]⟩
  | .m2 => ⟨.C,true,[],[]⟩
  | .m3 => ⟨.E,true,[],[]⟩
  | .m4 => ⟨.D,true,[],[]⟩
def leftWord : L → List Bool
  | .l0 => [false,true,true]
def rightWord : D → List Bool
  | .d0 => [false,false,false]
  | .d1 => [true,false,false]
  | .d2 => [false,false,true]
  | .d3 => [true,false,true]
def rule : Mode → Option L → D → Rule Mode L D
  | .m0,none,.d0 => ⟨6,.m0,[],[.d1]⟩
  | .m0,none,.d1 => ⟨3,.m0,[.l0],[]⟩
  | .m0,none,.d2 => ⟨6,.m0,[],[.d3]⟩
  | .m0,none,.d3 => ⟨3,.m1,[.l0],[]⟩
  | .m0,some .l0,.d0 => ⟨2,.m2,[.l0],[.d1]⟩
  | .m0,some .l0,.d1 => ⟨3,.m0,[.l0,.l0],[]⟩
  | .m0,some .l0,.d2 => ⟨2,.m2,[.l0],[.d3]⟩
  | .m0,some .l0,.d3 => ⟨3,.m1,[.l0,.l0],[]⟩
  | .m1,none,.d0 => ⟨6,.m0,[],[.d0]⟩
  | .m1,none,.d1 => ⟨6,.m1,[],[.d1]⟩
  | .m1,none,.d2 => ⟨6,.m0,[],[.d2]⟩
  | .m1,none,.d3 => ⟨6,.m1,[],[.d3]⟩
  | .m1,some .l0,.d0 => ⟨2,.m3,[.l0],[.d0]⟩
  | .m1,some .l0,.d1 => ⟨2,.m4,[.l0],[.d1]⟩
  | .m1,some .l0,.d2 => ⟨2,.m3,[.l0],[.d2]⟩
  | .m1,some .l0,.d3 => ⟨2,.m4,[.l0],[.d3]⟩
  | .m2,none,.d0 => ⟨4,.m0,[],[.d0]⟩
  | .m2,none,.d1 => ⟨4,.m0,[],[.d1]⟩
  | .m2,none,.d2 => ⟨4,.m0,[],[.d2]⟩
  | .m2,none,.d3 => ⟨4,.m0,[],[.d3]⟩
  | .m2,some .l0,.d0 => ⟨3,.m4,[],[.d0,.d0]⟩
  | .m2,some .l0,.d1 => ⟨3,.m4,[],[.d0,.d1]⟩
  | .m2,some .l0,.d2 => ⟨3,.m4,[],[.d0,.d2]⟩
  | .m2,some .l0,.d3 => ⟨3,.m4,[],[.d0,.d3]⟩
  | .m3,none,.d0 => ⟨4,.m0,[],[.d0]⟩
  | .m3,none,.d1 => ⟨4,.m0,[],[.d1]⟩
  | .m3,none,.d2 => ⟨4,.m0,[],[.d2]⟩
  | .m3,none,.d3 => ⟨4,.m0,[],[.d3]⟩
  | .m3,some .l0,.d0 => ⟨3,.m4,[],[.d0,.d0]⟩
  | .m3,some .l0,.d1 => ⟨3,.m4,[],[.d0,.d1]⟩
  | .m3,some .l0,.d2 => ⟨3,.m4,[],[.d0,.d2]⟩
  | .m3,some .l0,.d3 => ⟨3,.m4,[],[.d0,.d3]⟩
  | .m4,none,.d0 => ⟨4,.m1,[],[.d0]⟩
  | .m4,none,.d1 => ⟨4,.m1,[],[.d1]⟩
  | .m4,none,.d2 => ⟨4,.m1,[],[.d2]⟩
  | .m4,none,.d3 => ⟨4,.m1,[],[.d3]⟩
  | .m4,some .l0,.d0 => ⟨3,.m4,[],[.d2,.d0]⟩
  | .m4,some .l0,.d1 => ⟨3,.m4,[],[.d2,.d1]⟩
  | .m4,some .l0,.d2 => ⟨3,.m4,[],[.d2,.d2]⟩
  | .m4,some .l0,.d3 => ⟨3,.m4,[],[.d2,.d3]⟩
def spec : Spec Mode L D := ⟨shape,leftWord,rightWord,.m0,.d0,rule⟩
def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .D true c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .F true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .D true c)
  | .E,false => some (right .F false c)
  | .E,true => some (left .D false c)
  | .F,false => some (right .A false c)
  | .F,true => none
theorem positive : Positive spec := by
  intro m a d
  cases a with
  | none => cases m <;> cases d <;> decide
  | some a => cases m <;> cases a <;> cases d <;> decide

theorem sound : Sound spec step := by
  intro m a d l r
  cases a with
  | none => cases m <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]
  | some a => cases m <;> cases a <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]

theorem zero_eq : word (spec.rightWord spec.zeroDigit) z = z := by
  simp [spec,rightWord,word]

open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,16,11,24,1,13,17,15,22,13,2,0]
def table : Machine := fun s => decode (codes.getD (index s).val 0)

theorem project_step (c : BB6Coverage.Config) :
    (rawStep table c).map project = step (project c) := by
  rw [map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl

theorem never : NeverHalts table := by
  apply sourceNever table step project_step
  intro n
  have hn := neverPhase spec step sound positive zero_eq n spec.initial [] []
  change Box33PrefixMacro.run step n ⟨.A,z,false,z⟩ ≠ none
  simpa [phase,spec,shape,atShape,blocks,word] using hn

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms compatible_never
end M18

namespace M21
inductive Mode where
  | m0 | m1 | m2
inductive L where
  | l0
inductive D where
  | d0 | d1 | d2 | d3
def shape : Mode → Shape
  | .m0 => ⟨.A,false,[],[]⟩
  | .m1 => ⟨.C,true,[],[]⟩
  | .m2 => ⟨.D,true,[],[]⟩
def leftWord : L → List Bool
  | .l0 => [false,true,true]
def rightWord : D → List Bool
  | .d0 => [false,false,false]
  | .d1 => [true,false,false]
  | .d2 => [false,true,false]
  | .d3 => [true,true,false]
def rule : Mode → Option L → D → Rule Mode L D
  | .m0,none,.d0 => ⟨6,.m0,[],[.d1]⟩
  | .m0,none,.d1 => ⟨3,.m0,[.l0],[]⟩
  | .m0,none,.d2 => ⟨6,.m0,[],[.d3]⟩
  | .m0,none,.d3 => ⟨8,.m0,[],[.d0]⟩
  | .m0,some .l0,.d0 => ⟨2,.m1,[.l0],[.d1]⟩
  | .m0,some .l0,.d1 => ⟨3,.m0,[.l0,.l0],[]⟩
  | .m0,some .l0,.d2 => ⟨2,.m1,[.l0],[.d3]⟩
  | .m0,some .l0,.d3 => ⟨4,.m2,[.l0],[.d0]⟩
  | .m1,none,.d0 => ⟨4,.m0,[],[.d0]⟩
  | .m1,none,.d1 => ⟨4,.m0,[],[.d1]⟩
  | .m1,none,.d2 => ⟨4,.m0,[],[.d2]⟩
  | .m1,none,.d3 => ⟨4,.m0,[],[.d3]⟩
  | .m1,some .l0,.d0 => ⟨7,.m2,[],[.d2,.d0]⟩
  | .m1,some .l0,.d1 => ⟨7,.m2,[],[.d2,.d1]⟩
  | .m1,some .l0,.d2 => ⟨7,.m2,[],[.d2,.d2]⟩
  | .m1,some .l0,.d3 => ⟨7,.m2,[],[.d2,.d3]⟩
  | .m2,none,.d0 => ⟨4,.m0,[],[.d0]⟩
  | .m2,none,.d1 => ⟨4,.m0,[],[.d1]⟩
  | .m2,none,.d2 => ⟨4,.m0,[],[.d2]⟩
  | .m2,none,.d3 => ⟨4,.m0,[],[.d3]⟩
  | .m2,some .l0,.d0 => ⟨7,.m2,[],[.d2,.d0]⟩
  | .m2,some .l0,.d1 => ⟨7,.m2,[],[.d2,.d1]⟩
  | .m2,some .l0,.d2 => ⟨7,.m2,[],[.d2,.d2]⟩
  | .m2,some .l0,.d3 => ⟨7,.m2,[],[.d2,.d3]⟩
def spec : Spec Mode L D := ⟨shape,leftWord,rightWord,.m0,.d0,rule⟩
def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => none
  | .B,false => some (left .C true c)
  | .B,true => some (right .F true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .D false c)
  | .E,false => some (right .F false c)
  | .E,true => some (right .C false c)
  | .F,false => some (right .A false c)
  | .F,true => some (left .D false c)
theorem positive : Positive spec := by
  intro m a d
  cases a with
  | none => cases m <;> cases d <;> decide
  | some a => cases m <;> cases a <;> cases d <;> decide

theorem sound : Sound spec step := by
  intro m a d l r
  cases a with
  | none => cases m <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]
  | some a => cases m <;> cases a <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]

theorem zero_eq : word (spec.rightWord spec.zeroDigit) z = z := by
  simp [spec,rightWord,word]

open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,0,11,24,1,13,17,13,22,10,2,13]
def table : Machine := fun s => decode (codes.getD (index s).val 0)

theorem project_step (c : BB6Coverage.Config) :
    (rawStep table c).map project = step (project c) := by
  rw [map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl

theorem never : NeverHalts table := by
  apply sourceNever table step project_step
  intro n
  have hn := neverPhase spec step sound positive zero_eq n spec.initial [] []
  change Box33PrefixMacro.run step n ⟨.A,z,false,z⟩ ≠ none
  simpa [phase,spec,shape,atShape,blocks,word] using hn

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms compatible_never
end M21

namespace M22
inductive Mode where
  | m0 | m1 | m2
inductive L where
  | l0
inductive D where
  | d0 | d1 | d2 | d3
def shape : Mode → Shape
  | .m0 => ⟨.A,false,[],[]⟩
  | .m1 => ⟨.C,true,[],[]⟩
  | .m2 => ⟨.D,true,[],[]⟩
def leftWord : L → List Bool
  | .l0 => [false,true,true]
def rightWord : D → List Bool
  | .d0 => [false,false,false]
  | .d1 => [true,false,false]
  | .d2 => [false,true,false]
  | .d3 => [true,true,false]
def rule : Mode → Option L → D → Rule Mode L D
  | .m0,none,.d0 => ⟨6,.m0,[],[.d1]⟩
  | .m0,none,.d1 => ⟨3,.m0,[.l0],[]⟩
  | .m0,none,.d2 => ⟨6,.m0,[],[.d3]⟩
  | .m0,none,.d3 => ⟨8,.m0,[],[.d0]⟩
  | .m0,some .l0,.d0 => ⟨2,.m1,[.l0],[.d1]⟩
  | .m0,some .l0,.d1 => ⟨3,.m0,[.l0,.l0],[]⟩
  | .m0,some .l0,.d2 => ⟨2,.m1,[.l0],[.d3]⟩
  | .m0,some .l0,.d3 => ⟨4,.m2,[.l0],[.d0]⟩
  | .m1,none,.d0 => ⟨4,.m0,[],[.d0]⟩
  | .m1,none,.d1 => ⟨4,.m0,[],[.d1]⟩
  | .m1,none,.d2 => ⟨4,.m0,[],[.d2]⟩
  | .m1,none,.d3 => ⟨4,.m0,[],[.d3]⟩
  | .m1,some .l0,.d0 => ⟨7,.m2,[],[.d2,.d0]⟩
  | .m1,some .l0,.d1 => ⟨7,.m2,[],[.d2,.d1]⟩
  | .m1,some .l0,.d2 => ⟨7,.m2,[],[.d2,.d2]⟩
  | .m1,some .l0,.d3 => ⟨7,.m2,[],[.d2,.d3]⟩
  | .m2,none,.d0 => ⟨4,.m0,[],[.d0]⟩
  | .m2,none,.d1 => ⟨4,.m0,[],[.d1]⟩
  | .m2,none,.d2 => ⟨4,.m0,[],[.d2]⟩
  | .m2,none,.d3 => ⟨4,.m0,[],[.d3]⟩
  | .m2,some .l0,.d0 => ⟨7,.m2,[],[.d2,.d0]⟩
  | .m2,some .l0,.d1 => ⟨7,.m2,[],[.d2,.d1]⟩
  | .m2,some .l0,.d2 => ⟨7,.m2,[],[.d2,.d2]⟩
  | .m2,some .l0,.d3 => ⟨7,.m2,[],[.d2,.d3]⟩
def spec : Spec Mode L D := ⟨shape,leftWord,rightWord,.m0,.d0,rule⟩
def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => none
  | .B,false => some (left .C true c)
  | .B,true => some (right .F true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .D false c)
  | .E,false => some (right .F false c)
  | .E,true => some (right .C false c)
  | .F,false => some (right .A false c)
  | .F,true => some (left .C false c)
theorem positive : Positive spec := by
  intro m a d
  cases a with
  | none => cases m <;> cases d <;> decide
  | some a => cases m <;> cases a <;> cases d <;> decide

theorem sound : Sound spec step := by
  intro m a d l r
  cases a with
  | none => cases m <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]
  | some a => cases m <;> cases a <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]

theorem zero_eq : word (spec.rightWord spec.zeroDigit) z = z := by
  simp [spec,rightWord,word]

open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,0,11,24,1,13,17,13,22,10,2,9]
def table : Machine := fun s => decode (codes.getD (index s).val 0)

theorem project_step (c : BB6Coverage.Config) :
    (rawStep table c).map project = step (project c) := by
  rw [map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl

theorem never : NeverHalts table := by
  apply sourceNever table step project_step
  intro n
  have hn := neverPhase spec step sound positive zero_eq n spec.initial [] []
  change Box33PrefixMacro.run step n ⟨.A,z,false,z⟩ ≠ none
  simpa [phase,spec,shape,atShape,blocks,word] using hn

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms compatible_never
end M22

namespace M25
inductive Mode where
  | m0 | m1
inductive L where
  | l0
inductive D where
  | d0 | d1 | d2 | d3
def shape : Mode → Shape
  | .m0 => ⟨.A,false,[],[]⟩
  | .m1 => ⟨.C,true,[],[]⟩
def leftWord : L → List Bool
  | .l0 => [false,true,true]
def rightWord : D → List Bool
  | .d0 => [false,false,false]
  | .d1 => [true,false,false]
  | .d2 => [false,false,true]
  | .d3 => [true,false,true]
def rule : Mode → Option L → D → Rule Mode L D
  | .m0,none,.d0 => ⟨6,.m0,[],[.d1]⟩
  | .m0,none,.d1 => ⟨3,.m0,[.l0],[]⟩
  | .m0,none,.d2 => ⟨6,.m0,[],[.d3]⟩
  | .m0,none,.d3 => ⟨10,.m0,[],[.d0]⟩
  | .m0,some .l0,.d0 => ⟨2,.m1,[.l0],[.d1]⟩
  | .m0,some .l0,.d1 => ⟨3,.m0,[.l0,.l0],[]⟩
  | .m0,some .l0,.d2 => ⟨2,.m1,[.l0],[.d3]⟩
  | .m0,some .l0,.d3 => ⟨6,.m1,[.l0],[.d0]⟩
  | .m1,none,.d0 => ⟨4,.m0,[],[.d0]⟩
  | .m1,none,.d1 => ⟨4,.m0,[],[.d1]⟩
  | .m1,none,.d2 => ⟨4,.m0,[],[.d2]⟩
  | .m1,none,.d3 => ⟨4,.m0,[],[.d3]⟩
  | .m1,some .l0,.d0 => ⟨9,.m1,[],[.d2,.d0]⟩
  | .m1,some .l0,.d1 => ⟨9,.m1,[],[.d2,.d1]⟩
  | .m1,some .l0,.d2 => ⟨9,.m1,[],[.d2,.d2]⟩
  | .m1,some .l0,.d3 => ⟨9,.m1,[],[.d2,.d3]⟩
def spec : Spec Mode L D := ⟨shape,leftWord,rightWord,.m0,.d0,rule⟩
def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (left .C false c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .F true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .E true c)
  | .E,false => some (right .F false c)
  | .E,true => some (right .A true c)
  | .F,false => some (right .A false c)
  | .F,true => none
theorem positive : Positive spec := by
  intro m a d
  cases a with
  | none => cases m <;> cases d <;> decide
  | some a => cases m <;> cases a <;> cases d <;> decide

theorem sound : Sound spec step := by
  intro m a d l r
  cases a with
  | none => cases m <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]
  | some a => cases m <;> cases a <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]

theorem zero_eq : word (spec.rightWord spec.zeroDigit) z = z := by
  simp [spec,rightWord,word]

open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,9,11,24,1,13,17,19,22,4,2,0]
def table : Machine := fun s => decode (codes.getD (index s).val 0)

theorem project_step (c : BB6Coverage.Config) :
    (rawStep table c).map project = step (project c) := by
  rw [map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl

theorem never : NeverHalts table := by
  apply sourceNever table step project_step
  intro n
  have hn := neverPhase spec step sound positive zero_eq n spec.initial [] []
  change Box33PrefixMacro.run step n ⟨.A,z,false,z⟩ ≠ none
  simpa [phase,spec,shape,atShape,blocks,word] using hn

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms compatible_never
end M25

namespace M26
inductive Mode where
  | m0 | m1 | m2
inductive L where
  | l0
inductive D where
  | d0 | d1 | d2 | d3
def shape : Mode → Shape
  | .m0 => ⟨.A,false,[],[]⟩
  | .m1 => ⟨.C,true,[],[]⟩
  | .m2 => ⟨.D,true,[],[]⟩
def leftWord : L → List Bool
  | .l0 => [false,true,true]
def rightWord : D → List Bool
  | .d0 => [false,false,false]
  | .d1 => [true,false,false]
  | .d2 => [false,false,true]
  | .d3 => [true,false,true]
def rule : Mode → Option L → D → Rule Mode L D
  | .m0,none,.d0 => ⟨6,.m0,[],[.d1]⟩
  | .m0,none,.d1 => ⟨3,.m0,[.l0],[]⟩
  | .m0,none,.d2 => ⟨6,.m0,[],[.d3]⟩
  | .m0,none,.d3 => ⟨10,.m0,[],[.d0]⟩
  | .m0,some .l0,.d0 => ⟨2,.m1,[.l0],[.d1]⟩
  | .m0,some .l0,.d1 => ⟨3,.m0,[.l0,.l0],[]⟩
  | .m0,some .l0,.d2 => ⟨2,.m1,[.l0],[.d3]⟩
  | .m0,some .l0,.d3 => ⟨6,.m1,[.l0],[.d0]⟩
  | .m1,none,.d0 => ⟨4,.m0,[],[.d0]⟩
  | .m1,none,.d1 => ⟨4,.m0,[],[.d1]⟩
  | .m1,none,.d2 => ⟨4,.m0,[],[.d2]⟩
  | .m1,none,.d3 => ⟨4,.m0,[],[.d3]⟩
  | .m1,some .l0,.d0 => ⟨7,.m2,[],[.d2,.d0]⟩
  | .m1,some .l0,.d1 => ⟨7,.m2,[],[.d2,.d1]⟩
  | .m1,some .l0,.d2 => ⟨7,.m2,[],[.d2,.d2]⟩
  | .m1,some .l0,.d3 => ⟨7,.m2,[],[.d2,.d3]⟩
  | .m2,none,.d0 => ⟨4,.m0,[],[.d0]⟩
  | .m2,none,.d1 => ⟨4,.m0,[],[.d1]⟩
  | .m2,none,.d2 => ⟨4,.m0,[],[.d2]⟩
  | .m2,none,.d3 => ⟨4,.m0,[],[.d3]⟩
  | .m2,some .l0,.d0 => ⟨7,.m2,[],[.d2,.d0]⟩
  | .m2,some .l0,.d1 => ⟨7,.m2,[],[.d2,.d1]⟩
  | .m2,some .l0,.d2 => ⟨7,.m2,[],[.d2,.d2]⟩
  | .m2,some .l0,.d3 => ⟨7,.m2,[],[.d2,.d3]⟩
def spec : Spec Mode L D := ⟨shape,leftWord,rightWord,.m0,.d0,rule⟩
def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (left .C false c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .F true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .D false c)
  | .E,false => some (right .F false c)
  | .E,true => some (right .A true c)
  | .F,false => some (right .A false c)
  | .F,true => none
theorem positive : Positive spec := by
  intro m a d
  cases a with
  | none => cases m <;> cases d <;> decide
  | some a => cases m <;> cases a <;> cases d <;> decide

theorem sound : Sound spec step := by
  intro m a d l r
  cases a with
  | none => cases m <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]
  | some a => cases m <;> cases a <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]

theorem zero_eq : word (spec.rightWord spec.zeroDigit) z = z := by
  simp [spec,rightWord,word]

open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,9,11,24,1,13,17,13,22,4,2,0]
def table : Machine := fun s => decode (codes.getD (index s).val 0)

theorem project_step (c : BB6Coverage.Config) :
    (rawStep table c).map project = step (project c) := by
  rw [map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl

theorem never : NeverHalts table := by
  apply sourceNever table step project_step
  intro n
  have hn := neverPhase spec step sound positive zero_eq n spec.initial [] []
  change Box33PrefixMacro.run step n ⟨.A,z,false,z⟩ ≠ none
  simpa [phase,spec,shape,atShape,blocks,word] using hn

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms compatible_never
end M26

namespace M27
inductive Mode where
  | m0 | m1
inductive L where
  | l0
inductive D where
  | d0 | d1 | d2 | d3
def shape : Mode → Shape
  | .m0 => ⟨.A,false,[],[]⟩
  | .m1 => ⟨.C,true,[],[]⟩
def leftWord : L → List Bool
  | .l0 => [false,true,true]
def rightWord : D → List Bool
  | .d0 => [false,false,false]
  | .d1 => [true,false,false]
  | .d2 => [false,false,true]
  | .d3 => [true,false,true]
def rule : Mode → Option L → D → Rule Mode L D
  | .m0,none,.d0 => ⟨6,.m0,[],[.d1]⟩
  | .m0,none,.d1 => ⟨3,.m0,[.l0],[]⟩
  | .m0,none,.d2 => ⟨6,.m0,[],[.d3]⟩
  | .m0,none,.d3 => ⟨10,.m0,[],[.d0]⟩
  | .m0,some .l0,.d0 => ⟨2,.m1,[.l0],[.d1]⟩
  | .m0,some .l0,.d1 => ⟨3,.m0,[.l0,.l0],[]⟩
  | .m0,some .l0,.d2 => ⟨2,.m1,[.l0],[.d3]⟩
  | .m0,some .l0,.d3 => ⟨6,.m1,[.l0],[.d0]⟩
  | .m1,none,.d0 => ⟨4,.m0,[],[.d0]⟩
  | .m1,none,.d1 => ⟨4,.m0,[],[.d1]⟩
  | .m1,none,.d2 => ⟨4,.m0,[],[.d2]⟩
  | .m1,none,.d3 => ⟨4,.m0,[],[.d3]⟩
  | .m1,some .l0,.d0 => ⟨9,.m1,[],[.d2,.d0]⟩
  | .m1,some .l0,.d1 => ⟨9,.m1,[],[.d2,.d1]⟩
  | .m1,some .l0,.d2 => ⟨9,.m1,[],[.d2,.d2]⟩
  | .m1,some .l0,.d3 => ⟨9,.m1,[],[.d2,.d3]⟩
def spec : Spec Mode L D := ⟨shape,leftWord,rightWord,.m0,.d0,rule⟩
def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (left .C false c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .F true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (right .C true c)
  | .E,false => some (right .F false c)
  | .E,true => some (right .A true c)
  | .F,false => some (right .A false c)
  | .F,true => none
theorem positive : Positive spec := by
  intro m a d
  cases a with
  | none => cases m <;> cases d <;> decide
  | some a => cases m <;> cases a <;> cases d <;> decide

theorem sound : Sound spec step := by
  intro m a d l r
  cases a with
  | none => cases m <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]
  | some a => cases m <;> cases a <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]

theorem zero_eq : word (spec.rightWord spec.zeroDigit) z = z := by
  simp [spec,rightWord,word]

open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,9,11,24,1,13,17,12,22,4,2,0]
def table : Machine := fun s => decode (codes.getD (index s).val 0)

theorem project_step (c : BB6Coverage.Config) :
    (rawStep table c).map project = step (project c) := by
  rw [map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl

theorem never : NeverHalts table := by
  apply sourceNever table step project_step
  intro n
  have hn := neverPhase spec step sound positive zero_eq n spec.initial [] []
  change Box33PrefixMacro.run step n ⟨.A,z,false,z⟩ ≠ none
  simpa [phase,spec,shape,atShape,blocks,word] using hn

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms compatible_never
end M27

namespace M28
inductive Mode where
  | m0 | m1
inductive L where
  | l0
inductive D where
  | d0 | d1 | d2 | d3
def shape : Mode → Shape
  | .m0 => ⟨.A,false,[],[]⟩
  | .m1 => ⟨.C,true,[],[]⟩
def leftWord : L → List Bool
  | .l0 => [false,true,true]
def rightWord : D → List Bool
  | .d0 => [false,false,false]
  | .d1 => [true,false,false]
  | .d2 => [false,false,true]
  | .d3 => [true,false,true]
def rule : Mode → Option L → D → Rule Mode L D
  | .m0,none,.d0 => ⟨6,.m0,[],[.d1]⟩
  | .m0,none,.d1 => ⟨3,.m0,[.l0],[]⟩
  | .m0,none,.d2 => ⟨6,.m0,[],[.d3]⟩
  | .m0,none,.d3 => ⟨10,.m0,[],[.d0]⟩
  | .m0,some .l0,.d0 => ⟨2,.m1,[.l0],[.d1]⟩
  | .m0,some .l0,.d1 => ⟨3,.m0,[.l0,.l0],[]⟩
  | .m0,some .l0,.d2 => ⟨2,.m1,[.l0],[.d3]⟩
  | .m0,some .l0,.d3 => ⟨6,.m1,[.l0],[.d0]⟩
  | .m1,none,.d0 => ⟨4,.m0,[],[.d0]⟩
  | .m1,none,.d1 => ⟨4,.m0,[],[.d1]⟩
  | .m1,none,.d2 => ⟨4,.m0,[],[.d2]⟩
  | .m1,none,.d3 => ⟨4,.m0,[],[.d3]⟩
  | .m1,some .l0,.d0 => ⟨7,.m1,[],[.d2,.d0]⟩
  | .m1,some .l0,.d1 => ⟨7,.m1,[],[.d2,.d1]⟩
  | .m1,some .l0,.d2 => ⟨7,.m1,[],[.d2,.d2]⟩
  | .m1,some .l0,.d3 => ⟨7,.m1,[],[.d2,.d3]⟩
def spec : Spec Mode L D := ⟨shape,leftWord,rightWord,.m0,.d0,rule⟩
def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (left .C false c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .F true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .C false c)
  | .E,false => some (right .F false c)
  | .E,true => some (right .A true c)
  | .F,false => some (right .A false c)
  | .F,true => none
theorem positive : Positive spec := by
  intro m a d
  cases a with
  | none => cases m <;> cases d <;> decide
  | some a => cases m <;> cases a <;> cases d <;> decide

theorem sound : Sound spec step := by
  intro m a d l r
  cases a with
  | none => cases m <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]
  | some a => cases m <;> cases a <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]

theorem zero_eq : word (spec.rightWord spec.zeroDigit) z = z := by
  simp [spec,rightWord,word]

open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,9,11,24,1,13,17,9,22,4,2,0]
def table : Machine := fun s => decode (codes.getD (index s).val 0)

theorem project_step (c : BB6Coverage.Config) :
    (rawStep table c).map project = step (project c) := by
  rw [map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl

theorem never : NeverHalts table := by
  apply sourceNever table step project_step
  intro n
  have hn := neverPhase spec step sound positive zero_eq n spec.initial [] []
  change Box33PrefixMacro.run step n ⟨.A,z,false,z⟩ ≠ none
  simpa [phase,spec,shape,atShape,blocks,word] using hn

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms compatible_never
end M28

namespace M31
inductive Mode where
  | m0 | m1 | m2
inductive L where
  | l0
inductive D where
  | d0 | d1 | d2 | d3
def shape : Mode → Shape
  | .m0 => ⟨.A,false,[],[]⟩
  | .m1 => ⟨.C,true,[],[]⟩
  | .m2 => ⟨.D,true,[],[]⟩
def leftWord : L → List Bool
  | .l0 => [false,true,true]
def rightWord : D → List Bool
  | .d0 => [false,false,false]
  | .d1 => [true,false,false]
  | .d2 => [false,true,false]
  | .d3 => [true,true,false]
def rule : Mode → Option L → D → Rule Mode L D
  | .m0,none,.d0 => ⟨6,.m0,[],[.d1]⟩
  | .m0,none,.d1 => ⟨5,.m0,[.l0],[]⟩
  | .m0,none,.d2 => ⟨6,.m0,[],[.d3]⟩
  | .m0,none,.d3 => ⟨8,.m0,[],[.d0]⟩
  | .m0,some .l0,.d0 => ⟨2,.m1,[.l0],[.d1]⟩
  | .m0,some .l0,.d1 => ⟨5,.m0,[.l0,.l0],[]⟩
  | .m0,some .l0,.d2 => ⟨2,.m1,[.l0],[.d3]⟩
  | .m0,some .l0,.d3 => ⟨4,.m2,[.l0],[.d0]⟩
  | .m1,none,.d0 => ⟨4,.m0,[],[.d0]⟩
  | .m1,none,.d1 => ⟨4,.m0,[],[.d1]⟩
  | .m1,none,.d2 => ⟨4,.m0,[],[.d2]⟩
  | .m1,none,.d3 => ⟨4,.m0,[],[.d3]⟩
  | .m1,some .l0,.d0 => ⟨7,.m2,[],[.d2,.d0]⟩
  | .m1,some .l0,.d1 => ⟨7,.m2,[],[.d2,.d1]⟩
  | .m1,some .l0,.d2 => ⟨7,.m2,[],[.d2,.d2]⟩
  | .m1,some .l0,.d3 => ⟨7,.m2,[],[.d2,.d3]⟩
  | .m2,none,.d0 => ⟨4,.m0,[],[.d0]⟩
  | .m2,none,.d1 => ⟨4,.m0,[],[.d1]⟩
  | .m2,none,.d2 => ⟨4,.m0,[],[.d2]⟩
  | .m2,none,.d3 => ⟨4,.m0,[],[.d3]⟩
  | .m2,some .l0,.d0 => ⟨7,.m2,[],[.d2,.d0]⟩
  | .m2,some .l0,.d1 => ⟨7,.m2,[],[.d2,.d1]⟩
  | .m2,some .l0,.d2 => ⟨7,.m2,[],[.d2,.d2]⟩
  | .m2,some .l0,.d3 => ⟨7,.m2,[],[.d2,.d3]⟩
def spec : Spec Mode L D := ⟨shape,leftWord,rightWord,.m0,.d0,rule⟩
def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .F true c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .C true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .D false c)
  | .E,false => some (right .F false c)
  | .E,true => some (right .C false c)
  | .F,false => some (right .A false c)
  | .F,true => none
theorem positive : Positive spec := by
  intro m a d
  cases a with
  | none => cases m <;> cases d <;> decide
  | some a => cases m <;> cases a <;> cases d <;> decide

theorem sound : Sound spec step := by
  intro m a d l r
  cases a with
  | none => cases m <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]
  | some a => cases m <;> cases a <;> cases d <;>
      simp [spec,shape,leftWord,rightWord,rule,atShape,inLeft,outLeft,blocks,Box33PrefixMacro.run,step,left,right,word]

theorem zero_eq : word (spec.rightWord spec.zeroDigit) z = z := by
  simp [spec,rightWord,word]

open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,24,11,12,1,13,17,13,22,10,2,0]
def table : Machine := fun s => decode (codes.getD (index s).val 0)

theorem project_step (c : BB6Coverage.Config) :
    (rawStep table c).map project = step (project c) := by
  rw [map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl

theorem never : NeverHalts table := by
  apply sourceNever table step project_step
  intro n
  have hn := neverPhase spec step sound positive zero_eq n spec.initial [] []
  change Box33PrefixMacro.run step n ⟨.A,z,false,z⟩ ≠ none
  simpa [phase,spec,shape,atShape,blocks,word] using hn

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms compatible_never
end M31
end BB6.Agent13.Box33D17V22PrefixFamily
