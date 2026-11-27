import Box33PrefixMacro

namespace BB6.Agent13.Box33D17V22PrefixExtra
open C9Pair
open BB6.Agent13.Box33PrefixMacro
open BB6.Agent13.Box33D14Growth (z word)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

namespace M29
inductive Mode where
  | m0 | m1 | m2 | m3 | m4 | m5 | m6 | m7
inductive L where
  | l0
inductive D where
  | d0 | d1 | d2
def shape : Mode → Shape
  | .m0 => ⟨.A,false,[],[false]⟩
  | .m1 => ⟨.B,false,[true],[]⟩
  | .m2 => ⟨.C,true,[],[true]⟩
  | .m3 => ⟨.A,false,[],[true]⟩
  | .m4 => ⟨.D,false,[true],[]⟩
  | .m5 => ⟨.B,true,[true],[]⟩
  | .m6 => ⟨.F,true,[],[false]⟩
  | .m7 => ⟨.A,true,[],[false]⟩
def leftWord : L → List Bool
  | .l0 => [false,true]
def rightWord : D → List Bool
  | .d0 => [false,false]
  | .d1 => [false,true]
  | .d2 => [true,false]
def rule : Mode → Option L → D → Rule Mode L D
  | .m0,none,.d0 => ⟨14,.m0,[.l0],[]⟩
  | .m0,none,.d1 => ⟨22,.m0,[],[.d2]⟩
  | .m0,none,.d2 => ⟨1,.m1,[],[.d2]⟩
  | .m0,some .l0,.d0 => ⟨1,.m1,[.l0],[.d0]⟩
  | .m0,some .l0,.d1 => ⟨1,.m1,[.l0],[.d1]⟩
  | .m0,some .l0,.d2 => ⟨1,.m1,[.l0],[.d2]⟩
  | .m1,none,.d0 => ⟨13,.m0,[.l0],[]⟩
  | .m1,none,.d1 => ⟨21,.m0,[],[.d2]⟩
  | .m1,none,.d2 => ⟨1,.m2,[],[.d2]⟩
  | .m1,some .l0,.d0 => ⟨1,.m2,[.l0],[.d0]⟩
  | .m1,some .l0,.d1 => ⟨1,.m2,[.l0],[.d1]⟩
  | .m1,some .l0,.d2 => ⟨1,.m2,[.l0],[.d2]⟩
  | .m2,none,.d0 => ⟨12,.m0,[.l0],[]⟩
  | .m2,none,.d1 => ⟨20,.m0,[],[.d2]⟩
  | .m2,none,.d2 => ⟨4,.m3,[],[.d2]⟩
  | .m2,some .l0,.d0 => ⟨1,.m4,[],[.d1,.d0]⟩
  | .m2,some .l0,.d1 => ⟨1,.m4,[],[.d1,.d1]⟩
  | .m2,some .l0,.d2 => ⟨1,.m4,[],[.d1,.d2]⟩
  | .m3,none,.d0 => ⟨8,.m0,[.l0],[]⟩
  | .m3,none,.d1 => ⟨8,.m3,[.l0],[]⟩
  | .m3,none,.d2 => ⟨1,.m5,[],[.d2]⟩
  | .m3,some .l0,.d0 => ⟨3,.m4,[],[.d2,.d0]⟩
  | .m3,some .l0,.d1 => ⟨3,.m4,[],[.d2,.d1]⟩
  | .m3,some .l0,.d2 => ⟨3,.m4,[],[.d2,.d2]⟩
  | .m4,none,.d0 => ⟨5,.m0,[],[.d0]⟩
  | .m4,none,.d1 => ⟨5,.m0,[],[.d1]⟩
  | .m4,none,.d2 => ⟨5,.m0,[],[.d2]⟩
  | .m4,some .l0,.d0 => ⟨2,.m4,[],[.d0,.d0]⟩
  | .m4,some .l0,.d1 => ⟨2,.m4,[],[.d0,.d1]⟩
  | .m4,some .l0,.d2 => ⟨2,.m4,[],[.d0,.d2]⟩
  | .m5,none,.d0 => ⟨7,.m0,[.l0],[]⟩
  | .m5,none,.d1 => ⟨7,.m3,[.l0],[]⟩
  | .m5,none,.d2 => ⟨1,.m6,[],[.d2]⟩
  | .m5,some .l0,.d0 => ⟨2,.m4,[],[.d2,.d0]⟩
  | .m5,some .l0,.d1 => ⟨2,.m4,[],[.d2,.d1]⟩
  | .m5,some .l0,.d2 => ⟨2,.m4,[],[.d2,.d2]⟩
  | .m6,none,.d0 => ⟨6,.m0,[.l0],[]⟩
  | .m6,none,.d1 => ⟨6,.m3,[.l0],[]⟩
  | .m6,none,.d2 => ⟨4,.m7,[],[.d2]⟩
  | .m6,some .l0,.d0 => ⟨1,.m4,[],[.d2,.d0]⟩
  | .m6,some .l0,.d1 => ⟨1,.m4,[],[.d2,.d1]⟩
  | .m6,some .l0,.d2 => ⟨1,.m4,[],[.d2,.d2]⟩
  | .m7,none,.d0 => ⟨2,.m0,[.l0],[]⟩
  | .m7,none,.d1 => ⟨2,.m3,[.l0],[]⟩
  | .m7,none,.d2 => ⟨2,.m7,[.l0],[]⟩
  | .m7,some .l0,.d0 => ⟨2,.m0,[.l0,.l0],[]⟩
  | .m7,some .l0,.d1 => ⟨2,.m3,[.l0,.l0],[]⟩
  | .m7,some .l0,.d2 => ⟨2,.m7,[.l0,.l0],[]⟩
def spec : Spec Mode L D := ⟨shape,leftWord,rightWord,.m0,.d0,rule⟩
def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .F true c)
  | .B,false => some (left .C true c)
  | .B,true => some (left .F false c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => none
  | .E,false => some (right .F false c)
  | .E,true => some (left .D false c)
  | .F,false => some (right .A false c)
  | .F,true => some (left .D true c)
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
def codes : List (Fin 25) := [8,24,11,21,1,13,17,0,22,13,2,15]
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
end M29

namespace M30
inductive Mode where
  | m0 | m1 | m2 | m3 | m4 | m5 | m6 | m7
inductive L where
  | l0
inductive D where
  | d0 | d1 | d2
def shape : Mode → Shape
  | .m0 => ⟨.A,false,[],[false]⟩
  | .m1 => ⟨.B,false,[true],[]⟩
  | .m2 => ⟨.C,true,[],[true]⟩
  | .m3 => ⟨.A,false,[],[true]⟩
  | .m4 => ⟨.D,false,[true],[]⟩
  | .m5 => ⟨.B,true,[true],[]⟩
  | .m6 => ⟨.D,true,[],[false]⟩
  | .m7 => ⟨.A,true,[],[false]⟩
def leftWord : L → List Bool
  | .l0 => [false,true]
def rightWord : D → List Bool
  | .d0 => [false,false]
  | .d1 => [false,true]
  | .d2 => [true,false]
def rule : Mode → Option L → D → Rule Mode L D
  | .m0,none,.d0 => ⟨14,.m0,[.l0],[]⟩
  | .m0,none,.d1 => ⟨22,.m0,[],[.d2]⟩
  | .m0,none,.d2 => ⟨1,.m1,[],[.d2]⟩
  | .m0,some .l0,.d0 => ⟨1,.m1,[.l0],[.d0]⟩
  | .m0,some .l0,.d1 => ⟨1,.m1,[.l0],[.d1]⟩
  | .m0,some .l0,.d2 => ⟨1,.m1,[.l0],[.d2]⟩
  | .m1,none,.d0 => ⟨13,.m0,[.l0],[]⟩
  | .m1,none,.d1 => ⟨21,.m0,[],[.d2]⟩
  | .m1,none,.d2 => ⟨1,.m2,[],[.d2]⟩
  | .m1,some .l0,.d0 => ⟨1,.m2,[.l0],[.d0]⟩
  | .m1,some .l0,.d1 => ⟨1,.m2,[.l0],[.d1]⟩
  | .m1,some .l0,.d2 => ⟨1,.m2,[.l0],[.d2]⟩
  | .m2,none,.d0 => ⟨12,.m0,[.l0],[]⟩
  | .m2,none,.d1 => ⟨20,.m0,[],[.d2]⟩
  | .m2,none,.d2 => ⟨4,.m3,[],[.d2]⟩
  | .m2,some .l0,.d0 => ⟨1,.m4,[],[.d1,.d0]⟩
  | .m2,some .l0,.d1 => ⟨1,.m4,[],[.d1,.d1]⟩
  | .m2,some .l0,.d2 => ⟨1,.m4,[],[.d1,.d2]⟩
  | .m3,none,.d0 => ⟨8,.m0,[.l0],[]⟩
  | .m3,none,.d1 => ⟨8,.m3,[.l0],[]⟩
  | .m3,none,.d2 => ⟨1,.m5,[],[.d2]⟩
  | .m3,some .l0,.d0 => ⟨3,.m4,[],[.d2,.d0]⟩
  | .m3,some .l0,.d1 => ⟨3,.m4,[],[.d2,.d1]⟩
  | .m3,some .l0,.d2 => ⟨3,.m4,[],[.d2,.d2]⟩
  | .m4,none,.d0 => ⟨5,.m0,[],[.d0]⟩
  | .m4,none,.d1 => ⟨5,.m0,[],[.d1]⟩
  | .m4,none,.d2 => ⟨5,.m0,[],[.d2]⟩
  | .m4,some .l0,.d0 => ⟨2,.m4,[],[.d0,.d0]⟩
  | .m4,some .l0,.d1 => ⟨2,.m4,[],[.d0,.d1]⟩
  | .m4,some .l0,.d2 => ⟨2,.m4,[],[.d0,.d2]⟩
  | .m5,none,.d0 => ⟨7,.m0,[.l0],[]⟩
  | .m5,none,.d1 => ⟨7,.m3,[.l0],[]⟩
  | .m5,none,.d2 => ⟨1,.m6,[],[.d2]⟩
  | .m5,some .l0,.d0 => ⟨2,.m4,[],[.d2,.d0]⟩
  | .m5,some .l0,.d1 => ⟨2,.m4,[],[.d2,.d1]⟩
  | .m5,some .l0,.d2 => ⟨2,.m4,[],[.d2,.d2]⟩
  | .m6,none,.d0 => ⟨6,.m0,[.l0],[]⟩
  | .m6,none,.d1 => ⟨6,.m3,[.l0],[]⟩
  | .m6,none,.d2 => ⟨4,.m7,[],[.d2]⟩
  | .m6,some .l0,.d0 => ⟨1,.m4,[],[.d2,.d0]⟩
  | .m6,some .l0,.d1 => ⟨1,.m4,[],[.d2,.d1]⟩
  | .m6,some .l0,.d2 => ⟨1,.m4,[],[.d2,.d2]⟩
  | .m7,none,.d0 => ⟨2,.m0,[.l0],[]⟩
  | .m7,none,.d1 => ⟨2,.m3,[.l0],[]⟩
  | .m7,none,.d2 => ⟨2,.m7,[.l0],[]⟩
  | .m7,some .l0,.d0 => ⟨2,.m0,[.l0,.l0],[]⟩
  | .m7,some .l0,.d1 => ⟨2,.m3,[.l0,.l0],[]⟩
  | .m7,some .l0,.d2 => ⟨2,.m7,[.l0,.l0],[]⟩
def spec : Spec Mode L D := ⟨shape,leftWord,rightWord,.m0,.d0,rule⟩
def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .F true c)
  | .B,false => some (left .C true c)
  | .B,true => some (left .D false c)
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
def codes : List (Fin 25) := [8,24,11,13,1,13,17,15,22,13,2,0]
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
end M30
end BB6.Agent13.Box33D17V22PrefixExtra
