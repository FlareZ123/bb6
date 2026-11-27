import Box33ExactMacro

namespace BB6.Agent13.Box33D17V23Exact
open C9Pair
open BB6.Agent13.Box33PrefixMacro BB6.Agent13.Box33ExactMacro
open BB6.Agent13.Box33D14Growth (z word)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

namespace M1
inductive Mode where
  | m0 | m1 | m2 | m3 | m4
inductive L where
  | l0
inductive D where
  | d0 | d1 | d2 | d3
def shape : Mode → Shape
  | .m0 => ⟨.A,false,[false,false],[false,false]⟩
  | .m1 => ⟨.D,false,[false],[]⟩
  | .m2 => ⟨.E,false,[],[false]⟩
  | .m3 => ⟨.E,true,[],[false]⟩
  | .m4 => ⟨.F,true,[true],[]⟩
def leftWord : L → List Bool
  | .l0 => [true,true,true]
def rightWord : D → List Bool
  | .d0 => [false,false,false]
  | .d1 => [true,false,false]
  | .d2 => [false,true,false]
  | .d3 => [true,true,false]
def rule : Mode → Option L → Option D → Rule Mode L D
  | .m0,none,none => ⟨3,.m1,[],[.d2]⟩
  | .m0,none,some .d0 => ⟨3,.m1,[],[.d2,.d0]⟩
  | .m0,none,some .d1 => ⟨3,.m1,[],[.d2,.d1]⟩
  | .m0,none,some .d2 => ⟨3,.m1,[],[.d2,.d2]⟩
  | .m0,none,some .d3 => ⟨3,.m1,[],[.d2,.d3]⟩
  | .m0,some .l0,none => ⟨3,.m1,[.l0],[.d2]⟩
  | .m0,some .l0,some .d0 => ⟨3,.m1,[.l0],[.d2,.d0]⟩
  | .m0,some .l0,some .d1 => ⟨3,.m1,[.l0],[.d2,.d1]⟩
  | .m0,some .l0,some .d2 => ⟨3,.m1,[.l0],[.d2,.d2]⟩
  | .m0,some .l0,some .d3 => ⟨3,.m1,[.l0],[.d2,.d3]⟩
  | .m1,none,none => ⟨1,.m2,[],[]⟩
  | .m1,none,some .d0 => ⟨1,.m2,[],[.d0]⟩
  | .m1,none,some .d1 => ⟨1,.m2,[],[.d1]⟩
  | .m1,none,some .d2 => ⟨1,.m2,[],[.d2]⟩
  | .m1,none,some .d3 => ⟨1,.m2,[],[.d3]⟩
  | .m1,some .l0,none => ⟨1,.m2,[.l0],[]⟩
  | .m1,some .l0,some .d0 => ⟨1,.m2,[.l0],[.d0]⟩
  | .m1,some .l0,some .d1 => ⟨1,.m2,[.l0],[.d1]⟩
  | .m1,some .l0,some .d2 => ⟨1,.m2,[.l0],[.d2]⟩
  | .m1,some .l0,some .d3 => ⟨1,.m2,[.l0],[.d3]⟩
  | .m2,none,none => ⟨8,.m2,[],[.d1]⟩
  | .m2,none,some .d0 => ⟨8,.m2,[],[.d1]⟩
  | .m2,none,some .d1 => ⟨5,.m2,[.l0],[]⟩
  | .m2,none,some .d2 => ⟨8,.m2,[],[.d3]⟩
  | .m2,none,some .d3 => ⟨2,.m3,[],[.d3]⟩
  | .m2,some .l0,none => ⟨2,.m4,[],[.d2]⟩
  | .m2,some .l0,some .d0 => ⟨2,.m4,[],[.d2,.d0]⟩
  | .m2,some .l0,some .d1 => ⟨2,.m4,[],[.d2,.d1]⟩
  | .m2,some .l0,some .d2 => ⟨2,.m4,[],[.d2,.d2]⟩
  | .m2,some .l0,some .d3 => ⟨2,.m4,[],[.d2,.d3]⟩
  | .m3,none,none => ⟨6,.m2,[],[.d1]⟩
  | .m3,none,some .d0 => ⟨6,.m2,[],[.d1]⟩
  | .m3,none,some .d1 => ⟨3,.m2,[.l0],[]⟩
  | .m3,none,some .d2 => ⟨6,.m2,[],[.d3]⟩
  | .m3,none,some .d3 => ⟨3,.m3,[.l0],[]⟩
  | .m3,some .l0,none => ⟨6,.m4,[],[.d0,.d1]⟩
  | .m3,some .l0,some .d0 => ⟨6,.m4,[],[.d0,.d1]⟩
  | .m3,some .l0,some .d1 => ⟨3,.m2,[.l0,.l0],[]⟩
  | .m3,some .l0,some .d2 => ⟨6,.m4,[],[.d0,.d3]⟩
  | .m3,some .l0,some .d3 => ⟨3,.m3,[.l0,.l0],[]⟩
  | .m4,none,none => ⟨3,.m2,[],[]⟩
  | .m4,none,some .d0 => ⟨3,.m2,[],[.d0]⟩
  | .m4,none,some .d1 => ⟨3,.m2,[],[.d1]⟩
  | .m4,none,some .d2 => ⟨3,.m2,[],[.d2]⟩
  | .m4,none,some .d3 => ⟨3,.m2,[],[.d3]⟩
  | .m4,some .l0,none => ⟨3,.m4,[],[]⟩
  | .m4,some .l0,some .d0 => ⟨3,.m4,[],[.d0,.d0]⟩
  | .m4,some .l0,some .d1 => ⟨3,.m4,[],[.d0,.d1]⟩
  | .m4,some .l0,some .d2 => ⟨3,.m4,[],[.d0,.d2]⟩
  | .m4,some .l0,some .d3 => ⟨3,.m4,[],[.d0,.d3]⟩
def spec : ExactSpec Mode L D := ⟨shape,leftWord,rightWord,word [] z,word [] z,.m0,rule⟩
def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => none
  | .B,false => some (left .C true c)
  | .B,true => some (right .E true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .F false c)
  | .E,false => some (left .F true c)
  | .E,true => some (right .A true c)
  | .F,false => some (right .E false c)
  | .F,true => some (left .F false c)
theorem positive : ExactPositive spec := by
  intro m a d
  cases a with
  | none =>
    cases d with
    | none => cases m <;> decide
    | some d => cases m <;> cases d <;> decide
  | some a =>
    cases d with
    | none => cases m <;> cases a <;> decide
    | some d => cases m <;> cases a <;> cases d <;> decide

theorem sound : ExactSound spec step := by
  intro m a d l r
  cases a with
  | none =>
    cases d with
    | none => cases m <;> simp [spec,shape,leftWord,rightWord,rule,atShape,inStack,outStack,blocks,Box33PrefixMacro.run,step,left,right,word]
    | some d => cases m <;> cases d <;> simp [spec,shape,leftWord,rightWord,rule,atShape,inStack,outStack,blocks,Box33PrefixMacro.run,step,left,right,word]
  | some a =>
    cases d with
    | none => cases m <;> cases a <;> simp [spec,shape,leftWord,rightWord,rule,atShape,inStack,outStack,blocks,Box33PrefixMacro.run,step,left,right,word]
    | some d => cases m <;> cases a <;> cases d <;> simp [spec,shape,leftWord,rightWord,rule,atShape,inStack,outStack,blocks,Box33PrefixMacro.run,step,left,right,word]

open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,0,11,20,1,13,17,21,23,4,18,21]
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
  have hn := exactNever spec step sound positive n spec.initial [] []
  change Box33PrefixMacro.run step n ⟨.A,z,false,z⟩ ≠ none
  simpa [exactPhase,spec,shape,atShape,blocks,word] using hn

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms compatible_never
end M1

namespace M2
inductive Mode where
  | m0 | m1 | m2 | m3 | m4 | m5 | m6 | m7
inductive L where
  | l0
inductive D where
  | d0 | d1 | d2 | d3
def shape : Mode → Shape
  | .m0 => ⟨.A,false,[],[false,false]⟩
  | .m1 => ⟨.D,false,[false],[]⟩
  | .m2 => ⟨.B,false,[true],[false]⟩
  | .m3 => ⟨.E,false,[],[false]⟩
  | .m4 => ⟨.C,true,[],[true,false]⟩
  | .m5 => ⟨.E,true,[],[false]⟩
  | .m6 => ⟨.C,true,[true],[]⟩
  | .m7 => ⟨.D,true,[true,true],[]⟩
def leftWord : L → List Bool
  | .l0 => [true,true,true]
def rightWord : D → List Bool
  | .d0 => [false,false,false]
  | .d1 => [true,false,false]
  | .d2 => [false,true,false]
  | .d3 => [true,true,false]
def rule : Mode → Option L → Option D → Rule Mode L D
  | .m0,none,none => ⟨3,.m1,[],[.d2]⟩
  | .m0,none,some .d0 => ⟨3,.m1,[],[.d2,.d0]⟩
  | .m0,none,some .d1 => ⟨3,.m1,[],[.d2,.d1]⟩
  | .m0,none,some .d2 => ⟨3,.m1,[],[.d2,.d2]⟩
  | .m0,none,some .d3 => ⟨3,.m1,[],[.d2,.d3]⟩
  | .m0,some .l0,none => ⟨1,.m2,[.l0],[]⟩
  | .m0,some .l0,some .d0 => ⟨1,.m2,[.l0],[.d0]⟩
  | .m0,some .l0,some .d1 => ⟨1,.m2,[.l0],[.d1]⟩
  | .m0,some .l0,some .d2 => ⟨1,.m2,[.l0],[.d2]⟩
  | .m0,some .l0,some .d3 => ⟨1,.m2,[.l0],[.d3]⟩
  | .m1,none,none => ⟨1,.m3,[],[]⟩
  | .m1,none,some .d0 => ⟨1,.m3,[],[.d0]⟩
  | .m1,none,some .d1 => ⟨1,.m3,[],[.d1]⟩
  | .m1,none,some .d2 => ⟨1,.m3,[],[.d2]⟩
  | .m1,none,some .d3 => ⟨1,.m3,[],[.d3]⟩
  | .m1,some .l0,none => ⟨1,.m3,[.l0],[]⟩
  | .m1,some .l0,some .d0 => ⟨1,.m3,[.l0],[.d0]⟩
  | .m1,some .l0,some .d1 => ⟨1,.m3,[.l0],[.d1]⟩
  | .m1,some .l0,some .d2 => ⟨1,.m3,[.l0],[.d2]⟩
  | .m1,some .l0,some .d3 => ⟨1,.m3,[.l0],[.d3]⟩
  | .m2,none,none => ⟨2,.m1,[],[.d2]⟩
  | .m2,none,some .d0 => ⟨2,.m1,[],[.d2,.d0]⟩
  | .m2,none,some .d1 => ⟨2,.m1,[],[.d2,.d1]⟩
  | .m2,none,some .d2 => ⟨2,.m1,[],[.d2,.d2]⟩
  | .m2,none,some .d3 => ⟨2,.m1,[],[.d2,.d3]⟩
  | .m2,some .l0,none => ⟨1,.m4,[.l0],[]⟩
  | .m2,some .l0,some .d0 => ⟨1,.m4,[.l0],[.d0]⟩
  | .m2,some .l0,some .d1 => ⟨1,.m4,[.l0],[.d1]⟩
  | .m2,some .l0,some .d2 => ⟨1,.m4,[.l0],[.d2]⟩
  | .m2,some .l0,some .d3 => ⟨1,.m4,[.l0],[.d3]⟩
  | .m3,none,none => ⟨8,.m3,[],[.d1]⟩
  | .m3,none,some .d0 => ⟨8,.m3,[],[.d1]⟩
  | .m3,none,some .d1 => ⟨5,.m3,[.l0],[]⟩
  | .m3,none,some .d2 => ⟨8,.m3,[],[.d3]⟩
  | .m3,none,some .d3 => ⟨2,.m5,[],[.d3]⟩
  | .m3,some .l0,none => ⟨2,.m6,[],[.d2]⟩
  | .m3,some .l0,some .d0 => ⟨2,.m6,[],[.d2,.d0]⟩
  | .m3,some .l0,some .d1 => ⟨2,.m6,[],[.d2,.d1]⟩
  | .m3,some .l0,some .d2 => ⟨2,.m6,[],[.d2,.d2]⟩
  | .m3,some .l0,some .d3 => ⟨2,.m6,[],[.d2,.d3]⟩
  | .m4,none,none => ⟨1,.m1,[],[.d2]⟩
  | .m4,none,some .d0 => ⟨1,.m1,[],[.d2,.d0]⟩
  | .m4,none,some .d1 => ⟨1,.m1,[],[.d2,.d1]⟩
  | .m4,none,some .d2 => ⟨1,.m1,[],[.d2,.d2]⟩
  | .m4,none,some .d3 => ⟨1,.m1,[],[.d2,.d3]⟩
  | .m4,some .l0,none => ⟨1,.m7,[],[.d2]⟩
  | .m4,some .l0,some .d0 => ⟨1,.m7,[],[.d2,.d0]⟩
  | .m4,some .l0,some .d1 => ⟨1,.m7,[],[.d2,.d1]⟩
  | .m4,some .l0,some .d2 => ⟨1,.m7,[],[.d2,.d2]⟩
  | .m4,some .l0,some .d3 => ⟨1,.m7,[],[.d2,.d3]⟩
  | .m5,none,none => ⟨3,.m6,[],[.d1]⟩
  | .m5,none,some .d0 => ⟨3,.m6,[],[.d1]⟩
  | .m5,none,some .d1 => ⟨3,.m3,[.l0],[]⟩
  | .m5,none,some .d2 => ⟨3,.m6,[],[.d3]⟩
  | .m5,none,some .d3 => ⟨3,.m5,[.l0],[]⟩
  | .m5,some .l0,none => ⟨3,.m6,[.l0],[.d1]⟩
  | .m5,some .l0,some .d0 => ⟨3,.m6,[.l0],[.d1]⟩
  | .m5,some .l0,some .d1 => ⟨3,.m3,[.l0,.l0],[]⟩
  | .m5,some .l0,some .d2 => ⟨3,.m6,[.l0],[.d3]⟩
  | .m5,some .l0,some .d3 => ⟨3,.m5,[.l0,.l0],[]⟩
  | .m6,none,none => ⟨3,.m3,[],[]⟩
  | .m6,none,some .d0 => ⟨3,.m3,[],[.d0]⟩
  | .m6,none,some .d1 => ⟨3,.m3,[],[.d1]⟩
  | .m6,none,some .d2 => ⟨3,.m3,[],[.d2]⟩
  | .m6,none,some .d3 => ⟨3,.m3,[],[.d3]⟩
  | .m6,some .l0,none => ⟨3,.m6,[],[]⟩
  | .m6,some .l0,some .d0 => ⟨3,.m6,[],[.d0,.d0]⟩
  | .m6,some .l0,some .d1 => ⟨3,.m6,[],[.d0,.d1]⟩
  | .m6,some .l0,some .d2 => ⟨3,.m6,[],[.d0,.d2]⟩
  | .m6,some .l0,some .d3 => ⟨3,.m6,[],[.d0,.d3]⟩
  | .m7,none,none => ⟨3,.m1,[],[]⟩
  | .m7,none,some .d0 => ⟨3,.m1,[],[.d0,.d0]⟩
  | .m7,none,some .d1 => ⟨3,.m1,[],[.d0,.d1]⟩
  | .m7,none,some .d2 => ⟨3,.m1,[],[.d0,.d2]⟩
  | .m7,none,some .d3 => ⟨3,.m1,[],[.d0,.d3]⟩
  | .m7,some .l0,none => ⟨3,.m7,[],[]⟩
  | .m7,some .l0,some .d0 => ⟨3,.m7,[],[.d0,.d0]⟩
  | .m7,some .l0,some .d1 => ⟨3,.m7,[],[.d0,.d1]⟩
  | .m7,some .l0,some .d2 => ⟨3,.m7,[],[.d0,.d2]⟩
  | .m7,some .l0,some .d3 => ⟨3,.m7,[],[.d0,.d3]⟩
def spec : ExactSpec Mode L D := ⟨shape,leftWord,rightWord,word [] z,word [] z,.m0,rule⟩
def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => none
  | .B,false => some (left .C true c)
  | .B,true => some (right .E true c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .F false c)
  | .E,false => some (left .F true c)
  | .E,true => some (right .A true c)
  | .F,false => some (right .E false c)
  | .F,true => some (left .C false c)
theorem positive : ExactPositive spec := by
  intro m a d
  cases a with
  | none =>
    cases d with
    | none => cases m <;> decide
    | some d => cases m <;> cases d <;> decide
  | some a =>
    cases d with
    | none => cases m <;> cases a <;> decide
    | some d => cases m <;> cases a <;> cases d <;> decide

theorem sound : ExactSound spec step := by
  intro m a d l r
  cases a with
  | none =>
    cases d with
    | none => cases m <;> simp [spec,shape,leftWord,rightWord,rule,atShape,inStack,outStack,blocks,Box33PrefixMacro.run,step,left,right,word]
    | some d => cases m <;> cases d <;> simp [spec,shape,leftWord,rightWord,rule,atShape,inStack,outStack,blocks,Box33PrefixMacro.run,step,left,right,word]
  | some a =>
    cases d with
    | none => cases m <;> cases a <;> simp [spec,shape,leftWord,rightWord,rule,atShape,inStack,outStack,blocks,Box33PrefixMacro.run,step,left,right,word]
    | some d => cases m <;> cases a <;> cases d <;> simp [spec,shape,leftWord,rightWord,rule,atShape,inStack,outStack,blocks,Box33PrefixMacro.run,step,left,right,word]

open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,0,11,20,1,13,17,21,23,4,18,9]
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
  have hn := exactNever spec step sound positive n spec.initial [] []
  change Box33PrefixMacro.run step n ⟨.A,z,false,z⟩ ≠ none
  simpa [exactPhase,spec,shape,atShape,blocks,word] using hn

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms compatible_never
end M2

namespace M3
inductive Mode where
  | m0 | m1 | m2 | m3
inductive L where
  | l0
inductive D where
  | d0 | d1 | d2 | d3
def shape : Mode → Shape
  | .m0 => ⟨.A,false,[false,false],[false]⟩
  | .m1 => ⟨.E,false,[],[]⟩
  | .m2 => ⟨.E,true,[],[]⟩
  | .m3 => ⟨.F,true,[],[]⟩
def leftWord : L → List Bool
  | .l0 => [true,true,true]
def rightWord : D → List Bool
  | .d0 => [false,false,false]
  | .d1 => [true,true,false]
  | .d2 => [false,false,true]
  | .d3 => [true,true,true]
def rule : Mode → Option L → Option D → Rule Mode L D
  | .m0,none,none => ⟨4,.m1,[],[.d2]⟩
  | .m0,none,some .d0 => ⟨4,.m1,[],[.d2,.d0]⟩
  | .m0,none,some .d1 => ⟨4,.m1,[],[.d2,.d1]⟩
  | .m0,none,some .d2 => ⟨4,.m1,[],[.d2,.d2]⟩
  | .m0,none,some .d3 => ⟨4,.m1,[],[.d2,.d3]⟩
  | .m0,some .l0,none => ⟨4,.m1,[.l0],[.d2]⟩
  | .m0,some .l0,some .d0 => ⟨4,.m1,[.l0],[.d2,.d0]⟩
  | .m0,some .l0,some .d1 => ⟨4,.m1,[.l0],[.d2,.d1]⟩
  | .m0,some .l0,some .d2 => ⟨4,.m1,[.l0],[.d2,.d2]⟩
  | .m0,some .l0,some .d3 => ⟨4,.m1,[.l0],[.d2,.d3]⟩
  | .m1,none,none => ⟨10,.m1,[],[.d1]⟩
  | .m1,none,some .d0 => ⟨10,.m1,[],[.d1]⟩
  | .m1,none,some .d1 => ⟨5,.m1,[.l0],[]⟩
  | .m1,none,some .d2 => ⟨10,.m1,[],[.d3]⟩
  | .m1,none,some .d3 => ⟨2,.m2,[],[.d3]⟩
  | .m1,some .l0,none => ⟨3,.m3,[],[.d2]⟩
  | .m1,some .l0,some .d0 => ⟨3,.m3,[],[.d2,.d0]⟩
  | .m1,some .l0,some .d1 => ⟨3,.m3,[],[.d2,.d1]⟩
  | .m1,some .l0,some .d2 => ⟨3,.m3,[],[.d2,.d2]⟩
  | .m1,some .l0,some .d3 => ⟨3,.m3,[],[.d2,.d3]⟩
  | .m2,none,none => ⟨6,.m3,[],[.d1]⟩
  | .m2,none,some .d0 => ⟨6,.m3,[],[.d1]⟩
  | .m2,none,some .d1 => ⟨3,.m1,[.l0],[]⟩
  | .m2,none,some .d2 => ⟨6,.m3,[],[.d3]⟩
  | .m2,none,some .d3 => ⟨3,.m2,[.l0],[]⟩
  | .m2,some .l0,none => ⟨6,.m3,[.l0],[.d1]⟩
  | .m2,some .l0,some .d0 => ⟨6,.m3,[.l0],[.d1]⟩
  | .m2,some .l0,some .d1 => ⟨3,.m1,[.l0,.l0],[]⟩
  | .m2,some .l0,some .d2 => ⟨6,.m3,[.l0],[.d3]⟩
  | .m2,some .l0,some .d3 => ⟨3,.m2,[.l0,.l0],[]⟩
  | .m3,none,none => ⟨2,.m1,[],[]⟩
  | .m3,none,some .d0 => ⟨2,.m1,[],[.d0]⟩
  | .m3,none,some .d1 => ⟨2,.m1,[],[.d1]⟩
  | .m3,none,some .d2 => ⟨2,.m1,[],[.d2]⟩
  | .m3,none,some .d3 => ⟨2,.m1,[],[.d3]⟩
  | .m3,some .l0,none => ⟨3,.m3,[],[]⟩
  | .m3,some .l0,some .d0 => ⟨3,.m3,[],[.d0,.d0]⟩
  | .m3,some .l0,some .d1 => ⟨3,.m3,[],[.d0,.d1]⟩
  | .m3,some .l0,some .d2 => ⟨3,.m3,[],[.d0,.d2]⟩
  | .m3,some .l0,some .d3 => ⟨3,.m3,[],[.d0,.d3]⟩
def spec : ExactSpec Mode L D := ⟨shape,leftWord,rightWord,word [] z,word [] z,.m0,rule⟩
def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (right .D true c)
  | .B,false => some (left .C true c)
  | .B,true => none
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (right .E true c)
  | .E,false => some (left .F true c)
  | .E,true => some (right .A true c)
  | .F,false => some (right .E false c)
  | .F,true => some (left .F false c)
theorem positive : ExactPositive spec := by
  intro m a d
  cases a with
  | none =>
    cases d with
    | none => cases m <;> decide
    | some d => cases m <;> cases d <;> decide
  | some a =>
    cases d with
    | none => cases m <;> cases a <;> decide
    | some d => cases m <;> cases a <;> cases d <;> decide

theorem sound : ExactSound spec step := by
  intro m a d l r
  cases a with
  | none =>
    cases d with
    | none => cases m <;> simp [spec,shape,leftWord,rightWord,rule,atShape,inStack,outStack,blocks,Box33PrefixMacro.run,step,left,right,word]
    | some d => cases m <;> cases d <;> simp [spec,shape,leftWord,rightWord,rule,atShape,inStack,outStack,blocks,Box33PrefixMacro.run,step,left,right,word]
  | some a =>
    cases d with
    | none => cases m <;> cases a <;> simp [spec,shape,leftWord,rightWord,rule,atShape,inStack,outStack,blocks,Box33PrefixMacro.run,step,left,right,word]
    | some d => cases m <;> cases a <;> cases d <;> simp [spec,shape,leftWord,rightWord,rule,atShape,inStack,outStack,blocks,Box33PrefixMacro.run,step,left,right,word]

open BB6Coverage
open Box17 (index decode)
def codes : List (Fin 25) := [8,16,11,0,1,13,17,20,23,4,18,21]
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
  have hn := exactNever spec step sound positive n spec.initial [] []
  change Box33PrefixMacro.run step n ⟨.A,z,false,z⟩ ≠ none
  simpa [exactPhase,spec,shape,atShape,blocks,word] using hn

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms compatible_never
end M3
end BB6.Agent13.Box33D17V23Exact
