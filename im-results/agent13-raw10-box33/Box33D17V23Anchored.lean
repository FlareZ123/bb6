import Box33ExactMacro

namespace BB6.Agent13.Box33D17V23Anchored
open C9Pair
open BB6.Agent13.Box33PrefixMacro BB6.Agent13.Box33ExactMacro
open BB6.Agent13.Box33D14Growth (z word)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

namespace M0
inductive Mode where
  | m0 | m1 | m2
inductive L where
  | l0 | l1 | l2 | l3
inductive D where
  | d0
def shape : Mode → Shape
  | .m0 => ⟨.E,false,[],[]⟩
  | .m1 => ⟨.B,true,[],[]⟩
  | .m2 => ⟨.D,true,[],[]⟩
def leftWord : L → List Bool
  | .l0 => [false,false,false]
  | .l1 => [true,false,false]
  | .l2 => [false,true,false]
  | .l3 => [true,true,false]
def rightWord : D → List Bool
  | .d0 => [true,true,true]
def rule : Mode → Option L → Option D → Rule Mode L D
  | .m0,none,none => ⟨6,.m0,[.l1],[]⟩
  | .m0,none,some .d0 => ⟨4,.m1,[.l1],[.d0]⟩
  | .m0,some .l0,none => ⟨6,.m0,[.l1],[]⟩
  | .m0,some .l0,some .d0 => ⟨4,.m1,[.l1],[.d0]⟩
  | .m0,some .l1,none => ⟨6,.m0,[.l2],[]⟩
  | .m0,some .l1,some .d0 => ⟨4,.m2,[.l2],[.d0]⟩
  | .m0,some .l2,none => ⟨6,.m0,[.l3],[]⟩
  | .m0,some .l2,some .d0 => ⟨4,.m1,[.l3],[.d0]⟩
  | .m0,some .l3,none => ⟨3,.m0,[],[.d0]⟩
  | .m0,some .l3,some .d0 => ⟨3,.m0,[],[.d0,.d0]⟩
  | .m1,none,none => ⟨2,.m0,[],[]⟩
  | .m1,none,some .d0 => ⟨3,.m2,[],[]⟩
  | .m1,some .l0,none => ⟨2,.m0,[.l0],[]⟩
  | .m1,some .l0,some .d0 => ⟨3,.m2,[.l0,.l0],[]⟩
  | .m1,some .l1,none => ⟨2,.m0,[.l1],[]⟩
  | .m1,some .l1,some .d0 => ⟨3,.m2,[.l0,.l1],[]⟩
  | .m1,some .l2,none => ⟨2,.m0,[.l2],[]⟩
  | .m1,some .l2,some .d0 => ⟨3,.m2,[.l0,.l2],[]⟩
  | .m1,some .l3,none => ⟨2,.m0,[.l3],[]⟩
  | .m1,some .l3,some .d0 => ⟨3,.m2,[.l0,.l3],[]⟩
  | .m2,none,none => ⟨2,.m0,[],[]⟩
  | .m2,none,some .d0 => ⟨3,.m2,[],[]⟩
  | .m2,some .l0,none => ⟨2,.m0,[.l0],[]⟩
  | .m2,some .l0,some .d0 => ⟨3,.m2,[.l0,.l0],[]⟩
  | .m2,some .l1,none => ⟨2,.m0,[.l1],[]⟩
  | .m2,some .l1,some .d0 => ⟨3,.m2,[.l0,.l1],[]⟩
  | .m2,some .l2,none => ⟨2,.m0,[.l2],[]⟩
  | .m2,some .l2,some .d0 => ⟨3,.m2,[.l0,.l2],[]⟩
  | .m2,some .l3,none => ⟨2,.m0,[.l3],[]⟩
  | .m2,some .l3,some .d0 => ⟨3,.m2,[.l0,.l3],[]⟩
def spec : ExactSpec Mode L D := ⟨shape,leftWord,rightWord,word [] z,word [false,false,true] z,.m0,rule⟩
def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (left .E true c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .D false c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (right .D false c)
  | .E,false => some (left .F true c)
  | .E,true => none
  | .F,false => some (right .F false c)
  | .F,true => some (left .A true c)
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
def codes : List (Fin 25) := [8,19,11,14,1,13,17,14,23,0,22,3]
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
  let k : Nat := 4
  have hi : Box33PrefixMacro.run step k (project BB6Coverage.blank) =
      some (exactPhase spec spec.initial [] []) := by
    simp [k,project,Box33Source.project,BB6Coverage.blank,Box33Source.q,Box33Source.perm,exactPhase,spec,shape,atShape,blocks,leftWord,rightWord,word,Box33PrefixMacro.run,step,left,right]
  intro h
  have hc := exactNever spec step sound positive (n-k) spec.initial [] []
  by_cases hn : n≤k
  · rw [←show n+(k-n)=k by omega,Box33PrefixMacro.run_add,h] at hi
    contradiction
  · rw [←show k+(n-k)=n by omega,Box33PrefixMacro.run_add,hi,Option.bind_some] at h
    exact hc h

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms compatible_never
end M0

namespace M4
inductive Mode where
  | m0 | m1
inductive L where
  | l0 | l1 | l2 | l3
inductive D where
  | d0
def shape : Mode → Shape
  | .m0 => ⟨.E,false,[],[]⟩
  | .m1 => ⟨.D,true,[],[]⟩
def leftWord : L → List Bool
  | .l0 => [false,false,false]
  | .l1 => [true,false,false]
  | .l2 => [false,true,false]
  | .l3 => [true,true,false]
def rightWord : D → List Bool
  | .d0 => [true,true,true]
def rule : Mode → Option L → Option D → Rule Mode L D
  | .m0,none,none => ⟨4,.m0,[.l1],[]⟩
  | .m0,none,some .d0 => ⟨2,.m1,[.l1],[.d0]⟩
  | .m0,some .l0,none => ⟨4,.m0,[.l1],[]⟩
  | .m0,some .l0,some .d0 => ⟨2,.m1,[.l1],[.d0]⟩
  | .m0,some .l1,none => ⟨6,.m0,[.l2],[]⟩
  | .m0,some .l1,some .d0 => ⟨4,.m1,[.l2],[.d0]⟩
  | .m0,some .l2,none => ⟨4,.m0,[.l3],[]⟩
  | .m0,some .l2,some .d0 => ⟨2,.m1,[.l3],[.d0]⟩
  | .m0,some .l3,none => ⟨3,.m0,[],[.d0]⟩
  | .m0,some .l3,some .d0 => ⟨3,.m0,[],[.d0,.d0]⟩
  | .m1,none,none => ⟨2,.m0,[],[]⟩
  | .m1,none,some .d0 => ⟨3,.m1,[],[]⟩
  | .m1,some .l0,none => ⟨2,.m0,[.l0],[]⟩
  | .m1,some .l0,some .d0 => ⟨3,.m1,[.l0,.l0],[]⟩
  | .m1,some .l1,none => ⟨2,.m0,[.l1],[]⟩
  | .m1,some .l1,some .d0 => ⟨3,.m1,[.l0,.l1],[]⟩
  | .m1,some .l2,none => ⟨2,.m0,[.l2],[]⟩
  | .m1,some .l2,some .d0 => ⟨3,.m1,[.l0,.l2],[]⟩
  | .m1,some .l3,none => ⟨2,.m0,[.l3],[]⟩
  | .m1,some .l3,some .d0 => ⟨3,.m1,[.l0,.l3],[]⟩
def spec : ExactSpec Mode L D := ⟨shape,leftWord,rightWord,word [] z,word [false,false,true] z,.m0,rule⟩
def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (left .E true c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .D false c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (right .D false c)
  | .E,false => some (left .F true c)
  | .E,true => none
  | .F,false => some (right .D true c)
  | .F,true => some (left .A true c)
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
def codes : List (Fin 25) := [8,19,11,14,1,13,17,14,23,0,16,3]
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
  let k : Nat := 4
  have hi : Box33PrefixMacro.run step k (project BB6Coverage.blank) =
      some (exactPhase spec spec.initial [] []) := by
    simp [k,project,Box33Source.project,BB6Coverage.blank,Box33Source.q,Box33Source.perm,exactPhase,spec,shape,atShape,blocks,leftWord,rightWord,word,Box33PrefixMacro.run,step,left,right]
  intro h
  have hc := exactNever spec step sound positive (n-k) spec.initial [] []
  by_cases hn : n≤k
  · rw [←show n+(k-n)=k by omega,Box33PrefixMacro.run_add,h] at hi
    contradiction
  · rw [←show k+(n-k)=n by omega,Box33PrefixMacro.run_add,hi,Option.bind_some] at h
    exact hc h

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms compatible_never
end M4

namespace M11
inductive Mode where
  | m0 | m1 | m2
inductive L where
  | l0 | l1 | l2 | l3
inductive D where
  | d0
def shape : Mode → Shape
  | .m0 => ⟨.E,false,[],[]⟩
  | .m1 => ⟨.B,true,[],[]⟩
  | .m2 => ⟨.D,true,[],[]⟩
def leftWord : L → List Bool
  | .l0 => [false,false,false]
  | .l1 => [true,false,false]
  | .l2 => [false,true,false]
  | .l3 => [true,true,false]
def rightWord : D → List Bool
  | .d0 => [true,true,true]
def rule : Mode → Option L → Option D → Rule Mode L D
  | .m0,none,none => ⟨4,.m0,[.l1],[]⟩
  | .m0,none,some .d0 => ⟨2,.m1,[.l1],[.d0]⟩
  | .m0,some .l0,none => ⟨4,.m0,[.l1],[]⟩
  | .m0,some .l0,some .d0 => ⟨2,.m1,[.l1],[.d0]⟩
  | .m0,some .l1,none => ⟨6,.m0,[.l2],[]⟩
  | .m0,some .l1,some .d0 => ⟨4,.m2,[.l2],[.d0]⟩
  | .m0,some .l2,none => ⟨4,.m0,[.l3],[]⟩
  | .m0,some .l2,some .d0 => ⟨2,.m1,[.l3],[.d0]⟩
  | .m0,some .l3,none => ⟨3,.m0,[],[.d0]⟩
  | .m0,some .l3,some .d0 => ⟨3,.m0,[],[.d0,.d0]⟩
  | .m1,none,none => ⟨2,.m0,[],[]⟩
  | .m1,none,some .d0 => ⟨3,.m2,[],[]⟩
  | .m1,some .l0,none => ⟨2,.m0,[.l0],[]⟩
  | .m1,some .l0,some .d0 => ⟨3,.m2,[.l0,.l0],[]⟩
  | .m1,some .l1,none => ⟨2,.m0,[.l1],[]⟩
  | .m1,some .l1,some .d0 => ⟨3,.m2,[.l0,.l1],[]⟩
  | .m1,some .l2,none => ⟨2,.m0,[.l2],[]⟩
  | .m1,some .l2,some .d0 => ⟨3,.m2,[.l0,.l2],[]⟩
  | .m1,some .l3,none => ⟨2,.m0,[.l3],[]⟩
  | .m1,some .l3,some .d0 => ⟨3,.m2,[.l0,.l3],[]⟩
  | .m2,none,none => ⟨2,.m0,[],[]⟩
  | .m2,none,some .d0 => ⟨3,.m2,[],[]⟩
  | .m2,some .l0,none => ⟨2,.m0,[.l0],[]⟩
  | .m2,some .l0,some .d0 => ⟨3,.m2,[.l0,.l0],[]⟩
  | .m2,some .l1,none => ⟨2,.m0,[.l1],[]⟩
  | .m2,some .l1,some .d0 => ⟨3,.m2,[.l0,.l1],[]⟩
  | .m2,some .l2,none => ⟨2,.m0,[.l2],[]⟩
  | .m2,some .l2,some .d0 => ⟨3,.m2,[.l0,.l2],[]⟩
  | .m2,some .l3,none => ⟨2,.m0,[.l3],[]⟩
  | .m2,some .l3,some .d0 => ⟨3,.m2,[.l0,.l3],[]⟩
def spec : ExactSpec Mode L D := ⟨shape,leftWord,rightWord,word [] z,word [false,false,true] z,.m0,rule⟩
def step (c : C9Pair.Config) : Option C9Pair.Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => some (left .E true c)
  | .B,false => some (left .C true c)
  | .B,true => some (right .D false c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (right .D false c)
  | .E,false => some (left .F true c)
  | .E,true => none
  | .F,false => some (right .B true c)
  | .F,true => some (left .A true c)
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
def codes : List (Fin 25) := [8,19,11,14,1,13,17,14,23,0,8,3]
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
  let k : Nat := 4
  have hi : Box33PrefixMacro.run step k (project BB6Coverage.blank) =
      some (exactPhase spec spec.initial [] []) := by
    simp [k,project,Box33Source.project,BB6Coverage.blank,Box33Source.q,Box33Source.perm,exactPhase,spec,shape,atShape,blocks,leftWord,rightWord,word,Box33PrefixMacro.run,step,left,right]
  intro h
  have hc := exactNever spec step sound positive (n-k) spec.initial [] []
  by_cases hn : n≤k
  · rw [←show n+(k-n)=k by omega,Box33PrefixMacro.run_add,h] at hi
    contradiction
  · rw [←show k+(n-k)=n by omega,Box33PrefixMacro.run_add,hi,Option.bind_some] at h
    exact hc h

def partialTable : PartialMachine := fun s => some (table s)
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m := by
  have he : m = table := funext fun s => hm s _ rfl
  rw [he]
  exact never

#print axioms compatible_never
end M11
end BB6.Agent13.Box33D17V23Anchored
