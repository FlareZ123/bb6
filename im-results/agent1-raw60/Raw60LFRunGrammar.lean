import Raw60LFUnaryCore
namespace BB6.Agent1Raw60LFRunGrammar
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1Raw60LFUnaryCore
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none
abbrev A := Q 0

inductive Tail where
  | t0
  | t1
  | t2
  | t3
  | t4
  | t5
  | t6
  | t7
  | t8
  | t9
  | t10
  | t11
  | t12
  | t13
  | t14
  | t15
  | t16
  | t17
  | t18
  | t19
  | t20
  | t21
  | t22
  | t23
  | t24
  | t25
  | t26
  | t27
  | t28
  | t29
  | t30
  | t31
  | t32
  | t33
  | t34
  | t35
  | t36
  | t37
  | t38
  | t39
  | t40
  | t41
  | t42
  | t43
  | t44
  | t45
  | t46
  | t47
  | t48
  | t49
  | t50
inductive Word where
  | tail (i : Tail)
  | digit (b : Bool) (w : Word)

def encTail : Tail → List Bool
  | .t0 => []
  | .t1 => [false,true,true,true,true,true]
  | .t2 => [false,true,true,true,false,true,false,true,true,false,true,true,true]
  | .t3 => [false,true,true,false,true,false,true,true,true,true]
  | .t4 => [false,true,true,true,true,false,true,true,true,false,true,true]
  | .t5 => [false,true,true,true,true,false,true,true,false,true,true,true,true,false,true,true,true,true]
  | .t6 => [false,true,true,false,true,true,true,true]
  | .t7 => [false,true,true,true,true,false,true,true,true,true,true,true,true,true]
  | .t8 => [false,true,true,true,true,false,true,true,false,true,true,true,true,true,true,true,true,true,true,true]
  | .t9 => [false,true,true,true,true,true,true,true,true,true]
  | .t10 => [false,true,true,true,false,true,false,true,true,false,true,true,true,false,true,false,true,true,true,false,true,true]
  | .t11 => [false,true,true,false,true,false,true,true,true,false,true,true,true,true,false,true,true,true,true]
  | .t12 => [false,true,true,true,true,false,true,true,true,false,true,true,true,true,false,true,true,false,true,true,true,true,true,true,true]
  | .t13 => [false,true,true,true,true,false,true,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,true,true,true]
  | .t14 => [false,true,true,false,true,true,false,true,true,false,true,true,true,true,true,true,true]
  | .t15 => [false,true,true,true,true,false,true,true,true,true,false,true,true,false,true,false,true,true,false,true,true,true,false,true,false,true,true,true,true]
  | .t16 => [false,true,true,true,true,false,true,true,false,true,true,true,true,true,false,true,true,false,true,true,true,false,true,true,false,true,false,true,true,true,true]
  | .t17 => [false,true,true,true,false,true,true,false,true,true,true,false,true,true,false,true,false,true,true,true,true]
  | .t18 => [false,true,true,true,false,true,false,true,true,true,true,false,true,true,true,true,false,true,true,true,false,true,true]
  | .t19 => [false,true,true,false,true,true,true,true,false,true,true,true,false,true,true]
  | .t20 => [false,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,false,true,true,true,true]
  | .t21 => [false,true,true,true,true,false,true,true,false,true,true,true,true,true,true,true,false,true,true,false,true,true,true,true]
  | .t22 => [false,true,true,true,true,true,false,true,true,false,true,true,true,true]
  | .t23 => [false,true,true,true,false,true,false,true,true,false,true,true,true,false,true,true]
  | .t24 => [false,true,true,false,true,false,true,true,true,true,true,true]
  | .t25 => [false,true,true,true,true,false,true,true,true,false,true,true,true,true]
  | .t26 => [false,true,true,true,true,false,true,true,false,true,true,true,true,false,true,true]
  | .t27 => [false,true,true,false,true,true]
  | .t28 => [false,true,true,true,true,false,true,true,true,true,true,true]
  | .t29 => [false,true,true,true,true,false,true,true,false,true,true,true,true,true,true,true,true,true]
  | .t30 => [false,true,true,true,true,true,true,true]
  | .t31 => [false,true,true,true,false,true,false,true,true,false,true,true,true,false,true,false,true,true,true,true]
  | .t32 => [false,true,true,false,true,false,true,true,true,false,true,true]
  | .t33 => [false,true,true,true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,true]
  | .t34 => [false,true,true,true,true,false,true,true,false,true,true,true,true,false,true,true,false,true,true,true,true]
  | .t35 => [false,true,true,false,true,true,false,true,true,true,true]
  | .t36 => [false,true,true,true,true,false,true,true,true,true,false,true,true]
  | .t37 => [false,true,true,true,true,false,true,true,false,true,true,true,true,true,false,true,true,true,true]
  | .t38 => [false,true,true,true,false,true,true,true,true]
  | .t39 => [false,true,true,true,false,true,false,true,true,true,true,true,true,true,true]
  | .t40 => [false,true,true,true,true,true,true]
  | .t41 => [false,true,false,true,true,true,true]
  | .t42 => [false,true,true,true,false,true,true,true,true,true,true]
  | .t43 => [false,true,true,true,false,true,false,true,true,true,true,true,true,true,true,true,true]
  | .t44 => [false,true,true,true,true,true,true,true,true]
  | .t45 => [false,true,false,true,true,true,false,true,true]
  | .t46 => [false,true,true,true,false,true,true,true,true,false,true,true,true,true,true]
  | .t47 => [false,true,true,true,false,true,false,true,true,true,true,true,true,false,true,true,true]
  | .t48 => [false,true,true,true,true,false,true,true,true]
  | .t49 => [false,true,true,true,true,false,true,true,false,true,true,true,true,true,true]
  | .t50 => [false,true,true,true,true]

def block (b : Bool) : List Bool := if b then [false,true,true,true,true,false,true,true,false,true,true,true] else [false,true,true,true,false,true,false,true,true,true]

def enc : Word → List Bool
  | .tail i => encTail i
  | .digit b w => block b ++ enc w

def nextTail : Tail → Word
  | .t0 => Word.tail Tail.t1
  | .t1 => Word.tail Tail.t2
  | .t2 => Word.digit false (Word.tail Tail.t3)
  | .t3 => Word.tail Tail.t4
  | .t4 => Word.tail Tail.t5
  | .t5 => Word.digit true (Word.tail Tail.t6)
  | .t6 => Word.tail Tail.t7
  | .t7 => Word.tail Tail.t8
  | .t8 => Word.digit true (Word.tail Tail.t9)
  | .t9 => Word.tail Tail.t10
  | .t10 => Word.digit false (Word.tail Tail.t11)
  | .t11 => Word.tail Tail.t12
  | .t12 => Word.tail Tail.t13
  | .t13 => Word.digit true (Word.tail Tail.t14)
  | .t14 => Word.tail Tail.t15
  | .t15 => Word.tail Tail.t16
  | .t16 => Word.digit true (Word.tail Tail.t17)
  | .t17 => Word.tail Tail.t18
  | .t18 => Word.digit false (Word.tail Tail.t19)
  | .t19 => Word.tail Tail.t20
  | .t20 => Word.tail Tail.t21
  | .t21 => Word.digit true (Word.tail Tail.t22)
  | .t22 => Word.tail Tail.t23
  | .t23 => Word.digit false (Word.tail Tail.t24)
  | .t24 => Word.tail Tail.t25
  | .t25 => Word.tail Tail.t26
  | .t26 => Word.digit true (Word.tail Tail.t27)
  | .t27 => Word.tail Tail.t28
  | .t28 => Word.tail Tail.t29
  | .t29 => Word.digit true (Word.tail Tail.t30)
  | .t30 => Word.tail Tail.t31
  | .t31 => Word.digit false (Word.tail Tail.t32)
  | .t32 => Word.tail Tail.t33
  | .t33 => Word.tail Tail.t34
  | .t34 => Word.digit true (Word.tail Tail.t35)
  | .t35 => Word.tail Tail.t36
  | .t36 => Word.tail Tail.t37
  | .t37 => Word.digit true (Word.tail Tail.t38)
  | .t38 => Word.tail Tail.t39
  | .t39 => Word.digit false (Word.tail Tail.t40)
  | .t40 => Word.digit true (Word.tail Tail.t41)
  | .t41 => Word.tail Tail.t42
  | .t42 => Word.tail Tail.t43
  | .t43 => Word.digit false (Word.tail Tail.t44)
  | .t44 => Word.digit true (Word.tail Tail.t45)
  | .t45 => Word.tail Tail.t46
  | .t46 => Word.tail Tail.t47
  | .t47 => Word.digit false (Word.tail Tail.t48)
  | .t48 => Word.tail Tail.t49
  | .t49 => Word.digit true (Word.tail Tail.t50)
  | .t50 => Word.digit true (Word.tail Tail.t0)

def next : Word → Word
  | .tail i => nextTail i
  | .digit b w => .digit b (next w)

theorem encShape (w : Word) : enc w = [] ∨ ∃ R, enc w = false::R := by
  cases w with
  | tail i => cases i <;> first | exact Or.inl rfl | exact Or.inr ⟨_,rfl⟩
  | digit b w => cases b <;> exact Or.inr ⟨_,rfl⟩

def Macro (w : Word) : Prop := ∀ L : List Bool, ∃ t R, 0<t ∧ run0 table t (A (false::L) (enc w).tail) = some (F L (false::R)) ∧ enc (next w) = false::true::true::R

theorem base (i : Tail) : Macro (.tail i) := by
  intro L
  cases i with
  | t0 => exact ⟨17,[true,true,true],by decide,by rfl,by rfl⟩
  | t1 => exact ⟨69,[true,false,true,false,true,true,false,true,true,true],by decide,by rfl,by rfl⟩
  | t2 => exact ⟨93,[true,false,true,false,true,true,true,false,true,true,false,true,false,true,true,true,true],by decide,by rfl,by rfl⟩
  | t3 => exact ⟨49,[true,true,false,true,true,true,false,true,true],by decide,by rfl,by rfl⟩
  | t4 => exact ⟨105,[true,true,false,true,true,false,true,true,true,true,false,true,true,true,true],by decide,by rfl,by rfl⟩
  | t5 => exact ⟨81,[true,true,false,true,true,false,true,true,true,false,true,true,false,true,true,true,true],by decide,by rfl,by rfl⟩
  | t6 => exact ⟨77,[true,true,false,true,true,true,true,true,true,true,true],by decide,by rfl,by rfl⟩
  | t7 => exact ⟨133,[true,true,false,true,true,false,true,true,true,true,true,true,true,true,true,true,true],by decide,by rfl,by rfl⟩
  | t8 => exact ⟨81,[true,true,false,true,true,false,true,true,true,false,true,true,true,true,true,true,true,true,true],by decide,by rfl,by rfl⟩
  | t9 => exact ⟨209,[true,false,true,false,true,true,false,true,true,true,false,true,false,true,true,true,false,true,true],by decide,by rfl,by rfl⟩
  | t10 => exact ⟨141,[true,false,true,false,true,true,true,false,true,true,false,true,false,true,true,true,false,true,true,true,true,false,true,true,true,true],by decide,by rfl,by rfl⟩
  | t11 => exact ⟨149,[true,true,false,true,true,true,false,true,true,true,true,false,true,true,false,true,true,true,true,true,true,true],by decide,by rfl,by rfl⟩
  | t12 => exact ⟨89,[true,true,false,true,true,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true,true,true,true,true],by decide,by rfl,by rfl⟩
  | t13 => exact ⟨81,[true,true,false,true,true,false,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,true,true,true,true],by decide,by rfl,by rfl⟩
  | t14 => exact ⟨193,[true,true,false,true,true,true,true,false,true,true,false,true,false,true,true,false,true,true,true,false,true,false,true,true,true,true],by decide,by rfl,by rfl⟩
  | t15 => exact ⟨121,[true,true,false,true,true,false,true,true,true,true,true,false,true,true,false,true,true,true,false,true,true,false,true,false,true,true,true,true],by decide,by rfl,by rfl⟩
  | t16 => exact ⟨81,[true,true,false,true,true,false,true,true,true,false,true,true,true,false,true,true,false,true,true,true,false,true,true,false,true,false,true,true,true,true],by decide,by rfl,by rfl⟩
  | t17 => exact ⟨105,[true,false,true,false,true,true,true,true,false,true,true,true,true,false,true,true,true,false,true,true],by decide,by rfl,by rfl⟩
  | t18 => exact ⟨49,[true,false,true,false,true,true,true,false,true,true,false,true,true,true,true,false,true,true,true,false,true,true],by decide,by rfl,by rfl⟩
  | t19 => exact ⟨117,[true,true,false,true,true,true,true,true,true,false,true,true,true,true,false,true,true,true,true],by decide,by rfl,by rfl⟩
  | t20 => exact ⟨113,[true,true,false,true,true,false,true,true,true,true,true,true,true,false,true,true,false,true,true,true,true],by decide,by rfl,by rfl⟩
  | t21 => exact ⟨81,[true,true,false,true,true,false,true,true,true,false,true,true,true,true,true,false,true,true,false,true,true,true,true],by decide,by rfl,by rfl⟩
  | t22 => exact ⟨81,[true,false,true,false,true,true,false,true,true,true,false,true,true],by decide,by rfl,by rfl⟩
  | t23 => exact ⟨109,[true,false,true,false,true,true,true,false,true,true,false,true,false,true,true,true,true,true,true],by decide,by rfl,by rfl⟩
  | t24 => exact ⟨49,[true,true,false,true,true,true,false,true,true,true,true],by decide,by rfl,by rfl⟩
  | t25 => exact ⟨89,[true,true,false,true,true,false,true,true,true,true,false,true,true],by decide,by rfl,by rfl⟩
  | t26 => exact ⟨81,[true,true,false,true,true,false,true,true,true,false,true,true,false,true,true],by decide,by rfl,by rfl⟩
  | t27 => exact ⟨61,[true,true,false,true,true,true,true,true,true],by decide,by rfl,by rfl⟩
  | t28 => exact ⟨117,[true,true,false,true,true,false,true,true,true,true,true,true,true,true,true],by decide,by rfl,by rfl⟩
  | t29 => exact ⟨81,[true,true,false,true,true,false,true,true,true,false,true,true,true,true,true,true,true],by decide,by rfl,by rfl⟩
  | t30 => exact ⟨137,[true,false,true,false,true,true,false,true,true,true,false,true,false,true,true,true,true],by decide,by rfl,by rfl⟩
  | t31 => exact ⟨97,[true,false,true,false,true,true,true,false,true,true,false,true,false,true,true,true,false,true,true],by decide,by rfl,by rfl⟩
  | t32 => exact ⟨93,[true,true,false,true,true,true,false,true,true,true,true,false,true,true,true,true],by decide,by rfl,by rfl⟩
  | t33 => exact ⟨89,[true,true,false,true,true,false,true,true,true,true,false,true,true,false,true,true,true,true],by decide,by rfl,by rfl⟩
  | t34 => exact ⟨81,[true,true,false,true,true,false,true,true,true,false,true,true,false,true,true,false,true,true,true,true],by decide,by rfl,by rfl⟩
  | t35 => exact ⟨57,[true,true,false,true,true,true,true,false,true,true],by decide,by rfl,by rfl⟩
  | t36 => exact ⟨113,[true,true,false,true,true,false,true,true,true,true,true,false,true,true,true,true],by decide,by rfl,by rfl⟩
  | t37 => exact ⟨81,[true,true,false,true,true,false,true,true,true,false,true,true,true,false,true,true,true,true],by decide,by rfl,by rfl⟩
  | t38 => exact ⟨77,[true,false,true,false,true,true,true,true,true,true,true,true],by decide,by rfl,by rfl⟩
  | t39 => exact ⟨49,[true,false,true,false,true,true,true,false,true,true,true,true,true,true],by decide,by rfl,by rfl⟩
  | t40 => exact ⟨137,[true,true,false,true,true,false,true,true,true,false,true,false,true,true,true,true],by decide,by rfl,by rfl⟩
  | t41 => exact ⟨33,[true,false,true,true,true,true,true,true],by decide,by rfl,by rfl⟩
  | t42 => exact ⟨93,[true,false,true,false,true,true,true,true,true,true,true,true,true,true],by decide,by rfl,by rfl⟩
  | t43 => exact ⟨49,[true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,true],by decide,by rfl,by rfl⟩
  | t44 => exact ⟨209,[true,true,false,true,true,false,true,true,true,false,true,false,true,true,true,false,true,true],by decide,by rfl,by rfl⟩
  | t45 => exact ⟨45,[true,false,true,true,true,true,false,true,true,true,true,true],by decide,by rfl,by rfl⟩
  | t46 => exact ⟨73,[true,false,true,false,true,true,true,true,true,true,false,true,true,true],by decide,by rfl,by rfl⟩
  | t47 => exact ⟨49,[true,false,true,false,true,true,true,false,true,true,true,true,false,true,true,true],by decide,by rfl,by rfl⟩
  | t48 => exact ⟨93,[true,true,false,true,true,false,true,true,true,true,true,true],by decide,by rfl,by rfl⟩
  | t49 => exact ⟨81,[true,true,false,true,true,false,true,true,true,false,true,true,true,true],by decide,by rfl,by rfl⟩
  | t50 => exact ⟨69,[true,true,false,true,true,false,true,true,true],by decide,by rfl,by rfl⟩

theorem advance (w : Word) : Macro w := by
  induction w with
  | tail i => exact base i
  | digit b w ih =>
    intro L
    cases b with
    | false =>
      have h1 : run0 table 30 (A (false::L) (enc (.digit false w)).tail) = some (A (false::([true,true,false,true,true,true,false,true,false,true]++L)) (enc w).tail) := by
        rcases encShape w with h | ⟨R,h⟩ <;> simp only [enc,h] <;> rfl
      obtain ⟨t,R,ht,h2,he⟩ := ih ([true,true,false,true,true,true,false,true,false,true]++L)
      have h3 : run0 table 18 (F ([true,true,false,true,true,true,false,true,false,true]++L) (false::R)) = some (F L (false::true::false::true::false::true::true::true::false::true::true::R)) := by rfl
      exact ⟨30+t+18,_,by omega,join0 (join0 h1 h2) h3,by simp only [next,enc,he]; rfl⟩
    | true =>
      have h1 : run0 table 36 (A (false::L) (enc (.digit true w)).tail) = some (A (false::([true,true,false,true,true,true,true,false,true,false,false,true]++L)) (enc w).tail) := by
        rcases encShape w with h | ⟨R,h⟩ <;> simp only [enc,h] <;> rfl
      obtain ⟨t,R,ht,h2,he⟩ := ih ([true,true,false,true,true,true,true,false,true,false,false,true]++L)
      have h3 : run0 table 44 (F ([true,true,false,true,true,true,true,false,true,false,false,true]++L) (false::R)) = some (F L (false::true::true::false::true::true::false::true::true::true::false::true::true::R)) := by rfl
      exact ⟨36+t+44,_,by omega,join0 (join0 h1 h2) h3,by simp only [next,enc,he]; rfl⟩

def cfg (w : Word) := F [] ([false,true,false,true,true]++enc w)

theorem epoch (w : Word) : ∃ t, 0<t ∧ run0 table t (cfg w) = some (cfg (next w)) := by
  have h1 : run0 table 8 (cfg w) = some (A [false,true,true,false,true,true,false,true] (enc w).tail) := by
    rcases encShape w with h | ⟨R,h⟩ <;> simp only [cfg,h] <;> rfl
  obtain ⟨t,R,ht,h2,he⟩ := advance w [true,true,false,true,true,false,true]
  have h3 : run0 table 13 (F [true,true,false,true,true,false,true] (false::R)) = some (F [] ([false,true,false,true,true,false,true,true]++R)) := by rfl
  exact ⟨8+t+13,by omega,by simp only [cfg,he]; exact join0 (join0 h1 h2) h3⟩

def words : Nat → Word
  | 0 => .tail .t50
  | n+1 => next (words n)
def family (n : Nat) := cfg (words n)
theorem entry : run0 table 69 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem growth_exists (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := epoch (words n)
noncomputable def cost (n : Nat) : Nat := Classical.choose (growth_exists n)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 69 cost entry (fun n => (Classical.choose_spec (growth_exists n)).1)
    (fun n => (Classical.choose_spec (growth_exists n)).2) m hm
#print axioms never
end BB6.Agent1Raw60LFRunGrammar
