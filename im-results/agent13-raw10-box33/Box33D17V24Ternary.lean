import Box33PrefixMacro
namespace BB6.Agent13.Box33D17V24Ternary
open C9Pair
open BB6.Agent13.Box33D14Growth (z word rep rep_add cfg)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
inductive Variant where | m1 | m3 | m32 deriving DecidableEq
def step (v : Variant) (c : Config) : Option Config :=
  match c.q,c.a with
  | .A,false => some (right .B true c)
  | .A,true => none
  | .B,false => some (left .C true c)
  | .B,true => some (left .C false c)
  | .C,false => some (left .A false c)
  | .C,true => some (left .D false c)
  | .D,false => some (left .E false c)
  | .D,true => some (left .A true c)
  | .E,false => some (right .F true c)
  | .E,true => some (right .E false c)
  | .F,false => some (right .F false c)
  | .F,true => match v with
    | .m1 => some (left .D true c)
    | .m3 => some (left .A false c)
    | .m32 => some (right .B false c)
abbrev run (v : Variant) := BB6.Agent13.Box33PrefixMacro.run (step v)
theorem run_add (v : Variant) (m n : Nat) (c : Config) :
    run v (m+n) c = (run v m c).bind (run v n) :=
  BB6.Agent13.Box33PrefixMacro.run_add (step v) m n c
abbrev A := cfg .A
abbrev F := cfg .F
abbrev zeros := rep [false]
def base (v : Variant) (b : Bool) : Stream :=
  match v with
  | .m1 => word [false,true,true] z
  | .m3 => z
  | .m32 => word [false,false,b] z
def tail (v : Variant) (b : Bool) : Stream :=
  match v with
  | .m32 => push b z
  | _ => z
def off (v : Variant) : Nat := if v = .m1 then 2 else 1
def finishCost (v : Variant) : Nat := match v with | .m1 => 10 | .m3 => 1 | .m32 => 3
def rootCost (v : Variant) : Nat := match v with | .m1 => 18 | .m3 => 8 | .m32 => 10
def carryR (v : Variant) (b : Bool) : Nat → Stream
  | 0 => base v b
  | k+1 => word [false,true] (zeros (2*k+off v) (push true (tail v b)))
theorem popFirst (v : Variant) (b : Bool) (l : Stream) :
    run v 4 (A (word [true,false] l) (carryR v b 0)) = some (A l (carryR v b 1)) := by
  cases v <;> cases b <;> simp [A,cfg,carryR,base,tail,off,zeros,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem popRaw (v : Variant) (l r : Stream) :
    run v 4 (A (word [true,false] l) (word [false,true] r)) =
      some (A l (word [false,true,false,false] r)) := by
  cases v <;> simp [A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem popCarry (v : Variant) (b : Bool) (k : Nat) (l : Stream) :
    run v 4 (A (word [true,false] l) (carryR v b k)) = some (A l (carryR v b (k+1))) := by
  cases k with
  | zero => exact popFirst v b l
  | succ k =>
    rw [carryR,carryR,show 2*(k+1)+off v = 2+(2*k+off v) by omega,show zeros (2+(2*k+off v)) (push true (tail v b)) = zeros 2 (zeros (2*k+off v) (push true (tail v b))) from rep_add [false] 2 _ _]
    exact popRaw v l _
theorem rootZero (v : Variant) (b : Bool) (l : Stream) :
    run v (rootCost v) (A (word [false,false] l) (base v b)) =
      some (A (word [false,true] l) (base v (!b))) := by
  cases v <;> cases b <;> simp [rootCost,A,cfg,base,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem rootOne (v : Variant) (b : Bool) (l : Stream) :
    run v (rootCost v) (A (word [false,true] l) (base v b)) =
      some (A (word [true,false] l) (base v (!b))) := by
  cases v <;> cases b <;> simp [rootCost,A,cfg,base,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem enterZero (v : Variant) (l r : Stream) :
    run v 5 (A (word [false,false] l) (word [false,true] r)) =
      some (F (push true l) (zeros 3 r)) := by
  cases v <;> simp [A,F,cfg,word,rep,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem enterOne (v : Variant) (l r : Stream) :
    run v 6 (A (word [false,true] l) (word [false,true] r)) =
      some (F (word [true,false] l) (zeros 2 r)) := by
  cases v <;> simp [A,F,cfg,word,rep,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem fStep (v : Variant) (l r : Stream) :
    run v 1 (F l (push false r)) = some (F (push false l) r) := by
  simp [F,cfg,BB6.Agent13.Box33PrefixMacro.run,step,right]
theorem fSweep (v : Variant) (n : Nat) (l r : Stream) :
    run v n (F l (zeros n r)) = some (F (zeros n l) r) := by
  induction n generalizing l r with
  | zero => rfl
  | succ n ih =>
    rw [run_add,show zeros (n+1) r = zeros n (push false r) from rep_add [false] n 1 r,
      ih,Option.bind_some]
    exact fStep v (zeros n l) r
theorem finish (v : Variant) (b : Bool) (l : Stream) :
    run v (finishCost v) (F (zeros (off v) l) (push true (tail v b))) =
      some (A l (base v (!b))) := by
  cases v <;> cases b <;> simp [finishCost,F,A,cfg,off,base,tail,rep,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem drain (v : Variant) (b : Bool) (n : Nat) (l : Stream) :
    run v (n+off v+finishCost v) (F l (zeros (n+off v) (push true (tail v b)))) =
      some (A (zeros n l) (base v (!b))) := by
  rw [run_add,fSweep,Option.bind_some,show n+off v = off v+n by omega,show zeros (off v+n) l = zeros (off v) (zeros n l) from rep_add [false] _ _ _,finish]
theorem flushZero (v : Variant) (b : Bool) (k : Nat) (l : Stream) :
    ∃ t, 0<t ∧ run v t (A (word [false,false] l) (carryR v b k)) =
      some (A (zeros (2*k) (word [false,true] l)) (base v (!b))) := by
  cases k with
  | zero => exact ⟨rootCost v, by cases v <;> decide,rootZero v b l⟩
  | succ k =>
    refine ⟨5+(2*(k+1)+1+off v+finishCost v),by omega,?_⟩
    rw [run_add,carryR,enterZero,Option.bind_some]
    rw [←show zeros (3+(2*k+off v)) (push true (tail v b)) = zeros 3 (zeros (2*k+off v) (push true (tail v b))) from rep_add [false] 3 _ _,show 3+(2*k+off v)=2*(k+1)+1+off v by omega,drain]
    rw [show zeros (2*(k+1)+1) (push true l) = zeros (2*(k+1)) (word [false,true] l) from rep_add _ _ _ _]
theorem flushOne (v : Variant) (b : Bool) (k : Nat) (l : Stream) :
    ∃ t, 0<t ∧ run v t (A (word [false,true] l) (carryR v b k)) =
      some (A (zeros (2*k) (word [true,false] l)) (base v (!b))) := by
  cases k with
  | zero => exact ⟨rootCost v, by cases v <;> decide,rootOne v b l⟩
  | succ k =>
    refine ⟨6+(2*(k+1)+off v+finishCost v),by omega,?_⟩
    rw [run_add,carryR,enterOne,Option.bind_some]
    rw [←show zeros (2+(2*k+off v)) (push true (tail v b)) = zeros 2 (zeros (2*k+off v) (push true (tail v b))) from rep_add [false] 2 _ _,show 2+(2*k+off v)=2*(k+1)+off v by omega,drain]
inductive Digit where | zero | one | two
def digits : List Digit → Stream
  | [] => z
  | .zero::ds => word [false,false] (digits ds)
  | .one::ds => word [false,true] (digits ds)
  | .two::ds => word [true,false] (digits ds)
theorem zeroDigits (k : Nat) (ds : List Digit) :
    digits (List.replicate k .zero ++ ds) = zeros (2*k) (digits ds) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ,List.cons_append,digits,ih]
    rw [show 2*(k+1)=2+2*k by omega,show zeros (2+2*k) (digits ds) = zeros 2 (zeros (2*k) (digits ds)) from rep_add [false] 2 _ _]
    rfl
def phase (v : Variant) (b : Bool) (k : Nat) (ds : List Digit) : Config :=
  A (digits ds) (carryR v b k)
theorem progress (v : Variant) (b : Bool) (k : Nat) (ds : List Digit) :
    ∃ t : Nat, 0<t ∧ ∃ b' k' ds', run v t (phase v b k ds) = some (phase v b' k' ds') := by
  cases ds with
  | nil =>
    obtain ⟨t,ht,h⟩ := flushZero v b k z
    refine ⟨t,ht,!b,0,List.replicate k .zero ++ [.one],?_⟩
    simpa [phase,zeroDigits,digits,carryR,word] using h
  | cons d ds =>
    cases d with
    | zero =>
      obtain ⟨t,ht,h⟩ := flushZero v b k (digits ds)
      refine ⟨t,ht,!b,0,List.replicate k .zero ++ (.one::ds),?_⟩
      simpa [phase,zeroDigits,digits,carryR] using h
    | one =>
      obtain ⟨t,ht,h⟩ := flushOne v b k (digits ds)
      refine ⟨t,ht,!b,0,List.replicate k .zero ++ (.two::ds),?_⟩
      simpa [phase,zeroDigits,digits,carryR] using h
    | two => exact ⟨4,by decide,b,k+1,ds,popCarry v b k (digits ds)⟩
theorem neverPhase (v : Variant) (n : Nat) (b : Bool) (k : Nat) (ds : List Digit) :
    run v n (phase v b k ds) ≠ none := by
  induction n using Nat.strongRecOn generalizing b k ds with
  | ind n ih =>
    intro h
    obtain ⟨t,ht,b',k',ds',he⟩ := progress v b k ds
    by_cases hn : n≤t
    · rw [←show n+(t-n)=t by omega,run_add,h] at he
      contradiction
    · rw [←show t+(n-t)=n by omega,run_add,he,Option.bind_some] at h
      exact ih _ (by omega) b' k' ds' h
theorem init1 : run .m1 17 (A z z) = some (phase .m1 false 0 [.two]) := by
  simp [phase,carryR,digits,base,A,cfg,word,BB6.Agent13.Box33PrefixMacro.run,step,left,right]
theorem neverBlank (v : Variant) (n : Nat) : run v n (A z z) ≠ none := by
  cases v with
  | m1 =>
    intro h
    by_cases hn : n≤17
    · have he := init1
      rw [←show n+(17-n)=17 by omega,run_add,h] at he
      contradiction
    · rw [←show 17+(n-17)=n by omega,run_add,init1,Option.bind_some] at h
      exact neverPhase .m1 _ false 0 [.two] h
  | m3 => exact neverPhase .m3 n false 0 []
  | m32 =>
    have he : phase .m32 false 0 [] = A z z := by simp [phase,digits,carryR,base,word]
    rw [←he]
    exact neverPhase .m32 n false 0 []
open BB6Coverage
open Box17 (index decode)
def codes : Variant → List (Fin 25)
  | .m1 => [8,0,11,9,1,13,17,3,24,18,22,15]
  | .m3 => [8,0,11,9,1,13,17,3,24,18,22,1]
  | .m32 => [8,0,11,9,1,13,17,3,24,18,22,6]
def table (v : Variant) : Machine := fun s => decode ((codes v).getD (index s).val 0)
theorem project_step (v : Variant) (c : BB6Coverage.Config) :
    (rawStep (table v) c).map BB6.Agent13.Box33PrefixMacro.project = step v (BB6.Agent13.Box33PrefixMacro.project c) := by
  rw [BB6.Agent13.Box33PrefixMacro.map_step]
  rcases c with ⟨s,p,t⟩
  have hs : s=0 ∨ s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 := by omega
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> cases hb : t p <;> cases v <;>
    simp only [readSlot,Box33Source.project,hb] <;> rfl
theorem never (v : Variant) : NeverHalts (table v) := by
  apply BB6.Agent13.Box33PrefixMacro.sourceNever (table v) (step v) (project_step v)
  intro n
  have hb : BB6.Agent13.Box33PrefixMacro.project BB6Coverage.blank = A z z := by
    change Box33Source.project false BB6Coverage.blank = A z z
    rw [Box33Source.project_blank false]
    simp [A,cfg,Box33UnarySweeper.blank] <;> rfl
  rw [hb]
  exact neverBlank v n
def partialTable (v : Variant) : PartialMachine := fun s => some (table v s)
theorem compatible_never (v : Variant) (m : Machine) (hm : compatible (partialTable v) m) : NeverHalts m := by
  have he : m = table v := funext fun s => hm s _ rfl
  rw [he]
  exact never v
#print axioms neverBlank
#print axioms compatible_never
end BB6.Agent13.Box33D17V24Ternary
