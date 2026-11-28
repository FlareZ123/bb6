import Box27ReturnInvariant
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Counter0011
open BB6Coverage

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,false,2⟩)
  | 1,true => some (some ⟨true,false,3⟩)
  | 2,_ => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨false,true,0⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,2⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none

inductive Digits : List Bool → Prop where
  | empty : Digits []
  | short : Digits [false,true]
  | block (a b : Bool) {R : List Bool} : Digits R → Digits (false::a::b::R)

def Zeros : List Bool := [false,false,false]
def Ones : List Bool := [true,true,true]
def ret (R : List Bool) : Z0 := ⟨3,[false],R⟩
def carry (k : Nat) (R : List Bool) : Z0 := ⟨0,[false]++rep Ones k++[false],R.tail⟩

theorem prefix_digits (k : Nat) (R : List Bool) (h : Digits R) : Digits (rep Zeros k++R) := by
  induction k with
  | zero => exact h
  | succ k ih => exact Digits.block false false ih

theorem zeros_rotate (k : Nat) : [false]++rep Zeros k = rep Zeros k++[false] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rep,List.append_assoc]
    change false::false::false::([false]++rep Zeros k) = false::false::false::(rep Zeros k++[false])
    rw [ih]

theorem leftAtom (L R : List Bool) :
    run0 table 9 ⟨3,[]++Ones++L,[false]++R⟩ = some ⟨3,[]++L,[false]++Zeros++R⟩ := by rfl

theorem erase (k : Nat) (R : List Bool) :
    run0 table (9*k) ⟨3,rep Ones k++[false],[false]++R⟩ = some (ret (rep Zeros k++[false]++R)) := by
  have h := sweepL table 3 [] [false] Ones Zeros 9 leftAtom k [false] R
  simpa only [List.nil_append,List.append_assoc,← List.append_assoc [false] (rep Zeros k) R,zeros_rotate,ret] using h

theorem carry_max (k : Nat) (R : List Bool) (h : Digits R) :
    run0 table 5 (carry k (false::true::true::R)) = some (carry (k+1) R) := by
  cases h <;> rfl

theorem entryCarry (R : List Bool) (h : Digits R) : run0 table 1 (ret R) = some (carry 0 R) := by
  cases h <;> rfl

theorem carry_return (R : List Bool) (h : Digits R) (k : Nat) :
    ∃ t S, 0<t ∧ Digits S ∧ run0 table t (carry k R) = some (ret S) := by
  induction h generalizing k with
  | empty =>
    have h1 : run0 table 3 (carry k []) = some ⟨3,rep Ones k++[false],[false,true]⟩ := by rfl
    have H := join0 h1 (erase k [true])
    exact ⟨3+9*k,rep Zeros k++[false,true],by omega,prefix_digits k _ Digits.short,by simpa only [List.append_assoc,List.cons_append,List.nil_append] using H⟩
  | short =>
    have h1 : run0 table 9 (carry k [false,true]) = some ⟨3,rep Ones k++[false],[false,false,true]⟩ := by rfl
    have H := join0 h1 (erase k [false,true])
    exact ⟨9+9*k,rep Zeros k++[false,false,true],by omega,prefix_digits k _ (Digits.block false true Digits.empty),by simpa only [List.append_assoc,List.cons_append,List.nil_append] using H⟩
  | @block a b R h ih =>
    cases a <;> cases b
    · have h1 : run0 table 3 (carry k (false::false::false::R)) = some ⟨3,rep Ones k++[false],[false,true,false]++R⟩ := by rfl
      have H := join0 h1 (erase k ([true,false]++R))
      exact ⟨3+9*k,rep Zeros k++(false::true::false::R),by omega,prefix_digits k _ (Digits.block true false h),by simpa only [List.append_assoc,List.cons_append,List.nil_append] using H⟩
    · have h1 : run0 table 3 (carry k (false::false::true::R)) = some ⟨3,rep Ones k++[false],[false,true,true]++R⟩ := by rfl
      have H := join0 h1 (erase k ([true,true]++R))
      exact ⟨3+9*k,rep Zeros k++(false::true::true::R),by omega,prefix_digits k _ (Digits.block true true h),by simpa only [List.append_assoc,List.cons_append,List.nil_append] using H⟩
    · have h1 : run0 table 9 (carry k (false::true::false::R)) = some ⟨3,rep Ones k++[false],[false,false,true]++R⟩ := by rfl
      have H := join0 h1 (erase k ([false,true]++R))
      exact ⟨9+9*k,rep Zeros k++(false::false::true::R),by omega,prefix_digits k _ (Digits.block false true h),by simpa only [List.append_assoc,List.cons_append,List.nil_append] using H⟩
    · obtain ⟨t,S,ht,hS,hr⟩ := ih (k+1)
      exact ⟨5+t,S,by omega,hS,join0 (carry_max k R h) hr⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply never_of_return table (fun z => ∃ R, Digits R ∧ z=ret R) 13 ?_ ?_ m hm
  · exact ⟨ret [false,false,true],⟨_,Digits.block false true Digits.empty,rfl⟩,rfl⟩
  · intro z hz
    obtain ⟨R,h,rfl⟩ := hz
    obtain ⟨t,S,ht,hS,hr⟩ := carry_return R h 0
    exact ⟨1+t,ret S,by omega,⟨S,hS,rfl⟩,join0 (entryCarry R h) hr⟩
#print axioms never
end BB6Coverage.Agent31Pump.Counter0011
