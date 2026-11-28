import Box27ReturnInvariant
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Counter0178
open BB6Coverage

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,false,2⟩)
  | 2,_ => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,true,2⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

inductive Digits : List Bool → Prop where
  | empty : Digits []
  | one : Digits [true]
  | two : Digits [true,true]
  | block (a b : Bool) {R : List Bool} : Digits R → Digits (a::b::b::R)

def Zeros : List Bool := [false,false,false]
def Ones : List Bool := [true,true,true]
def ret (R : List Bool) : Z0 := ⟨5,[false],R⟩
def carry (k : Nat) (R : List Bool) : Z0 := ⟨3,rep Ones (k+1)++[false],R⟩
def eraseStart (k : Nat) (R : List Bool) : Z0 := ⟨5,rep Ones (k+1)++[false],R⟩

theorem prefix_digits (k : Nat) (R : List Bool) (h : Digits R) : Digits (rep Zeros k++R) := by
  induction k with
  | zero => exact h
  | succ k ih => exact Digits.block false false ih

theorem leftAtom (L R : List Bool) :
    run0 table 3 ⟨5,[]++Ones++L,[]++R⟩ = some ⟨5,[]++L,[]++Zeros++R⟩ := by rfl

theorem erase (k : Nat) (R : List Bool) :
    run0 table (3*(k+1)) (eraseStart k R) = some (ret (rep Zeros (k+1)++R)) := by
  simpa only [List.nil_append,eraseStart,ret] using sweepL table 5 [] [] Ones Zeros 3 leftAtom (k+1) [false] R

theorem carry_return (R : List Bool) (h : Digits R) (k : Nat) :
    ∃ t S, 0<t ∧ Digits S ∧ run0 table t (carry k R) = some (ret S) := by
  induction h generalizing k with
  | empty =>
    have h1 : run0 table 2 (carry k []) = some (eraseStart k [true]) := by rfl
    exact ⟨2+3*(k+1),_,by omega,prefix_digits (k+1) _ Digits.one,join0 h1 (erase k [true])⟩
  | one =>
    have h1 : run0 table 8 (carry k [true]) = some (eraseStart k [false,true,true]) := by rfl
    exact ⟨8+3*(k+1),_,by omega,prefix_digits (k+1) _ (Digits.block false true Digits.empty),join0 h1 (erase k [false,true,true])⟩
  | two =>
    have h1 : run0 table 10 (carry k [true,true]) = some (eraseStart k [false,false,false,true]) := by rfl
    exact ⟨10+3*(k+1),_,by omega,prefix_digits (k+1) _ (Digits.block false false Digits.one),join0 h1 (erase k [false,false,false,true])⟩
  | @block a b R h ih =>
    cases a <;> cases b
    · have h1 : run0 table 2 (carry k (false::false::false::R)) = some (eraseStart k (true::false::false::R)) := by rfl
      exact ⟨2+3*(k+1),_,by omega,prefix_digits (k+1) _ (Digits.block true false h),join0 h1 (erase k _)⟩
    · have h1 : run0 table 2 (carry k (false::true::true::R)) = some (eraseStart k (true::true::true::R)) := by rfl
      exact ⟨2+3*(k+1),_,by omega,prefix_digits (k+1) _ (Digits.block true true h),join0 h1 (erase k _)⟩
    · have h1 : run0 table 8 (carry k (true::false::false::R)) = some (eraseStart k (false::true::true::R)) := by rfl
      exact ⟨8+3*(k+1),_,by omega,prefix_digits (k+1) _ (Digits.block false true h),join0 h1 (erase k _)⟩
    · have h1 : run0 table 3 (carry k (true::true::true::R)) = some (carry (k+1) R) := by rfl
      obtain ⟨t,S,ht,hS,hr⟩ := ih (k+1)
      exact ⟨3+t,S,by omega,hS,join0 h1 hr⟩

theorem return_step (R : List Bool) (h : Digits R) :
    ∃ t S, 0<t ∧ Digits S ∧ run0 table t (ret R) = some (ret S) := by
  cases h with
  | empty => exact ⟨2,[true],by decide,Digits.one,rfl⟩
  | one => exact ⟨8,[false,true,true],by decide,Digits.block false true Digits.empty,rfl⟩
  | two => exact ⟨10,[false,false,false,true],by decide,Digits.block false false Digits.one,rfl⟩
  | @block a b R h =>
    cases a <;> cases b
    · exact ⟨2,_,by decide,Digits.block true false h,rfl⟩
    · exact ⟨2,_,by decide,Digits.block true true h,rfl⟩
    · exact ⟨8,_,by decide,Digits.block false true h,rfl⟩
    · have h1 : run0 table 3 (ret (true::true::true::R)) = some (carry 0 R) := by rfl
      obtain ⟨t,S,ht,hS,hr⟩ := carry_return R h 0
      exact ⟨3+t,S,by omega,hS,join0 h1 hr⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply never_of_return table (fun z => ∃ R, Digits R ∧ z=ret R) 10 ?_ ?_ m hm
  · exact ⟨ret [true,true,true],⟨_,Digits.block true true Digits.empty,rfl⟩,rfl⟩
  · intro z hz
    obtain ⟨R,h,rfl⟩ := hz
    obtain ⟨t,S,ht,hS,hr⟩ := return_step R h
    exact ⟨t,ret S,ht,⟨S,hS,rfl⟩,hr⟩
#print axioms never
end BB6Coverage.Agent31Pump.Counter0178
