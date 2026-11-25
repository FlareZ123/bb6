import ReturnInvariant

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent31Pump.Raw111Ternary
open BB6Coverage

-- 1RB---_1RC1RA_0RD0LE_1LD1RE_1LF0RC_0RA0LF
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

abbrev O : List Bool := [true,true,true,true]
abbrev Z : List Bool := [false,false,false,false]
abbrev T₁ : List Bool := [false,true,false,false]
abbrev T₂ : List Bool := [true,false,true,false]
abbrev E₁ : List Bool := [false,true,false]
abbrev E₂ : List Bool := [true,false,true]

def base (n : Nat) (R : List Bool) : Z0 :=
  ⟨0,false :: (rep O n ++ [false]),R⟩

/-- Low-order ternary digits 0000, 0100, 1010 and the two final carry forms. -/
inductive Good : List Bool → Prop
  | nil : Good []
  | t0 {R} : Good R → Good (Z ++ R)
  | t1 {R} : Good R → Good (T₁ ++ R)
  | t2 {R} : Good R → Good (T₂ ++ R)
  | end1 : Good E₁
  | end2 : Good E₂

theorem zeroPrefix (n : Nat) (R : List Bool) (h : Good R) :
    Good (rep Z n ++ R) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simpa only [rep,List.append_assoc] using Good.t0 ih

theorem zeroShift (n : Nat) (R : List Bool) :
    rep Z n ++ false::R = false::(rep Z n ++ R) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,List.append_assoc]
    rw [ih]
    rfl

theorem erase (L R : List Bool) :
    run0 table 4 ⟨5,O++L,R⟩ = some ⟨5,L,Z++R⟩ := by rfl

theorem scan (n : Nat) (R : List Bool) :
    run0 table (4*n+1) ⟨5,rep O n ++ [false],false::R⟩ =
      some (base 0 (rep Z n ++ R)) := by
  have h := sweepL table 5 [] [] O Z 4 erase n [false] (false::R)
  simp only [List.nil_append] at h
  rw [zeroShift n R] at h
  have h' : run0 table 1 ⟨5,[false],false::(rep Z n ++ R)⟩ =
      some (base 0 (rep Z n ++ R)) := by rfl
  exact join0 h h'

theorem phase0 (L R : List Bool) :
    run0 table 11 ⟨0,false::L,Z++R⟩ =
      some ⟨5,L,false::(T₁++R)⟩ := by rfl
theorem phase1 (L R : List Bool) :
    run0 table 13 ⟨0,false::L,T₁++R⟩ =
      some ⟨5,L,false::(T₂++R)⟩ := by rfl
theorem phaseEmpty (L : List Bool) :
    run0 table 11 ⟨0,false::L,[]⟩ =
      some ⟨5,L,false::E₁⟩ := by rfl
theorem phaseEnd1 (L : List Bool) :
    run0 table 13 ⟨0,false::L,E₁⟩ =
      some ⟨5,L,false::E₂⟩ := by rfl
theorem carry (n : Nat) (R : List Bool) :
    run0 table 4 (base n (T₂++R)) = some (base (n+1) R) := by rfl
theorem carryEnd (n : Nat) :
    run0 table 4 (base n E₂) = some (base (n+1) []) := by rfl

def Invariant (c : Z0) : Prop := ∃ n R, Good R ∧ c = base n R

theorem returns (c : Z0) (h : Invariant c) :
    ∃ k d, 0 < k ∧ run0 table k c = some d ∧ Invariant d := by
  obtain ⟨n,R,hR,rfl⟩ := h
  cases hR with
  | nil =>
    exact ⟨11+(4*n+1),base 0 _,by omega,
      join0 (phaseEmpty (rep O n ++ [false])) (scan n E₁),
      0,_,zeroPrefix n E₁ Good.end1,rfl⟩
  | t0 h =>
    exact ⟨11+(4*n+1),base 0 _,by omega,
      join0 (phase0 (rep O n ++ [false]) _) (scan n _),
      0,_,zeroPrefix n _ (Good.t1 h),rfl⟩
  | t1 h =>
    exact ⟨13+(4*n+1),base 0 _,by omega,
      join0 (phase1 (rep O n ++ [false]) _) (scan n _),
      0,_,zeroPrefix n _ (Good.t2 h),rfl⟩
  | t2 h =>
    exact ⟨4,base (n+1) _,by omega,carry n _,n+1,_,h,rfl⟩
  | end1 =>
    exact ⟨13+(4*n+1),base 0 _,by omega,
      join0 (phaseEnd1 (rep O n ++ [false])) (scan n E₂),
      0,_,zeroPrefix n E₂ Good.end2,rfl⟩
  | end2 =>
    exact ⟨4,base (n+1) [],by omega,carryEnd n,n+1,[],Good.nil,rfl⟩

theorem entry : run0 table 30 ⟨0,[],[]⟩ = some (base 1 []) := by rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_return table Invariant 30 (base 1 []) entry ⟨1,[],Good.nil,rfl⟩ returns m hm

#print axioms never
end BB6Coverage.Agent31Pump.Raw111Ternary
