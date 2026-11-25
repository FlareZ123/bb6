import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw121TripleCounter
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev E (L R : List Bool) : Z0 := ⟨4,L,R⟩
abbrev T : List Bool := [true,true,true]
abbrev P : List Bool := [true,true,false]
def pad (t : Bool) : List Bool := if t then [false] else []
def X (a : Nat) (t : Bool) (R : List Bool) := E (false::(rep T a++true::pad t)) R
def Y (b : Nat) (t : Bool) := E (false::(rep T b++true::true::pad t)) []
inductive Good : List Bool → Prop
  | terminal (b : Nat) : Good (rep T b)
  | more (b : Nat) (R : List Bool) : Good R → Good (rep T b++(P++R))

theorem good_T {R} (h : Good R) : Good (T++R) := by
  cases h with
  | terminal b => exact Good.terminal (b+1)
  | more b R h => simpa only [rep,List.append_assoc] using Good.more (b+1) R h

theorem good_P {R} (h : Good R) : Good (P++R) := Good.more 0 R h

theorem good_prefix (n : Nat) {R} (h : Good R) : Good (rep P n++(T++R)) := by
  induction n with
  | zero => exact good_T h
  | succ n ih => simpa only [rep,List.append_assoc] using good_P ih

theorem commute (n : Nat) (L : List Bool) : true::(rep T n++L) = rep T n++true::L := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,List.cons_append,List.nil_append] at *; rw [← ih]

theorem a_one (L R : List Bool) : run0 table 3 (A (T++L) R) = some (A L (P++R)) := by rfl
theorem a_many (n : Nat) (L R : List Bool) : run0 table (3*n) (A (rep T n++L) R) = some (A L (rep P n++R)) := by
  simpa only [List.nil_append] using sweepL table 0 [] [] T P 3 a_one n L R

theorem e_one (L R : List Bool) : run0 table 3 (E (true::L) (T++R)) = some (E (true::(T++L)) R) := by rfl
theorem e_many (n : Nat) (L R : List Bool) : run0 table (3*n) (E (true::L) (rep T n++R)) = some (E (true::(rep T n++L)) R) := by
  simpa only [List.nil_append,List.cons_append] using sweepR table 4 [true] [] T T 3 e_one n L R

theorem x_zero (t : Bool) (R : List Bool) : run0 table 4 (X 0 t R) = some (E [true,true,false] R) := by cases t <;> rfl

theorem x_terminal (b : Nat) (t : Bool) : run0 table (4+3*b+1) (X 0 t (rep T b)) = some (Y b true) := by
  have hscan : run0 table (3*b) (E [true,true,false] (rep T b)) = some (E (true::(rep T b++[true,false])) []) := by
    simpa only [List.append_nil] using e_many b [true,false] []
  have h := join0 (x_zero t (rep T b)) hscan
  have h1 : run0 table 1 (E (true::(rep T b++[true,false])) []) = some (Y b true) := by
    change some (E (false::true::(rep T b++[true,false])) []) = _
    rw [commute]; rfl
  exact join0 h h1

theorem x_more (b : Nat) (t : Bool) (R : List Bool) : run0 table (4+3*b+3) (X 0 t (rep T b++(P++R))) = some (X (b+1) true R) := by
  have h := join0 (x_zero t (rep T b++(P++R))) (e_many b [true,false] (P++R))
  have h1 : run0 table 3 (E (true::(rep T b++[true,false])) (P++R)) = some (X (b+1) true R) := by rfl
  exact join0 h h1

theorem x_succ (a : Nat) (t : Bool) (R : List Bool) : run0 table (3+3*a+4) (X (a+1) t R) = some (X 0 true (rep P a++(T++R))) := by
  have h0 : run0 table 3 (X (a+1) t R) = some (A (rep T a++true::true::pad t) (T++R)) := by
    change some (A (true::(rep T a++true::pad t)) (T++R)) = _
    rw [commute]
  have h1 := a_many a (true::true::pad t) (T++R)
  have h2 : run0 table 4 (A (true::true::pad t) (rep P a++(T++R))) = some (X 0 true (rep P a++(T++R))) := by cases t <;> rfl
  exact join0 (join0 h0 h1) h2

theorem y_begin (b : Nat) (t : Bool) : run0 table (3+3*b) (Y b t) = some (A (pad t) (rep P b++T)) := by
  have h0 : run0 table 3 (Y b t) = some (A (rep T b++pad t) T) := by
    unfold Y
    rw [← commute b (true::pad t),← commute b (pad t)]
    rfl
  exact join0 h0 (a_many b (pad t) T)

theorem y_zero (t : Bool) : run0 table 15 (Y 0 t) = some (Y 1 false) := by cases t <;> rfl

theorem y_succ (b : Nat) (t : Bool) : run0 table (3+3*(b+1)+11) (Y (b+1) t) = some (X 1 false (rep P b++T)) := by
  have h0 := y_begin (b+1) t
  have h1 : run0 table 11 (A (pad t) (P++(rep P b++T))) = some (X 1 false (rep P b++T)) := by cases t <;> rfl
  exact join0 (by simpa only [rep,List.append_assoc] using h0) h1

inductive Inv : Z0 → Prop
  | x (a : Nat) (t : Bool) (R : List Bool) : Good R → Inv (X a t R)
  | y (b : Nat) (t : Bool) : Inv (Y b t)

theorem closed {c : Z0} (h : Inv c) : ∃ d k, 0<k ∧ run0 table k c = some d ∧ Inv d := by
  cases h with
  | x a t R h =>
    cases a with
    | zero =>
      cases h with
      | terminal b => exact ⟨_,_,by omega,x_terminal b t,Inv.y b true⟩
      | more b R h => exact ⟨_,_,by omega,x_more b t R,Inv.x (b+1) true R h⟩
    | succ a => exact ⟨_,_,by omega,x_succ a t R,Inv.x 0 true _ (good_prefix a h)⟩
  | y b t =>
    cases b with
    | zero => exact ⟨_,15,by decide,y_zero t,Inv.y 1 false⟩
    | succ b => exact ⟨_,_,by omega,y_succ b t,Inv.x 1 false _ (by
        have h : Good (rep P b++(T++[])) := good_prefix b (Good.terminal 0)
        simpa only [List.append_nil] using h)⟩

theorem entry : run0 table 8 ⟨0,[],[]⟩ = some (X 1 false []) := by rfl
#print axioms closed
#print axioms entry
end BB6.Agent11Raw121TripleCounter
