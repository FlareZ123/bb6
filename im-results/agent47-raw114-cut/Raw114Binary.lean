import SweepPumping

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw114Binary
open BB6Coverage

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,false,3⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def right (n : Nat) : List Bool := true :: rep [true,true] n ++ [false,false,false,false]
def atA (l : List Bool) (n : Nat) : Z0 := ⟨0,l,right n⟩

inductive Good : List Bool → Prop
  | nil : Good []
  | singleton (b : Bool) : Good [b]
  | pair (b : Bool) {l : List Bool} : Good l → Good (b::false::l)

theorem good_prefix (n : Nat) {l : List Bool} (h : Good l) : Good (rep [false,false] n ++ l) := by
  induction n with
  | zero => exact h
  | succ n ih => exact Good.pair false ih

theorem erase (L R : List Bool) :
    run0 table 2 ⟨1,[true]++L,[true,true]++R⟩ =
      some ⟨1,[true]++[false,false]++L,R⟩ := by rfl

theorem gadget (L : List Bool) :
    run0 table 13 ⟨1,true::L,[false,false,false,false]⟩ =
      some (atA L 0) := by rfl

theorem first (l : List Bool) (n : Nat) (h : l.headD false = false) :
    run0 table 1 (atA l n) = some ⟨1,true::true::l.tail,rep [true,true] n ++ [false,false,false,false]⟩ := by
  cases l with
  | nil => rfl
  | cons b l => cases b <;> simp_all [atA,right,run0,step0,move0,table]

theorem zero_step (l : List Bool) (n : Nat) (h : l.headD false = false) :
    run0 table (14+2*n) (atA l n) = some (atA (rep [false,false] n ++ true::l.tail) 0) := by
  have H := sweepR table 1 [true] [] [true,true] [false,false] 2 erase n (true::l.tail) [false,false,false,false]
  have H' := join0 (first l n h) (by simpa only [List.cons_append,List.nil_append] using H)
  have H'' := join0 H' (gadget (rep [false,false] n ++ true::l.tail))
  rw [show 1+2*n+13 = 14+2*n by omega] at H''
  exact H''

theorem one_step_pair (l : List Bool) (n : Nat) :
    run0 table 2 (atA (true::false::l) n) = some (atA l (n+1)) := by rfl

theorem one_step_singleton (n : Nat) :
    run0 table 2 (atA [true] n) = some (atA [] (n+1)) := by rfl

structure CountState where
  l : List Bool
  n : Nat

def next (s : CountState) : CountState :=
  if s.l.headD false then ⟨s.l.tail.tail,s.n+1⟩
  else ⟨rep [false,false] s.n ++ true::s.l.tail,0⟩

def cost (s : CountState) : Nat := if s.l.headD false then 2 else 14+2*s.n

def config (s : CountState) : Z0 := atA s.l s.n

theorem next_good (s : CountState) (h : Good s.l) : Good (next s).l := by
  rcases s with ⟨l,n⟩
  cases h with
  | nil => exact good_prefix n (Good.singleton true)
  | singleton b =>
    cases b
    · exact good_prefix n (Good.singleton true)
    · exact Good.nil
  | pair b h =>
    cases b
    · exact good_prefix n (Good.pair true h)
    · exact h

theorem step (s : CountState) (h : Good s.l) : run0 table (cost s) (config s) = some (config (next s)) := by
  rcases s with ⟨l,n⟩
  cases h with
  | nil => exact zero_step [] n rfl
  | singleton b =>
    cases b
    · exact zero_step [false] n rfl
    · exact one_step_singleton n
  | pair b h =>
    cases b
    · exact zero_step _ n rfl
    · exact one_step_pair _ n

def states : Nat → CountState
  | 0 => ⟨[],0⟩
  | n+1 => next (states n)

theorem states_good (n : Nat) : Good (states n).l := by
  induction n with
  | zero => exact Good.nil
  | succ n ih => exact next_good _ ih

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (config (states 0)) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table (fun n => config (states n)) 14 (fun n => cost (states n)) entry
    (by intro n; unfold cost; split <;> omega)
    (fun n => step (states n) (states_good n)) m hm
#print axioms never
end BB6Coverage.Agent31Pump.Raw114Binary
