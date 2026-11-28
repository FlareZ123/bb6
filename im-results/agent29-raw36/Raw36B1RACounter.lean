import ClosedGrowth
import Raw36B1RCCounter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace BB6.Agent29Raw36B1RACounter
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent29ClosedGrowth

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨false,false,3⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none
abbrev I : List Bool := [false,true]
abbrev O : List Bool := [false,false]
abbrev J : List Bool := [true,false]
abbrev T : List Bool := [true,true]
abbrev R0 : List Bool := [false,true,true,false,false,false,false,true,false,false]
def frame (L : List Bool) : Z0 := ⟨5,[true]++L,R0⟩

theorem pre (L : List Bool) : run0 table 8 ⟨5,[true,false]++L,R0⟩ = some ⟨5,I++L,R0⟩ := by rfl

theorem carryOne (L R : List Bool) : run0 table 4 ⟨5,I++J++L,R⟩ = some ⟨5,I++L,T++R⟩ := by rfl

theorem carryEnd (R : List Bool) : run0 table 4 ⟨5,I++[true],R⟩ = some ⟨5,I,T++R⟩ := by rfl

theorem zero (L R : List Bool) : run0 table 4 ⟨5,I++[false]++L,R⟩ = some ⟨5,[true]++I++L,R⟩ := by rfl

theorem turnEnd (R : List Bool) : run0 table 4 ⟨5,I,R⟩ = some ⟨5,[true]++I,R⟩ := by rfl

theorem returnOne (L R : List Bool) : run0 table 2 ⟨5,[true]++L,[]++T++R⟩ = some ⟨5,[true]++O++L,[]++R⟩ := by rfl

theorem incrementCarry (n : Nat) (L : List Bool) :
    run0 table (12+6*n) (frame (rep I n++O++L)) = some (frame (rep O n++I++L)) := by
  have he : rep I n++[false] = [false]++rep J n := (rotate false [true] n).symm
  have h1 := pre (rep J n++[false]++L)
  have h2 := sweepL table 5 I [] J T 4 carryOne n ([false]++L) R0
  have h3 := zero L (rep T n++R0)
  have h4 := sweepR table 5 [true] [] T O 2 returnOne n (I++L) R0
  simp only [List.nil_append,List.append_assoc] at h1 h2 h3 h4
  have h := join0 (join0 (join0 h1 h2) h3) h4
  simp only [frame,List.append_assoc] at ⊢
  rw [← List.append_assoc (rep I n) O L]
  have he' : rep I n++O = [false]++rep J n++[false] := by
    simpa only [O,List.append_assoc,List.cons_append,List.nil_append] using congrArg (fun x => x++[false]) he
  rw [he']
  simpa only [List.append_assoc,List.cons_append,List.nil_append,show 8+4*n+4+2*n=12+6*n by omega] using h

theorem overflow (n : Nat) :
    run0 table (18+6*n) (frame (rep I (n+1))) = some (frame (rep O (n+1)++I)) := by
  have he : rep I (n+1) = [false]++rep J n++[true] := by
    have h : rep I (n+1) = rep I n++I := by rw [rep_add];rfl
    rw [h]
    simpa only [I,List.append_assoc,List.cons_append,List.nil_append] using congrArg (fun x=>x++[true]) (rotate false [true] n).symm
  have h1 := pre (rep J n++[true])
  have h2 := sweepL table 5 I [] J T 4 carryOne n [true] R0
  have h3 := carryEnd (rep T n++R0)
  have h4 := turnEnd (T++rep T n++R0)
  have h5 := sweepR table 5 [true] [] T O 2 returnOne (n+1) I R0
  simp only [List.nil_append,List.append_assoc] at h1 h2 h3 h4 h5
  have h4' : run0 table 4 ⟨5,I,T++rep T n++R0⟩ = some ⟨5,[true]++I,rep T (n+1)++R0⟩ := by
    simpa only [rep,List.append_assoc] using h4
  have h := join0 (join0 (join0 (join0 h1 h2) h3) h4') h5
  rw [show 8+4*n+4+4+2*(n+1)=18+6*n by omega] at h
  simpa only [frame,he,List.append_assoc,List.cons_append,List.nil_append] using h

def digits : List Bool → List Bool
  | [] => []
  | b::bs => (if b then I else O)++digits bs

theorem digits_append (a b : List Bool) : digits (a++b) = digits a++digits b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,digits,ih,List.append_assoc]

theorem digits_rep (b : Bool) (n : Nat) : digits (List.replicate n b) = rep (if b then I else O) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,digits,rep,ih]

def inv (z : Z0) : Prop := ∃ w : List Bool, w ≠ [] ∧ z = frame (digits w)
theorem first : run0 table 64 ⟨0,[],[]⟩ = some (frame (digits [true])) := by rfl

theorem next (z : Z0) (hz : inv z) : ∃ t z', 0<t ∧ run0 table t z = some z' ∧ inv z' := by
  obtain ⟨w,hw,rfl⟩ := hz
  rcases BB6.Agent29Raw36B1RCCounter.leading w with ⟨k,L,rfl⟩ | ⟨k,rfl⟩
  · let w' := List.replicate k false++true::L
    refine ⟨12+6*k,frame (digits w'),by omega,?_,⟨w',by simp [w'],rfl⟩⟩
    simpa only [w',digits_append,digits_rep,digits,ite_true,Bool.false_eq_true,ite_false,List.append_assoc] using incrementCarry k (digits L)
  · cases k with
    | zero => exact False.elim (hw rfl)
    | succ k =>
      let w' := List.replicate (k+1) false++[true]
      refine ⟨18+6*k,frame (digits w'),by omega,?_,⟨w',by simp [w'],rfl⟩⟩
      simpa only [w',digits_append,digits_rep,digits,ite_true,Bool.false_eq_true,ite_false,List.append_nil] using overflow k

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_invariant table inv 64 (frame (digits [true])) first ⟨[true],by simp,rfl⟩ next m hm
#print axioms never
end BB6.Agent29Raw36B1RACounter
