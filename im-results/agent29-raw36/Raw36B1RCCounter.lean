import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace BB6.Agent29Raw36B1RCCounter
open BB6Coverage BB6Coverage.Agent31Pump

/-- Binary counter in D with right tape empty. Digits are little endian,
    encoded as 100 (zero) and 101 (one). The unassigned F1 is never read. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨false,false,3⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | _,_ => none

abbrev I : List Bool := [true,false,true]
abbrev O : List Bool := [true,false,false]
abbrev J : List Bool := [false,true,true]
abbrev C : List Bool := [false,true,false]
abbrev H : List Bool := [false,false,true]
abbrev R0 : List Bool := [false,true,false,false,false]
abbrev R1 : List Bool := [true,false,true,false,false,false]

def frame (L : List Bool) : Z0 := ⟨3,H++L,[]⟩
theorem prelude (L : List Bool) :
    run0 table 7 (frame (I++L)) = some ⟨0,[true]++L,R0⟩ := by rfl

theorem carryOne (L R : List Bool) :
    run0 table 5 ⟨0,[true]++I++L,[]++R⟩ =
      some ⟨0,[true]++L,[]++J++R⟩ := by rfl

theorem turnZero (L R : List Bool) :
    run0 table 9 ⟨0,[true]++O++L,R⟩ = some ⟨0,H++L,true::R⟩ := by rfl

theorem turnEnd (R : List Bool) :
    run0 table 7 ⟨0,[true],R⟩ = some ⟨0,H,true::R⟩ := by rfl

theorem returnOne (L R : List Bool) :
    run0 table 7 ⟨0,[false,false]++L,[]++I++R⟩ =
      some ⟨0,[false,false]++C++L,[]++R⟩ := by rfl

theorem finish (L : List Bool) :
    run0 table 10 ⟨0,[false,false]++L,R1⟩ =
      some (frame (O++[true,false]++L)) := by rfl

theorem zero (L : List Bool) :
    run0 table 14 (frame (O++L)) = some (frame (I++L)) := by rfl

theorem rotateR (k : Nat) : true::(rep J k++R0) = rep I k++R1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rep,List.append_assoc,List.cons_append] at *
    exact congrArg (fun l => I++l) ih

theorem rotateL (k : Nat) : [true,false]++rep C k++[true] = rep O k++I := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rep,List.append_assoc] at *
    exact congrArg (fun l => O++l) ih

theorem incrementCarry (k : Nat) (L : List Bool) :
    run0 table (14+12*k) (frame (rep I k++O++L)) =
      some (frame (rep O k++I++L)) := by
  cases k with
  | zero => exact zero L
  | succ k =>
    have h1 := prelude (rep I k++O++L)
    have h2 := sweepL table 0 [true] [] I J 5 carryOne k (O++L) R0
    simp only [List.nil_append,List.append_assoc] at h2
    have h3 := turnZero L (rep J k++R0)
    rw [rotateR] at h3
    have h4 := sweepR table 0 [false,false] [] I C 7 returnOne k ([true]++L) R1
    simp only [List.nil_append,List.append_assoc] at h4
    have h5 := finish (rep C k++[true]++L)
    have he : [true,false]++(rep C k++[true]++L) = rep O k++I++L := by
      simpa only [List.append_assoc] using congrArg (fun l => l++L) (rotateL k)
    have h5' : run0 table 10 ⟨0,[false,false]++rep C k++[true]++L,R1⟩ =
        some (frame (O++rep O k++I++L)) := by
      simp only [List.append_assoc] at h5 he ⊢
      rw [he] at h5
      exact h5
    simp only [List.append_assoc] at h1 h3 h5'
    have H1 := join0 h1 h2
    have H2 := join0 H1 h3
    have H3 := join0 H2 h4
    have H4 := join0 H3 h5'
    simpa only [rep,List.append_assoc,show 7+5*k+9+7*k+10=14+12*(k+1) by omega] using H4

theorem overflow (k : Nat) :
    run0 table (24+12*k) (frame (rep I (k+1))) =
      some (frame (rep O (k+1)++I)) := by
  have h1 := prelude (rep I k)
  have h2 := sweepL table 0 [true] [] I J 5 carryOne k [] R0
  simp only [List.nil_append,List.append_nil,List.append_assoc] at h2
  have h3 := turnEnd (rep J k++R0)
  rw [rotateR] at h3
  have h4 := sweepR table 0 [false,false] [] I C 7 returnOne k [true] R1
  simp only [List.nil_append,List.append_assoc] at h4
  have h5 := finish (rep C k++[true])
  have he : [true,false]++(rep C k++[true]) = rep O k++I := by
    simpa only [List.append_assoc] using rotateL k
  have h5' : run0 table 10 ⟨0,[false,false]++rep C k++[true],R1⟩ =
      some (frame (O++rep O k++I)) := by
    simpa only [List.append_assoc,he] using h5
  have H1 := join0 h1 h2
  have H2 := join0 H1 h3
  have H3 := join0 H2 h4
  have H4 := join0 H3 h5'
  simpa only [rep,List.append_assoc,show 7+5*k+7+7*k+10=24+12*k by omega] using H4

def digits : List Bool → List Bool
  | [] => []
  | b::bs => (if b then I else O) ++ digits bs

theorem digits_append (a b : List Bool) : digits (a++b) = digits a++digits b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,digits,ih,List.append_assoc]

theorem digits_rep (b : Bool) (k : Nat) :
    digits (List.replicate k b) = rep (if b then I else O) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ,digits,rep,ih]

theorem leading (w : List Bool) :
    (∃ k L, w = List.replicate k true ++ false::L) ∨
    (∃ k, w = List.replicate k true) := by
  induction w with
  | nil => exact Or.inr ⟨0,rfl⟩
  | cons b bs ih =>
    cases b with
    | false => exact Or.inl ⟨0,bs,rfl⟩
    | true =>
      rcases ih with ⟨k,L,h⟩ | ⟨k,h⟩
      · exact Or.inl ⟨k+1,L,by simp [List.replicate_succ,h]⟩
      · exact Or.inr ⟨k+1,by simp [List.replicate_succ,h]⟩

theorem advance (w : List Bool) (hw : w ≠ []) :
    ∃ t w', 0<t ∧ w'≠[] ∧
      run0 table t (frame (digits w)) = some (frame (digits w')) := by
  rcases leading w with ⟨k,L,rfl⟩ | ⟨k,rfl⟩
  · refine ⟨14+12*k,List.replicate k false++true::L,by omega,by simp,?_⟩
    simpa only [digits_append,digits_rep,digits,ite_true,Bool.false_eq_true,ite_false,List.append_assoc] using incrementCarry k (digits L)
  · cases k with
    | zero => exact False.elim (hw rfl)
    | succ k =>
      refine ⟨24+12*k,List.replicate (k+1) false++[true],by omega,by simp,?_⟩
      simpa only [digits_append,digits_rep,digits,ite_true,Bool.false_eq_true,ite_false,List.append_nil] using overflow k

theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (frame (digits [true])) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  let next : {w : List Bool // w ≠ []} → {w : List Bool // w ≠ []} := fun w =>
    ⟨Classical.choose (Classical.choose_spec (advance w.val w.property)),
      (Classical.choose_spec (Classical.choose_spec (advance w.val w.property))).2.1⟩
  let cost : {w : List Bool // w ≠ []} → Nat := fun w => Classical.choose (advance w.val w.property)
  let seq : Nat → {w : List Bool // w ≠ []} := Nat.rec ⟨[true],by simp⟩ (fun _ w => next w)
  apply never_of_growth table (fun n => frame (digits (seq n).val)) 17 (fun n => cost (seq n)) entry
  · intro n
    exact (Classical.choose_spec (Classical.choose_spec (advance (seq n).val (seq n).property))).1
  · intro n
    exact (Classical.choose_spec (Classical.choose_spec (advance (seq n).val (seq n).property))).2.2
  · exact hm
#print axioms incrementCarry
#print axioms overflow
#print axioms never
end BB6.Agent29Raw36B1RCCounter
