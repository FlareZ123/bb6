import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B0RCC1LEM146
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

abbrev Digit := Bool × Bool
def word : List Digit → List Bool
  | [] => []
  | (a,b)::xs => false::a::b::word xs

def tail (b : Bool) : List Bool := if b then [false,true] else []
def P : List Bool := [false,true,true]
def O : List Bool := [false,false,false]
def sectionE (xs : List Digit) (b : Bool) (k : Nat) : Z0 := ⟨4,word xs++tail b,rep P k++[true]⟩
private theorem word_append (xs ys : List Digit) : word (xs++ys) = word xs++word ys := by
  induction xs with
  | nil => rfl
  | cons d ds ih => cases d; simp [word,ih]
private theorem word_repeat (k : Nat) : word (List.replicate k (false,false)) = rep O k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [word,List.replicate_succ,rep,O,ih]
private theorem first : run0 table 8 ⟨0,[],[]⟩ = some (sectionE [(false,true)] false 0) := by rfl
private theorem carry (L R : List Bool) :
    run0 table 3 ⟨4,[false,true,true]++L,R⟩ = some ⟨4,L,P++R⟩ := by rfl
private theorem enter00 (L R : List Bool) :
    run0 table 2 ⟨4,[false,false,false]++L,R⟩ = some ⟨1,[true,true,false]++L,R⟩ := by rfl
private theorem enter10 (L R : List Bool) :
    run0 table 4 ⟨4,[false,true,false]++L,R⟩ = some ⟨1,[true,false,true]++L,R⟩ := by rfl
private theorem enter01 (L R : List Bool) :
    run0 table 2 ⟨4,[false,false,true]++L,R⟩ = some ⟨1,[true,true,true]++L,R⟩ := by rfl
private theorem enterEmpty (R : List Bool) :
    run0 table 2 ⟨4,[],R⟩ = some ⟨1,[true,true],R⟩ := by rfl
private theorem enterShort (R : List Bool) :
    run0 table 4 ⟨4,[false,true],R⟩ = some ⟨1,[true,false,true],R⟩ := by rfl
private theorem transfer (L R : List Bool) :
    run0 table 3 ⟨1,[true]++L,[]++P++R⟩ = some ⟨1,[true]++O++L,[]++R⟩ := by rfl
private theorem finish (L : List Bool) :
    run0 table 2 ⟨1,[true]++L,[true]⟩ = some ⟨4,[false]++L,[true]⟩ := by rfl
private theorem service (L : List Bool) (k : Nat) :
    run0 table (3*k+2) ⟨1,[true]++L,rep P k++[true]⟩ = some ⟨4,rep O k++[false]++L,[true]⟩ := by
  have h := sweepR table 1 [true] [] P O 3 transfer k L [true]
  have h' : run0 table (3*k) ⟨1,[true]++L,rep P k++[true]⟩ = some ⟨1,[true]++(rep O k++L),[true]⟩ := by
    simpa only [List.nil_append,List.append_assoc] using h
  have z := join0 h' (finish (rep O k++L))
  have hr : [false]++rep O k = rep O k++[false] := rotate false [false,false] k
  simpa only [List.append_assoc,← List.append_assoc [false] (rep O k),hr] using z

theorem return_step (xs : List Digit) (b : Bool) (k : Nat) :
    ∃ n ys c j, 0 < n ∧ run0 table n (sectionE xs b k) = some (sectionE ys c j) := by
  cases xs with
  | nil =>
    cases b
    · refine ⟨2+(3*k+2),List.replicate k (false,false),true,0,by omega,?_⟩
      have z := join0 (enterEmpty (rep P k++[true])) (service [true] k)
      simpa only [sectionE,word,tail,ite_true,ite_false,Bool.false_eq_true,word_repeat,rep,List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using z
    · refine ⟨4+(3*k+2),List.replicate k (false,false)++[(false,true)],false,0,by omega,?_⟩
      have z := join0 (enterShort (rep P k++[true])) (service [false,true] k)
      simpa only [sectionE,word,tail,ite_true,ite_false,Bool.false_eq_true,word_repeat,word_append,rep,List.nil_append,List.append_nil,List.append_assoc,List.cons_append] using z
  | cons d xs =>
    rcases d with ⟨a,e⟩
    cases a <;> cases e
    · refine ⟨2+(3*k+2),List.replicate k (false,false)++(true,false)::xs,b,0,by omega,?_⟩
      have z := join0 (enter00 (word xs++tail b) (rep P k++[true])) (service ([true,false]++word xs++tail b) k)
      simpa only [sectionE,word,word_repeat,word_append,rep,List.nil_append,List.append_assoc,List.cons_append] using z
    · refine ⟨2+(3*k+2),List.replicate k (false,false)++(true,true)::xs,b,0,by omega,?_⟩
      have z := join0 (enter01 (word xs++tail b) (rep P k++[true])) (service ([true,true]++word xs++tail b) k)
      simpa only [sectionE,word,word_repeat,word_append,rep,List.nil_append,List.append_assoc,List.cons_append] using z
    · refine ⟨4+(3*k+2),List.replicate k (false,false)++(false,true)::xs,b,0,by omega,?_⟩
      have z := join0 (enter10 (word xs++tail b) (rep P k++[true])) (service ([false,true]++word xs++tail b) k)
      simpa only [sectionE,word,word_repeat,word_append,rep,List.nil_append,List.append_assoc,List.cons_append] using z
    · refine ⟨3,xs,b,k+1,by decide,?_⟩
      simpa only [sectionE,word,rep,List.append_assoc,List.cons_append,List.nil_append] using carry (word xs++tail b) (rep P k++[true])

theorem live_prefix (n : Nat) : ∃ t xs b k, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some (sectionE xs b k) := by
  induction n with
  | zero => exact ⟨8,[(false,true)],false,0,by decide,first⟩
  | succ n ih =>
    obtain ⟨t,xs,b,k,ht,hr⟩ := ih
    obtain ⟨d,ys,c,j,hd,hs⟩ := return_step xs b k
    exact ⟨t+d,ys,c,j,by omega,join0 hr hs⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,xs,b,k,ht,hr⟩ := live_prefix n
  have hz : (zrun table t start).map project = some (sectionE xs b k) :=
    (run_project table t start).trans hr
  cases h : zrun table t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound table m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl
#print axioms live_prefix
#print axioms never
end BB6.Agent25Raw43B0RCC1LEM146
