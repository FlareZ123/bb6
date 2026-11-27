import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B0RCC0LEM2
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

abbrev Digit := Bool × Bool
def word : List Digit → List Bool
  | [] => []
  | (a,b)::xs => false::a::b::word xs

def P : List Bool := [true,false,false]
def Q : List Bool := [false,true,false]
def sectionE (xs : List Digit) (k : Nat) : Z0 := ⟨4,word xs,rep P k++[false]⟩
def good (xs : List Digit) (k : Nat) : Prop := 0 < k ∨ (xs.headD (false,false)).1 = false

theorem word_append (xs ys : List Digit) : word (xs++ys) = word xs++word ys := by
  induction xs with
  | nil => rfl
  | cons d ds ih => cases d; simp [word,ih]

theorem word_repeat (n : Nat) : word (List.replicate n (true,false)) = rep Q n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,word,rep,Q,ih]

private theorem first : run0 table 8 ⟨0,[],[]⟩ = some (sectionE [(false,true)] 0) := by rfl
private theorem carry (xs : List Digit) (k : Nat) :
    run0 table 3 (sectionE ((false,true)::xs) k) = some (sectionE xs (k+1)) := by rfl
private theorem zero (xs : List Digit) :
    run0 table 10 (sectionE ((false,false)::xs) 0) = some (sectionE ((false,true)::xs) 0) := by rfl
private theorem empty_zero : run0 table 10 (sectionE [] 0) = some (sectionE [(false,true)] 0) := by rfl
private theorem enter00 (L R : List Bool) :
    run0 table 4 ⟨4,[false,false,false]++L,R⟩ = some ⟨2,[false,true,true]++L,R⟩ := by rfl
private theorem enterEmpty (R : List Bool) :
    run0 table 4 ⟨4,[],R⟩ = some ⟨2,[false,true,true],R⟩ := by rfl
private theorem enterHigh (b : Bool) (L R : List Bool) :
    run0 table 2 ⟨4,[false,true,b]++L,R⟩ = some ⟨2,[false,false,b]++L,R⟩ := by rfl
private theorem transfer (L R : List Bool) :
    run0 table 3 ⟨2,[false]++L,[]++P++R⟩ = some ⟨2,[false]++P++L,[]++R⟩ := by rfl
private theorem turn (L : List Bool) :
    run0 table 6 ⟨2,[false]++P++L,[false]⟩ = some ⟨4,[false,false,false,false]++L,[false]⟩ := by rfl

/-- Right stack service: all 100 blocks are traversed, then the leading
    zero is restored and the remaining block boundaries are rotated. -/
private theorem service (a b : Bool) (L : List Bool) (k : Nat) :
    run0 table (3*(k+1)+6) ⟨2,[false,a,b]++L,rep P (k+1)++[false]⟩ =
      some ⟨4,[false,false,false]++rep Q k++[false,a,b]++L,[false]⟩ := by
  have h := sweepR table 2 [false] [] P P 3 transfer (k+1) ([a,b]++L) [false]
  have h' : run0 table (3*(k+1)) ⟨2,[false,a,b]++L,rep P (k+1)++[false]⟩ =
      some ⟨2,[false]++P++(rep P k++([a,b]++L)),[false]⟩ := by
    simpa only [List.nil_append,rep,List.append_assoc,List.cons_append] using h
  have t := turn (rep P k++([a,b]++L))
  have z := join0 h' t
  have hr : [false]++rep P k = rep Q k++[false] := rotate false [true,false] k
  have he : [false,false,false,false]++(rep P k++([a,b]++L)) =
      [false,false,false]++rep Q k++[false,a,b]++L := by
    calc
      _ = [false,false,false]++(([false]++rep P k)++([a,b]++L)) := by simp only [List.append_assoc]; rfl
      _ = _ := by rw [hr]; simp only [List.append_assoc]; rfl
  rw [he] at z
  exact z

private theorem service_word (a b : Bool) (xs : List Digit) (k : Nat) :
    run0 table (3*(k+1)+6) ⟨2,[false,a,b]++word xs,rep P (k+1)++[false]⟩ =
      some (sectionE ((false,false)::(List.replicate k (true,false)++(a,b)::xs)) 0) := by
  simpa only [sectionE,word,word_append,word_repeat,rep,List.nil_append,List.append_assoc,List.cons_append] using service a b (word xs) k

private theorem lowBounce (xs : List Digit) (k : Nat) :
    run0 table (4+(3*(k+1)+6)) (sectionE ((false,false)::xs) (k+1)) =
      some (sectionE ((false,false)::(List.replicate k (true,false)++(true,true)::xs)) 0) :=
  join0 (enter00 (word xs) (rep P (k+1)++[false])) (service_word true true xs k)
private theorem emptyBounce (k : Nat) :
    run0 table (4+(3*(k+1)+6)) (sectionE [] (k+1)) =
      some (sectionE ((false,false)::(List.replicate k (true,false)++[(true,true)])) 0) :=
  join0 (enterEmpty (rep P (k+1)++[false])) (service_word true true [] k)
private theorem highBounce (b : Bool) (xs : List Digit) (k : Nat) :
    run0 table (2+(3*(k+1)+6)) (sectionE ((true,b)::xs) (k+1)) =
      some (sectionE ((false,false)::(List.replicate k (true,false)++(false,b)::xs)) 0) :=
  join0 (enterHigh b (word xs) (rep P (k+1)++[false])) (service_word false b xs k)

theorem return_good (xs : List Digit) (k : Nat) (h : good xs k) :
    ∃ n ys j, 0 < n ∧ run0 table n (sectionE xs k) = some (sectionE ys j) ∧ good ys j := by
  cases xs with
  | nil =>
    cases k with
    | zero => exact ⟨10,[(false,true)],0,by decide,empty_zero,Or.inr rfl⟩
    | succ k => exact ⟨_,_,0,by omega,emptyBounce k,Or.inr rfl⟩
  | cons d xs =>
    rcases d with ⟨a,b⟩
    cases a <;> cases b
    · cases k with
      | zero => exact ⟨10,_,0,by decide,zero xs,Or.inr rfl⟩
      | succ k => exact ⟨_,_,0,by omega,lowBounce xs k,Or.inr rfl⟩
    · exact ⟨3,xs,k+1,by decide,carry xs k,Or.inl (by omega)⟩
    · cases k with
      | zero => simp [good] at h
      | succ k => exact ⟨_,_,0,by omega,highBounce false xs k,Or.inr rfl⟩
    · cases k with
      | zero => simp [good] at h
      | succ k => exact ⟨_,_,0,by omega,highBounce true xs k,Or.inr rfl⟩

theorem live_prefix (n : Nat) : ∃ t xs k, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some (sectionE xs k) ∧ good xs k := by
  induction n with
  | zero => exact ⟨8,[(false,true)],0,by decide,first,Or.inr rfl⟩
  | succ n ih =>
    obtain ⟨t,xs,k,ht,hr,hg⟩ := ih
    obtain ⟨d,ys,j,hd,hs,hg'⟩ := return_good xs k hg
    exact ⟨t+d,ys,j,by omega,join0 hr hs,hg'⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,xs,k,ht,hr,hg⟩ := live_prefix n
  have hz : (zrun table t start).map project = some (sectionE xs k) :=
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
end BB6.Agent25Raw43B0RCC0LEM2
