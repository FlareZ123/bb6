import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.BinaryCarry
open BB6Coverage BB6Coverage.Agent31Pump

/-- A closed family of finite configurations with positive-cost returns supplies
    arbitrarily long live prefixes. No choice of a particular counter value
    or growth rate is needed. -/
theorem never_of_returns (p : PartialMachine) (Good : Z0 → Prop)
    (z : Z0) (entry : Nat) (hentry : run0 p entry ⟨0,[],[]⟩ = some z)
    (hgood : Good z)
    (next : ∀ z, Good z → ∃ t z', 0<t ∧ run0 p t z = some z' ∧ Good z')
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have arbitrary : ∀ k, ∃ t z, k≤t ∧ run0 p t ⟨0,[],[]⟩ = some z ∧ Good z := by
    intro k
    induction k with
    | zero => exact ⟨entry,z,by omega,hentry,hgood⟩
    | succ k ih =>
      obtain ⟨t,z,ht,hr,hz⟩ := ih
      obtain ⟨d,z',hd,hs,hz'⟩ := next z hz
      exact ⟨t+d,z',by omega,join0 hr hs,hz'⟩
  intro n
  obtain ⟨t,z,ht,hr,hz⟩ := arbitrary n
  have hproj : (BB6Coverage.Agent50Zipper.zrun p t start).map project = some z :=
    (run_project p t start).trans hr
  cases h : BB6Coverage.Agent50Zipper.zrun p t start with
  | none => simp [h] at hproj
  | some z' =>
    have H := BB6Coverage.Agent50Zipper.zrun_sound p m hm t start z' h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

namespace Counter181
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def U : List Bool := [true,true,true,true,true]
def Z : List Bool := [false,false,false,false,false]
def digit (b : Bool) : List Bool := [false,false,b,false,false]
def enc : List Bool → List Bool
  | [] => [false,false,true]
  | b::bs => digit b ++ enc bs

def phase (k : Nat) (xs : List Bool) : Z0 :=
  ⟨0,[false]++rep U k++[false],enc xs⟩

theorem enc_zeros (k : Nat) (xs : List Bool) :
    enc (List.replicate k false ++ xs) = rep Z k ++ enc xs := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ,List.cons_append,enc,rep,ih,List.append_assoc]; rfl

theorem comm0 (k : Nat) : [false]++rep Z k = rep Z k++[false] :=
  rotate false [false,false,false,false] k

theorem eraseBlock (L R : List Bool) :
    run0 table 5 ⟨5,U++L,R⟩ = some ⟨5,L,Z++R⟩ := by rfl

theorem erase (k : Nat) (R : List Bool) :
    run0 table (5*k+1) ⟨5,rep U k++[false],[false]++R⟩ =
      some ⟨0,[false,false],rep Z k++R⟩ := by
  have h := sweepL table 5 [] [] U Z 5 eraseBlock k [false] ([false]++R)
  simp only [List.nil_append] at h
  have h' : run0 table (5*k) ⟨5,rep U k++[false],[false]++R⟩ =
      some ⟨5,[false],[false]++(rep Z k++R)⟩ := by
    have he : rep Z k ++ ([false]++R) = [false]++(rep Z k++R) := by
      calc
        _ = (rep Z k++[false])++R := by rw [List.append_assoc]
        _ = ([false]++rep Z k)++R := by rw [comm0 k]
        _ = _ := by rw [List.append_assoc]
    rw [he] at h
    exact h
  have h1 : run0 table 1 ⟨5,[false],[false]++(rep Z k++R)⟩ =
      some ⟨0,[false,false],rep Z k++R⟩ := by rfl
  exact join0 h' h1

theorem scanOne (L R : List Bool) :
    run0 table 7 ⟨0,[false]++L,digit true++R⟩ =
      some ⟨0,[false]++U++L,R⟩ := by rfl

theorem scanSentinel (L : List Bool) :
    run0 table 7 ⟨0,[false]++L,enc []⟩ =
      some ⟨0,[false]++U++L,[]⟩ := by rfl

theorem finishZero (L R : List Bool) :
    run0 table 13 ⟨0,[false]++L,digit false++R⟩ =
      some ⟨5,L,[false]++digit true++R⟩ := by rfl

theorem finishEmpty (L : List Bool) :
    run0 table 13 ⟨0,[false]++L,[]⟩ =
      some ⟨5,L,[false]++enc []⟩ := by rfl

theorem resetEmpty (k : Nat) :
    run0 table (13+(5*k+1)) ⟨0,[false]++rep U k++[false],[]⟩ =
      some (phase 0 (List.replicate k false)) := by
  have h := finishEmpty (rep U k++[false])
  have h' : run0 table 13 ⟨0,[false]++rep U k++[false],[]⟩ =
      some ⟨5,rep U k++[false],[false]++enc []⟩ := by
    simpa only [List.append_assoc] using h
  have H := join0 h' (erase k (enc []))
  have he := enc_zeros k []
  rw [List.append_nil] at he
  change run0 table (13+(5*k+1)) ⟨0,[false]++rep U k++[false],[]⟩ =
      some ⟨0,[false,false],enc (List.replicate k false)⟩
  rw [he]
  exact H

theorem resetZero (k : Nat) (xs : List Bool) :
    run0 table (13+(5*k+1)) (phase k (false::xs)) =
      some (phase 0 (List.replicate k false ++ true::xs)) := by
  have h := finishZero (rep U k++[false]) (enc xs)
  have h' : run0 table 13 (phase k (false::xs)) =
      some ⟨5,rep U k++[false],[false]++(digit true++enc xs)⟩ := by
    simpa only [phase,enc,List.append_assoc] using h
  have H := join0 h' (erase k (digit true++enc xs))
  change run0 table (13+(5*k+1)) (phase k (false::xs)) =
      some ⟨0,[false,false],enc (List.replicate k false++true::xs)⟩
  rw [enc_zeros]
  exact H

theorem resume (xs : List Bool) (k : Nat) :
    ∃ t ys, 0<t ∧ run0 table t (phase k xs) = some (phase 0 ys) := by
  induction xs generalizing k with
  | nil =>
    have h := scanSentinel (rep U k++[false])
    have h' : run0 table 7 (phase k []) =
        some ⟨0,[false]++rep U (k+1)++[false],[]⟩ := by
      simpa only [phase,rep,List.append_assoc] using h
    exact ⟨7+(13+(5*(k+1)+1)),List.replicate (k+1) false,by omega,
      join0 h' (resetEmpty (k+1))⟩
  | cons b xs ih =>
    cases b with
    | false => exact ⟨13+(5*k+1),List.replicate k false++true::xs,by omega,resetZero k xs⟩
    | true =>
      have h := scanOne (rep U k++[false]) (enc xs)
      have h' : run0 table 7 (phase k (true::xs)) = some (phase (k+1) xs) := by
        simpa only [phase,enc,rep,List.append_assoc] using h
      obtain ⟨t,ys,ht,hr⟩ := ih (k+1)
      exact ⟨7+t,ys,by omega,join0 h' hr⟩

theorem entry : run0 table 14 ⟨0,[],[]⟩ = some (phase 0 []) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_returns table (fun z => ∃ xs, z = phase 0 xs) (phase 0 []) 14 entry
    ⟨[],rfl⟩ (by
      intro z hz
      obtain ⟨xs,rfl⟩ := hz
      obtain ⟨t,ys,ht,hr⟩ := resume xs 0
      exact ⟨t,phase 0 ys,ht,hr,ys,rfl⟩) m hm
#print axioms never
end Counter181
namespace Counter184
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def U : List Bool := [true,true,true,true]
def Z : List Bool := [false,false,false,false]
def digit (b : Bool) : List Bool := [false,false,false,b]
def marked (b : Bool) : List Bool := [true,true,true,b]
def enc : List Bool → List Bool
  | [] => []
  | b::bs => digit b ++ enc bs
def mark : List Bool → List Bool
  | [] => [true,true,true]
  | b::bs => marked b ++ enc bs

def good (xs : List Bool) : Z0 := ⟨0,[false,false],enc xs⟩
def phase (k : Nat) (xs : List Bool) : Z0 :=
  ⟨0,[false]++rep U k++[false],mark xs⟩

theorem enc_zeros (k : Nat) (xs : List Bool) :
    enc (List.replicate k false ++ xs) = rep Z k ++ enc xs := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ,List.cons_append,enc,rep,ih,List.append_assoc]; rfl

theorem comm0 (k : Nat) : [false]++rep Z k = rep Z k++[false] :=
  rotate false [false,false,false] k

theorem eraseBlock (L R : List Bool) :
    run0 table 4 ⟨5,U++L,R⟩ = some ⟨5,L,Z++R⟩ := by rfl

theorem erase (k : Nat) (R : List Bool) :
    run0 table (4*k+1) ⟨5,rep U k++[false],[false]++R⟩ =
      some ⟨0,[false,false],rep Z k++R⟩ := by
  have h := sweepL table 5 [] [] U Z 4 eraseBlock k [false] ([false]++R)
  simp only [List.nil_append] at h
  have h' : run0 table (4*k) ⟨5,rep U k++[false],[false]++R⟩ =
      some ⟨5,[false],[false]++(rep Z k++R)⟩ := by
    have he : rep Z k ++ ([false]++R) = [false]++(rep Z k++R) := by
      calc
        _ = (rep Z k++[false])++R := by rw [List.append_assoc]
        _ = ([false]++rep Z k)++R := by rw [comm0 k]
        _ = _ := by rw [List.append_assoc]
    rw [he] at h
    exact h
  have h1 : run0 table 1 ⟨5,[false],[false]++(rep Z k++R)⟩ =
      some ⟨0,[false,false],rep Z k++R⟩ := by rfl
  exact join0 h' h1

theorem begin (xs : List Bool) : run0 table 8 (good xs) = some (phase 0 xs) := by
  cases xs with
  | nil => rfl
  | cons b xs => cases b <;> rfl

theorem scanOne (L : List Bool) (xs : List Bool) :
    run0 table 12 ⟨0,[false]++L,marked true++enc xs⟩ =
      some ⟨0,[false]++U++L,mark xs⟩ := by
  cases xs with
  | nil => rfl
  | cons b xs => cases b <;> rfl

theorem finishZero (L R : List Bool) :
    run0 table 9 ⟨0,[false]++L,marked false++R⟩ =
      some ⟨5,L,[false]++digit true++R⟩ := by rfl

theorem finishEmpty (L : List Bool) :
    run0 table 9 ⟨0,[false]++L,mark []⟩ =
      some ⟨5,L,[false]++digit true⟩ := by rfl

theorem resetEmpty (k : Nat) :
    run0 table (9+(4*k+1)) (phase k []) =
      some (good (List.replicate k false ++ [true])) := by
  have h := finishEmpty (rep U k++[false])
  have h' : run0 table 9 (phase k []) =
      some ⟨5,rep U k++[false],[false]++digit true⟩ := by
    simpa only [phase,List.append_assoc] using h
  have H := join0 h' (erase k (digit true))
  simpa only [good,enc_zeros,enc,List.append_nil] using H

theorem resetZero (k : Nat) (xs : List Bool) :
    run0 table (9+(4*k+1)) (phase k (false::xs)) =
      some (good (List.replicate k false ++ true::xs)) := by
  have h := finishZero (rep U k++[false]) (enc xs)
  have h' : run0 table 9 (phase k (false::xs)) =
      some ⟨5,rep U k++[false],[false]++(digit true++enc xs)⟩ := by
    simpa only [phase,mark,List.append_assoc] using h
  have H := join0 h' (erase k (digit true++enc xs))
  simpa only [good,enc_zeros,enc] using H

theorem resume (xs : List Bool) (k : Nat) :
    ∃ t ys, 0<t ∧ run0 table t (phase k xs) = some (good ys) := by
  induction xs generalizing k with
  | nil => exact ⟨9+(4*k+1),List.replicate k false++[true],by omega,resetEmpty k⟩
  | cons b xs ih =>
    cases b with
    | false => exact ⟨9+(4*k+1),List.replicate k false++true::xs,by omega,resetZero k xs⟩
    | true =>
      have h := scanOne (rep U k++[false]) xs
      have h' : run0 table 12 (phase k (true::xs)) = some (phase (k+1) xs) := by
        simpa only [phase,mark,rep,List.append_assoc] using h
      obtain ⟨t,ys,ht,hr⟩ := ih (k+1)
      exact ⟨12+t,ys,by omega,join0 h' hr⟩

theorem entry : run0 table 18 ⟨0,[],[]⟩ = some (good [true]) := by rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_returns table (fun z => ∃ xs, z = good xs) (good [true]) 18 entry
    ⟨[true],rfl⟩ (by
      intro z hz
      obtain ⟨xs,rfl⟩ := hz
      obtain ⟨t,ys,ht,hr⟩ := resume xs 0
      exact ⟨8+t,good ys,by omega,join0 (begin xs) hr,ys,rfl⟩) m hm
#print axioms never
end Counter184
end BB6.Agent19Raw40.BinaryCarry
