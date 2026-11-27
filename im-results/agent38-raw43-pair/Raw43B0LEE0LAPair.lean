import SweepPumping
set_option maxHeartbeats 0
namespace BB6.Agent38Raw43B0LEE0LAPair
open BB6Coverage BB6Coverage.Agent31Pump

-- false: M38, true: M39
def table (v : Bool) : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some (if v then ⟨false,true,5⟩ else ⟨false,false,1⟩))
  | _,_ => none

def rep (w : List Bool) : Nat → List Bool
  | 0 => []
  | n+1 => w ++ rep w n

theorem rep_snoc (w : List Bool) (n : Nat) (L : List Bool) : rep w n ++ (w ++ L) = rep w (n+1) ++ L := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep,List.append_assoc,ih]

def X : List Bool := [true,false,false,true,true,false]
def Y : List Bool := [false,false,false,false,false,true]
def z : List Bool := [false,false,false,false,false,false,true]
def mid : Nat → List Bool
  | 0 => [false,false,true,false,false,false,true]
  | n+1 => [false,false,true,false,false,true] ++ rep Y n ++ z

def bottom (p : Bool) : List Bool := if p then [true,false,false,true,true] else [true,true]
def family (p : Bool) (n : Nat) : Z0 :=
  ⟨0,[],(if p then [false,false,true,false,false,true] else [false,false,true]) ++ rep Y n ++ z⟩

theorem enter (v p : Bool) (n : Nat) : run0 (table v) (if p then 14 else 11) (family p n) =
    some ⟨0,false::false::bottom p,mid n⟩ := by
  cases v <;> cases p <;> cases n <;> rfl

theorem forward (v : Bool) (n : Nat) (L : List Bool) :
    ∃ t, run0 (table v) t ⟨0,false::false::L,mid n⟩ =
      some ⟨0,[false,false,true,true,false] ++ rep X n ++ L,[false,false,true,true]⟩ := by
  induction n generalizing L with
  | zero => exact ⟨11,by cases v <;> rfl⟩
  | succ n ih =>
    have h1 : run0 (table v) 14 ⟨0,false::false::L,mid (n+1)⟩ =
      some ⟨0,false::false::(X++L),mid n⟩ := by cases v <;> cases n <;> rfl
    obtain ⟨t,h2⟩ := ih (X++L)
    refine ⟨14+t,?_⟩
    have h := join0 h1 h2
    simpa only [List.append_assoc,rep_snoc] using h

theorem pivot (v p : Bool) (n : Nat) :
    run0 (table v) (if v then 28 else 20) ⟨0,[false,false,true,true,false] ++ rep X n ++ bottom p,[false,false,true,true]⟩ =
      some ⟨1,false::(rep X n ++ bottom p),false::false::z⟩ := by
  cases v <;> cases p <;> cases n <;> rfl

theorem backward (v : Bool) (n : Nat) (L R : List Bool) :
    ∃ t, run0 (table v) t ⟨1,false::(rep X n ++ L),false::false::R⟩ =
      some ⟨1,false::L,false::false::(rep Y n ++ R)⟩ := by
  induction n generalizing R with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    have h1 : run0 (table v) 14 ⟨1,false::(rep X (n+1) ++ L),false::false::R⟩ =
      some ⟨1,false::(rep X n ++ L),false::false::(Y++R)⟩ := by cases v <;> rfl
    obtain ⟨t,h2⟩ := ih (Y++R)
    refine ⟨14+t,?_⟩
    simpa only [rep_snoc] using join0 h1 h2

theorem exit (v p : Bool) (n : Nat) : run0 (table v) (if p then 21 else if v then 20 else 16)
    ⟨1,false::bottom p,false::false::(rep Y n ++ z)⟩ =
    some (family (!p) (if p then n+1 else n)) := by
  cases v <;> cases p <;> rfl

theorem epoch (v p : Bool) (n : Nat) : ∃ t, 0<t ∧ run0 (table v) t (family p n) =
      some (family (!p) (if p then n+1 else n)) := by
  obtain ⟨t,h2⟩ := forward v n (bottom p)
  obtain ⟨u,h4⟩ := backward v n (bottom p) z
  have h := join0 (join0 (join0 (join0 (enter v p n) h2) (pivot v p n)) h4) (exit v p n)
  refine ⟨_,?_,h⟩
  cases v <;> cases p <;> simp <;> omega

theorem live_prefix (v : Bool) (n : Nat) :
    ∃ t p j, n≤t ∧ run0 (table v) t ⟨0,[],[]⟩ = some (family p j) := by
  induction n with
  | zero => cases v
            · exact ⟨58,false,0,by decide,rfl⟩
            · exact ⟨66,false,0,by decide,rfl⟩
  | succ n ih =>
    obtain ⟨t,p,j,ht,h⟩ := ih
    obtain ⟨u,hu,h'⟩ := epoch v p j
    exact ⟨t+u,!p,if p then j+1 else j,by omega,join0 h h'⟩

open BB6Coverage.Agent50Zipper

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  intro n
  obtain ⟨t,p,j,ht,hr⟩ := live_prefix v n
  have hz : (zrun (table v) t start).map project = some (family p j) :=
    (run_project (table v) t start).trans hr
  cases h : zrun (table v) t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound (table v) m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms never
end BB6.Agent38Raw43B0LEE0LAPair
