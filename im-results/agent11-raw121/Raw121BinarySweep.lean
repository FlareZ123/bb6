import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw121BinarySweep
open BB6Coverage BB6Coverage.Agent31Pump
inductive V | a | f deriving DecidableEq

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some (match v with | .a => ⟨true,false,0⟩ | .f => ⟨true,false,5⟩))
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev E (L R : List Bool) : Z0 := ⟨4,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
abbrev U : List Bool := [true]
abbrev Z : List Bool := [false]
abbrev P : List Bool := [false,true]
abbrev Q : List Bool := [true,false]
def fam (n j : Nat) (R : List Bool) := E (false::(rep U (j+4)++rep P n)) R

theorem first (v : V) (L R : List Bool) :
    run0 (table v) 2 (E (false::true::L) R) = some (F L (false::true::R)) := by cases v <;> rfl

theorem f_one (v : V) (L R : List Bool) :
    run0 (table v) 1 (F (true::L) R) = some (F L (false::R)) := by rfl

theorem f_many (v : V) (j : Nat) (L R : List Bool) :
    run0 (table v) j (F (rep U j++L) R) = some (F L (rep Z j++R)) := by
  simpa only [List.nil_append,Nat.one_mul] using sweepL (table v) 5 [] [] U Z 1 (f_one v) j L R

theorem f_pair (v : V) (L R : List Bool) :
    run0 (table v) 2 (F (P++L) R) = some (F L (P++R)) := by rfl

theorem f_pairs (v : V) (n : Nat) (R : List Bool) :
    run0 (table v) (2*n) (F (rep P n) R) = some (F [] (rep P n++R)) := by
  simpa only [List.nil_append,List.append_nil] using sweepL (table v) 5 [] [] P P 2 (f_pair v) n [] R

theorem turn (v : V) (R : List Bool) :
    run0 (table v) 1 (F [] R) = some (A [] (true::R)) := by rfl

theorem a_pair (v : V) (L R : List Bool) :
    run0 (table v) 2 (A (false::L) (Q++R)) = some (A (false::(P++L)) R) := by rfl

theorem a_many (v : V) (n : Nat) (L R : List Bool) :
    run0 (table v) (2*n) (A (false::L) (rep Q n++R)) = some (A (false::(rep P n++L)) R) := by
  simpa only [List.nil_append,List.cons_append] using sweepR (table v) 0 [false] [] Q P 2 (a_pair v) n L R

theorem rotate_input (n : Nat) (R : List Bool) :
    true::(rep P n++false::R) = rep Q (n+1)++R := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,List.cons_append,List.nil_append,List.append_assoc] at *; rw [← ih]

theorem a_cross (v : V) (n : Nat) (R : List Bool) :
    run0 (table v) (2+2*n) (A [] (true::(rep P n++false::R))) = some (A (false::rep P (n+1)) R) := by
  rw [rotate_input]
  have h0 : run0 (table v) 2 (A [] (Q++(rep Q n++R))) = some (A [false,false,true] (rep Q n++R)) := by rfl
  have h1 := a_many v n P R
  have h := join0 h0 h1
  simpa only [rep,List.append_assoc,rep_snoc P n] using h

theorem boundary (v : V) (L R : List Bool) :
    run0 (table v) 7 (A (false::L) ([false,false,false]++R)) = some (E ([true,true,true,true]++L) R) := by rfl

theorem onesSplit (T : List Bool) : ∃ j S, T = rep U j ++ S ∧ S.headD false = false := by
  induction T with
  | nil => exact ⟨0,[],rfl,rfl⟩
  | cons b T ih =>
    cases b with
    | false => exact ⟨0,false::T,rfl,rfl⟩
    | true => obtain ⟨j,S,h,e⟩:=ih; exact ⟨j+1,S,by simp only [rep,List.cons_append,List.nil_append,h],e⟩

theorem e_one (v : V) (L R : List Bool) :
    run0 (table v) 1 (E (true::L) (true::R)) = some (E (true::true::L) R) := by rfl

theorem e_many (v : V) (j : Nat) (L R : List Bool) :
    run0 (table v) j (E (true::L) (rep U j++R)) = some (E (true::(rep U j++L)) R) := by
  simpa only [List.nil_append,Nat.one_mul,List.cons_append] using sweepR (table v) 4 [true] [] U U 1 (e_one v) j L R

theorem e_exit (v : V) (L R : List Bool) (hR : R.headD false=false) :
    run0 (table v) 1 (E (true::L) R) = some (E (false::true::L) R.tail) := by
  cases R with
  | nil => rfl
  | cons b R => have hb : b=false := hR; subst b; rfl

theorem rep_ones_comm (n : Nat) (L : List Bool) :
    true::(rep U n++L) = rep U n++true::L := by
  change U ++ (rep U n++L) = _
  rw [← List.append_assoc,← rep_snoc U n,List.append_assoc]
  rfl

theorem grow (v : V) (n j : Nat) (R : List Bool) :
    ∃ j' R' k, 0<k ∧ run0 (table v) k (fam n j R) = some (fam (n+1) j' R') := by
  have h0 : run0 (table v) 2 (fam n j R) = some (F (rep U (j+3)++rep P n) (false::true::R)) := by
    exact first v (rep U (j+3)++rep P n) R
  have h1 := f_many v (j+3) (rep P n) (false::true::R)
  have heq : rep Z (j+3) ++ false::true::R = rep Z (j+4)++true::R := by
    change rep Z (j+3) ++ (Z++true::R) = _
    rw [← List.append_assoc,rep_snoc Z (j+3)]
    rfl
  rw [heq] at h1
  have h2 := f_pairs v n (rep Z (j+4)++true::R)
  have h3 := turn v (rep P n++(rep Z (j+4)++true::R))
  have h4 := a_cross v n (rep Z (j+3)++true::R)
  have h5 := boundary v (rep P (n+1)) (rep Z j++true::R)
  have h01 := join0 h0 h1
  have h23 := join0 h2 h3
  have h0123 := join0 h01 h23
  have h01234 := join0 h0123 h4
  have h012345 := join0 h01234 h5
  obtain ⟨j',S,hS,hzero⟩ := onesSplit (rep Z j++true::R)
  rw [hS] at h012345
  have h6 := e_many v j' (true::true::true::rep P (n+1)) S
  have h7 := e_exit v (rep U j'++true::true::true::rep P (n+1)) S hzero
  have h := join0 (join0 h012345 h6) h7
  refine ⟨j',S.tail,((2+(j+3))+(2*n+1))+(2+2*n)+7+j'+1,by omega,?_⟩
  simpa only [fam,rep,List.cons_append,List.nil_append,rep_ones_comm] using h

theorem entry (v : V) : run0 (table v) 8 ⟨0,[],[]⟩ = some (fam 0 0 []) := by cases v <;> rfl
#print axioms grow
#print axioms entry
end BB6.Agent11Raw121BinarySweep
