import Raw121BinarySweep
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw121TripleSweep
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent11Raw121BinarySweep (onesSplit rep_ones_comm)
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none
abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev E (L R : List Bool) : Z0 := ⟨4,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
abbrev U : List Bool := [true]
abbrev Z : List Bool := [false]
abbrev P : List Bool := [false,true,true]
abbrev Q : List Bool := [true,false,true]
abbrev W : List Bool := [false,false,true]
abbrev X : List Bool := [false,true,false]
abbrev tail : List Bool := [false,true]
def fam (n j : Nat) (R : List Bool) := E (false::(rep U (j+4)++(rep P n++tail))) R

theorem first (L R : List Bool) :
    run0 table 2 (E (false::true::L) R) = some (F L (false::true::R)) := by rfl

theorem f_one (L R : List Bool) :
    run0 table 1 (F (true::L) R) = some (F L (false::R)) := by rfl

theorem f_many (j : Nat) (L R : List Bool) :
    run0 table j (F (rep U j++L) R) = some (F L (rep Z j++R)) := by
  simpa only [List.nil_append,Nat.one_mul] using sweepL table 5 [] [] U Z 1 f_one j L R

theorem turn (L R : List Bool) :
    run0 table 2 (F (false::true::L) R) = some (E (false::true::L) R) := by rfl

theorem e_triple (L R : List Bool) :
    run0 table 5 (E (tail++Q++L) R) = some (E (tail++L) (W++R)) := by rfl

theorem left_shift (n : Nat) : rep P n++tail = tail++rep Q n := by
  induction n with
  | zero => rfl
  | succ n ih => change (P ++ rep P n) ++ tail = tail ++ (Q ++ rep Q n); rw [List.append_assoc,ih]; rfl

theorem left_cross (n : Nat) (R : List Bool) :
    run0 table (5*n) (E (rep P n++tail) R) = some (E tail (rep W n++R)) := by
  rw [left_shift]
  simpa only [List.append_nil,List.nil_append] using sweepL table 4 tail [] Q W 5 e_triple n [] R

theorem a_entry (R : List Bool) :
    run0 table 6 (E tail R) = some (A [false,false,true] ([false,true]++R)) := by rfl

theorem right_shift (n : Nat) (R : List Bool) :
    [false,true]++(rep W n++false::R) = rep X (n+1)++R := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,List.cons_append,List.nil_append] at *; rw [← ih]

theorem a_triple (L R : List Bool) :
    run0 table 3 (A (false::L) (X++R)) = some (A (false::(P++L)) R) := by rfl

theorem a_many (n : Nat) (L R : List Bool) :
    run0 table (3*n) (A (false::L) (rep X n++R)) = some (A (false::(rep P n++L)) R) := by
  simpa only [List.nil_append,List.cons_append] using sweepR table 0 [false] [] X P 3 a_triple n L R

theorem boundary (L R : List Bool) :
    run0 table 7 (A (false::L) ([false,false,false]++R)) = some (E ([true,true,true,true]++L) R) := by rfl

theorem e_one (L R : List Bool) :
    run0 table 1 (E (true::L) (true::R)) = some (E (true::true::L) R) := by rfl

theorem e_many (j : Nat) (L R : List Bool) :
    run0 table j (E (true::L) (rep U j++R)) = some (E (true::(rep U j++L)) R) := by
  simpa only [List.nil_append,Nat.one_mul,List.cons_append] using sweepR table 4 [true] [] U U 1 e_one j L R

theorem e_exit (L R : List Bool) (hR : R.headD false=false) :
    run0 table 1 (E (true::L) R) = some (E (false::true::L) R.tail) := by
  cases R with
  | nil => rfl
  | cons b R => have hb : b=false := hR; subst b; rfl

theorem grow (n j : Nat) (R : List Bool) :
    ∃ j' R' k, 0<k ∧ run0 table k (fam n j R) = some (fam (n+1) j' R') := by
  have h0 : run0 table 2 (fam n j R) = some (F (rep U (j+3)++(rep P n++tail)) (false::true::R)) := by
    exact first (rep U (j+3)++(rep P n++tail)) R
  have h1 := f_many (j+3) (rep P n++tail) (false::true::R)
  have heq : rep Z (j+3) ++ false::true::R = rep Z (j+4)++true::R := by
    change rep Z (j+3) ++ (Z++true::R) = _
    rw [← List.append_assoc,rep_snoc Z (j+3)]
    rfl
  rw [heq] at h1
  have h2 : run0 table 2 (F (rep P n++tail) (rep Z (j+4)++true::R)) = some (E (rep P n++tail) (rep Z (j+4)++true::R)) := by
    rw [left_shift]; exact turn (rep Q n) _
  have h3 := left_cross n (rep Z (j+4)++true::R)
  have h4 := a_entry (rep W n++(rep Z (j+4)++true::R))
  have h4' : run0 table 6 (E tail (rep W n++(rep Z (j+4)++true::R))) = some (A [false,false,true] (rep X (n+1)++(rep Z (j+3)++true::R))) := by
    rw [← right_shift]; exact h4
  have h5 := a_many (n+1) tail (rep Z (j+3)++true::R)
  have h6 := boundary (rep P (n+1)++tail) (rep Z j++true::R)
  have h := join0 (join0 (join0 (join0 (join0 (join0 h0 h1) h2) h3) h4') h5) h6
  obtain ⟨j',S,hS,hzero⟩ := onesSplit (rep Z j++true::R)
  rw [hS] at h
  have h7 := e_many j' (true::true::true::(rep P (n+1)++tail)) S
  have h8 := e_exit (rep U j'++true::true::true::(rep P (n+1)++tail)) S hzero
  have h' := join0 (join0 h h7) h8
  refine ⟨j',S.tail,2+(j+3)+2+5*n+6+3*(n+1)+7+j'+1,by omega,?_⟩
  simpa only [fam,rep,List.cons_append,List.nil_append,rep_ones_comm,List.append_assoc] using h'

theorem entry : run0 table 25 ⟨0,[],[]⟩ = some (fam 0 0 [true]) := by rfl
#print axioms grow
#print axioms entry
end BB6.Agent11Raw121TripleSweep
