import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.RF149
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | _,_ => none

def p (a c : Nat) : List Bool := List.replicate a false ++ List.replicate c true
def b (a : Nat) : List Bool := p 1 a
def P := p 3 2
def Q := b 4
def r := p 2 2
def s := p 1 1
def e := p 0 2
def E (L R : List Bool) : Z0 := ⟨4,L,R⟩
def S (k : Nat) (V : List Bool) : Z0 := E [] (p 11 2 ++ rep P k ++ V)

theorem enter (R : List Bool) : run0 table 29 (E [] (p 11 2 ++ R)) =
    some (E (b 1 ++ b 8) (r ++ R)) := by rfl
theorem carry (L R : List Bool) : run0 table 5 (E (b 1 ++ L) (r ++ P ++ R)) =
    some (E (b 1 ++ Q ++ L) (r ++ R)) := by rfl
theorem carry2 (L R : List Bool) : run0 table 7 (E (b 2 ++ L) (s ++ P ++ R)) =
    some (E (b 2 ++ Q ++ L) (s ++ R)) := by rfl
theorem drain4 (L R : List Bool) : run0 table 13 (E (Q ++ L) (p 7 2 ++ R)) =
    some (E L (p 7 2 ++ P ++ R)) := by rfl
theorem drain8 (R : List Bool) : run0 table 17 (E (b 8) (p 7 2 ++ R)) =
    some (E [] (p 11 2 ++ P ++ R)) := by rfl
theorem prep9 (L R : List Bool) : run0 table 28 (E (b 1 ++ L) (r ++ p 9 2 ++ R)) =
    some (E L (p 7 2 ++ e ++ p 4 2 ++ R)) := by rfl
theorem prep12 (L R : List Bool) : run0 table 28 (E (b 1 ++ L) (r ++ p 12 2 ++ R)) =
    some (E L (p 7 2 ++ e ++ p 7 2 ++ R)) := by rfl
theorem inner7 (L R : List Bool) : run0 table 28 (E (b 1 ++ L) (r ++ p 3 4 ++ p 7 2 ++ R)) =
    some (E (b 1 ++ b 10 ++ Q ++ L) (r ++ R)) := by rfl
theorem inner4 (L R : List Bool) : run0 table 38 (E (b 1 ++ L) (r ++ p 3 4 ++ p 4 2 ++ P ++ R)) =
    some (E (b 2 ++ b 13 ++ Q ++ L) (s ++ R)) := by rfl
theorem finish10 (L R : List Bool) : run0 table 19 (E (b 10 ++ L) (p 7 2 ++ R)) =
    some (E L (p 13 2 ++ P ++ R)) := by rfl
theorem finish13 (L R : List Bool) : run0 table 22 (E (b 13 ++ L) (p 7 2 ++ R)) =
    some (E L (p 16 2 ++ P ++ R)) := by rfl
theorem outer9 (L R : List Bool) : run0 table 13 (E (Q ++ L) (p 13 2 ++ R)) =
    some (E L (p 7 2 ++ p 9 2 ++ R)) := by rfl
theorem outer12 (L R : List Bool) : run0 table 13 (E (Q ++ L) (p 16 2 ++ R)) =
    some (E L (p 7 2 ++ p 12 2 ++ R)) := by rfl

theorem suffix0 (L : List Bool) : run0 table 28 (E (b 1 ++ L) (r ++ p 6 8)) =
    some (E L (p 7 2 ++ e ++ p 1 8)) := by rfl
theorem suffix2 (L : List Bool) : run0 table 28 (E (b 1 ++ L) (r ++ p 17 4)) =
    some (E L (p 7 2 ++ e ++ p 12 4)) := by rfl
theorem suffix4 (L : List Bool) : run0 table 28 (E (b 1 ++ L) (r ++ p 10 4)) =
    some (E L (p 7 2 ++ e ++ p 5 4)) := by rfl
theorem suffix1 (L : List Bool) : run0 table 97 (E (b 2 ++ L) (s ++ p 3 4 ++ p 1 8)) =
    some (E L (p 7 2 ++ p 17 4)) := by rfl
theorem suffix3 (L : List Bool) : run0 table 26 (E (b 2 ++ L) (s ++ p 3 4 ++ p 12 4)) =
    some (E (Q ++ L) (p 7 2 ++ p 10 4)) := by rfl
theorem suffix5 (L : List Bool) : run0 table 26 (E (b 2 ++ L) (s ++ p 3 4 ++ p 5 4)) =
    some (E (Q ++ L) (p 7 2 ++ p 3 4)) := by rfl
theorem suffix6 (L : List Bool) : run0 table 70 (E (b 1 ++ L) (r ++ p 3 4)) =
    some (E L (p 7 2 ++ p 9 4)) := by rfl
theorem suffix7 (L : List Bool) : run0 table 54 (E (b 2 ++ Q ++ L) (s ++ p 9 4)) =
    some (E L (p 7 2 ++ p 6 8)) := by rfl

theorem scan (k : Nat) (V : List Bool) :
    run0 table (29+5*k) (S k V) = some (E (b 1 ++ rep Q k ++ b 8) (r ++ V)) := by
  have a := enter (rep P k ++ V)
  have c := sweepR table 4 (b 1) r P Q 5 carry k (b 8) V
  simp only [E,List.append_assoc,List.nil_append] at a c
  simpa only [S,E,List.append_assoc] using join0 a c

theorem drain (k : Nat) (V : List Bool) :
    run0 table (13*k+17) (E (rep Q k ++ b 8) (p 7 2 ++ V)) = some (S (k+1) V) := by
  have a := sweepL table 4 [] (p 7 2) Q P 13 (by
    intro X Y; simpa only [E,List.nil_append] using drain4 X Y) k (b 8) V
  have c := drain8 (rep P k ++ V)
  simp only [E,List.append_assoc,List.nil_append] at a c
  simpa only [S,E,rep,List.append_assoc] using join0 a c

theorem rep_succ_right (W : List Bool) (k : Nat) : rep W (k+1) = rep W k ++ W :=
  (rep_snoc W k).symm

theorem merge_extra (k : Nat) (V : List Bool) :
    S (k+1) (e ++ V) = S k (p 3 4 ++ V) := by
  unfold S
  rw [rep_succ_right]
  simp only [List.append_assoc]
  rfl

theorem prepS9 (k : Nat) (V : List Bool) :
    run0 table (29+5*k+28+(13*k+17)) (S k (p 9 2 ++ V)) =
      some (S k (p 3 4 ++ p 4 2 ++ V)) := by
  have a := scan k (p 9 2 ++ V)
  have c := prep9 (rep Q k ++ b 8) V
  have d := drain k (e ++ (p 4 2 ++ V))
  simp only [E,List.append_assoc] at a c d
  have h := join0 (join0 a c) d
  rw [merge_extra] at h
  simpa only [List.append_assoc] using h

theorem prepS12 (k : Nat) (V : List Bool) :
    run0 table (29+5*k+28+(13*k+17)) (S k (p 12 2 ++ V)) =
      some (S k (p 3 4 ++ p 7 2 ++ V)) := by
  have a := scan k (p 12 2 ++ V)
  have c := prep12 (rep Q k ++ b 8) V
  have d := drain k (e ++ (p 7 2 ++ V))
  simp only [E,List.append_assoc] at a c d
  have h := join0 (join0 a c) d
  rw [merge_extra] at h
  simpa only [List.append_assoc] using h

def T (k : Nat) : List Bool := Q ++ rep Q k ++ b 8

theorem scan7 (k j : Nat) (V : List Bool) :
    run0 table (29+5*k+28+5*j) (S k (p 3 4 ++ p 7 2 ++ rep P j ++ V)) =
      some (E (b 1 ++ rep Q j ++ b 10 ++ T k) (r ++ V)) := by
  have a := scan k (p 3 4 ++ p 7 2 ++ rep P j ++ V)
  have c := inner7 (rep Q k ++ b 8) (rep P j ++ V)
  have d := sweepR table 4 (b 1) r P Q 5 carry j (b 10 ++ T k) V
  simp only [E,T,List.append_assoc] at a c d
  simpa only [E,T,List.append_assoc] using join0 (join0 a c) d

theorem scan4 (k j : Nat) (V : List Bool) :
    run0 table (29+5*k+38+7*j) (S k (p 3 4 ++ p 4 2 ++ rep P (j+1) ++ V)) =
      some (E (b 2 ++ rep Q j ++ b 13 ++ T k) (s ++ V)) := by
  have a := scan k (p 3 4 ++ p 4 2 ++ rep P (j+1) ++ V)
  have c := inner4 (rep Q k ++ b 8) (rep P j ++ V)
  have d := sweepR table 4 (b 2) s P Q 7 carry2 j (b 13 ++ T k) V
  simp only [E,T,rep,List.append_assoc] at a c d
  simpa only [E,T,rep,List.append_assoc] using join0 (join0 a c) d

theorem drain10 (j : Nat) (L V : List Bool) :
    run0 table (13*j+19) (E (rep Q j ++ b 10 ++ L) (p 7 2 ++ V)) =
      some (E L (p 13 2 ++ rep P (j+1) ++ V)) := by
  have a := sweepL table 4 [] (p 7 2) Q P 13 (by
    intro X Y; simpa only [E,List.nil_append] using drain4 X Y) j (b 10 ++ L) V
  have c := finish10 L (rep P j ++ V)
  simp only [E,List.append_assoc,List.nil_append] at a c
  simpa only [E,rep,List.append_assoc] using join0 a c

theorem drain13 (j : Nat) (L V : List Bool) :
    run0 table (13*j+22) (E (rep Q j ++ b 13 ++ L) (p 7 2 ++ V)) =
      some (E L (p 16 2 ++ rep P (j+1) ++ V)) := by
  have a := sweepL table 4 [] (p 7 2) Q P 13 (by
    intro X Y; simpa only [E,List.nil_append] using drain4 X Y) j (b 13 ++ L) V
  have c := finish13 L (rep P j ++ V)
  simp only [E,List.append_assoc,List.nil_append] at a c
  simpa only [E,rep,List.append_assoc] using join0 a c

theorem outerS9 (k : Nat) (V : List Bool) :
    run0 table (13+(13*k+17)) (E (T k) (p 13 2 ++ V)) =
      some (S (k+1) (p 9 2 ++ V)) := by
  have a := outer9 (rep Q k ++ b 8) V
  have c := drain k (p 9 2 ++ V)
  simp only [E,List.append_assoc] at a c
  simpa only [E,T,List.append_assoc] using join0 a c

theorem outerS12 (k : Nat) (V : List Bool) :
    run0 table (13+(13*k+17)) (E (T k) (p 16 2 ++ V)) =
      some (S (k+1) (p 12 2 ++ V)) := by
  have a := outer12 (rep Q k ++ b 8) V
  have c := drain k (p 12 2 ++ V)
  simp only [E,List.append_assoc] at a c
  simpa only [E,T,List.append_assoc] using join0 a c

theorem merge_inner (j : Nat) (V : List Bool) :
    rep P (j+1) ++ (e ++ V) = rep P j ++ (p 3 4 ++ V) := by
  rw [rep_succ_right,List.append_assoc]
  rfl

theorem phase0 (k j : Nat) : ∃ t, 0<t ∧
    run0 table t (S k (p 12 2 ++ rep P j ++ p 6 8)) =
      some (S (k+1) (p 9 2 ++ rep P j ++ p 3 4 ++ p 1 8)) := by
  have a := prepS12 k (rep P j ++ p 6 8)
  have c := scan7 k j (p 6 8)
  have d := suffix0 (rep Q j ++ b 10 ++ T k)
  have f := drain10 j (T k) (e ++ p 1 8)
  have g := outerS9 k (rep P (j+1) ++ (e ++ p 1 8))
  simp only [E,List.append_assoc] at a c d f g
  have h := join0 (join0 (join0 (join0 a c) d) f) g
  rw [merge_inner] at h
  simp only [List.append_assoc]
  refine ⟨_,?_,h⟩
  omega

theorem phase2 (k j : Nat) : ∃ t, 0<t ∧
    run0 table t (S k (p 12 2 ++ rep P j ++ p 17 4)) =
      some (S (k+1) (p 9 2 ++ rep P j ++ p 3 4 ++ p 12 4)) := by
  have a := prepS12 k (rep P j ++ p 17 4)
  have c := scan7 k j (p 17 4)
  have d := suffix2 (rep Q j ++ b 10 ++ T k)
  have f := drain10 j (T k) (e ++ p 12 4)
  have g := outerS9 k (rep P (j+1) ++ (e ++ p 12 4))
  simp only [E,List.append_assoc] at a c d f g
  have h := join0 (join0 (join0 (join0 a c) d) f) g
  rw [merge_inner] at h
  simp only [List.append_assoc]
  refine ⟨_,?_,h⟩
  omega

theorem phase4 (k j : Nat) : ∃ t, 0<t ∧
    run0 table t (S k (p 12 2 ++ rep P j ++ p 10 4)) =
      some (S (k+1) (p 9 2 ++ rep P j ++ p 3 4 ++ p 5 4)) := by
  have a := prepS12 k (rep P j ++ p 10 4)
  have c := scan7 k j (p 10 4)
  have d := suffix4 (rep Q j ++ b 10 ++ T k)
  have f := drain10 j (T k) (e ++ p 5 4)
  have g := outerS9 k (rep P (j+1) ++ (e ++ p 5 4))
  simp only [E,List.append_assoc] at a c d f g
  have h := join0 (join0 (join0 (join0 a c) d) f) g
  rw [merge_inner] at h
  simp only [List.append_assoc]
  refine ⟨_,?_,h⟩
  omega

theorem phase1 (k j : Nat) : ∃ t, 0<t ∧
    run0 table t (S k (p 9 2 ++ rep P (j+1) ++ p 3 4 ++ p 1 8)) =
      some (S (k+1) (p 12 2 ++ rep P (j+1) ++ p 17 4)) := by
  have a := prepS9 k (rep P (j+1) ++ p 3 4 ++ p 1 8)
  have c := scan4 k j (p 3 4 ++ p 1 8)
  have d := suffix1 (rep Q j ++ b 13 ++ T k)
  have f := drain13 j (T k) (p 17 4)
  have g := outerS12 k (rep P (j+1) ++ p 17 4)
  simp only [E,List.append_assoc,rep] at a c d f g
  have h := join0 (join0 (join0 (join0 a c) d) f) g
  simp only [List.append_assoc,rep]
  refine ⟨_,?_,h⟩
  omega

theorem phase3 (k j : Nat) : ∃ t, 0<t ∧
    run0 table t (S k (p 9 2 ++ rep P (j+1) ++ p 3 4 ++ p 12 4)) =
      some (S (k+1) (p 12 2 ++ rep P (j+2) ++ p 10 4)) := by
  have a := prepS9 k (rep P (j+1) ++ p 3 4 ++ p 12 4)
  have c := scan4 k j (p 3 4 ++ p 12 4)
  have d := suffix3 (rep Q j ++ b 13 ++ T k)
  have f := drain13 (j+1) (T k) (p 10 4)
  have g := outerS12 k (rep P (j+2) ++ p 10 4)
  simp only [E,List.append_assoc,rep] at a c d f g
  have h := join0 (join0 (join0 (join0 a c) d) f) g
  simp only [List.append_assoc,rep]
  refine ⟨_,?_,h⟩
  omega

theorem phase5 (k j : Nat) : ∃ t, 0<t ∧
    run0 table t (S k (p 9 2 ++ rep P (j+1) ++ p 3 4 ++ p 5 4)) =
      some (S (k+1) (p 12 2 ++ rep P (j+2) ++ p 3 4)) := by
  have a := prepS9 k (rep P (j+1) ++ p 3 4 ++ p 5 4)
  have c := scan4 k j (p 3 4 ++ p 5 4)
  have d := suffix5 (rep Q j ++ b 13 ++ T k)
  have f := drain13 (j+1) (T k) (p 3 4)
  have g := outerS12 k (rep P (j+2) ++ p 3 4)
  simp only [E,List.append_assoc,rep] at a c d f g
  have h := join0 (join0 (join0 (join0 a c) d) f) g
  simp only [List.append_assoc,rep]
  refine ⟨_,?_,h⟩
  omega

theorem phase6 (k j : Nat) : ∃ t, 0<t ∧
    run0 table t (S k (p 12 2 ++ rep P j ++ p 3 4)) =
      some (S (k+1) (p 9 2 ++ rep P (j+1) ++ p 9 4)) := by
  have a := prepS12 k (rep P j ++ p 3 4)
  have c := scan7 k j (p 3 4)
  have d := suffix6 (rep Q j ++ b 10 ++ T k)
  have f := drain10 j (T k) (p 9 4)
  have g := outerS9 k (rep P (j+1) ++ p 9 4)
  simp only [E,List.append_assoc] at a c d f g
  have h := join0 (join0 (join0 (join0 a c) d) f) g
  simp only [List.append_assoc]
  refine ⟨_,?_,h⟩
  omega

theorem phase7 (k j : Nat) : ∃ t, 0<t ∧
    run0 table t (S k (p 9 2 ++ rep P (j+2) ++ p 9 4)) =
      some (S (k+1) (p 12 2 ++ rep P (j+1) ++ p 6 8)) := by
  have a := prepS9 k (rep P (j+2) ++ p 9 4)
  have c := scan4 k (j+1) (p 9 4)
  have d := suffix7 (rep Q j ++ b 13 ++ T k)
  have f := drain13 j (T k) (p 6 8)
  have g := outerS12 k (rep P (j+1) ++ p 6 8)
  simp only [E,List.append_assoc,rep] at a c d f g
  have h := join0 (join0 (join0 (join0 a c) d) f) g
  simp only [List.append_assoc,rep]
  refine ⟨_,?_,h⟩
  omega

theorem cycle (k j : Nat) : ∃ t, 0<t ∧
    run0 table t (S k (p 12 2 ++ rep P (j+1) ++ p 6 8)) =
      some (S (k+8) (p 12 2 ++ rep P (j+3) ++ p 6 8)) := by
  obtain ⟨t0,h0,a0⟩ := phase0 k (j+1)
  obtain ⟨t1,h1,a1⟩ := phase1 (k+1) j
  obtain ⟨t2,h2,a2⟩ := phase2 (k+2) (j+1)
  obtain ⟨t3,h3,a3⟩ := phase3 (k+3) j
  obtain ⟨t4,h4,a4⟩ := phase4 (k+4) (j+2)
  obtain ⟨t5,h5,a5⟩ := phase5 (k+5) (j+1)
  obtain ⟨t6,h6,a6⟩ := phase6 (k+6) (j+3)
  obtain ⟨t7,h7,a7⟩ := phase7 (k+7) (j+2)
  exact ⟨_,by omega,join0 (join0 (join0 (join0 (join0 (join0 (join0 a0 a1) a2) a3) a4) a5) a6) a7⟩

def family (n : Nat) : Z0 := S (8*n+8) (p 12 2 ++ rep P (2*n+1) ++ p 6 8)

theorem first : run0 table 3186 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem next (n : Nat) : ∃ t, 0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  have h := cycle (8*n+8) (2*n)
  simpa only [family,show 8*(n+1)+8=8*n+8+8 by omega,show 2*(n+1)+1=2*n+3 by omega] using h

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns table family 3186 first next m hm

#print axioms first
#print axioms next
#print axioms never
end BB6.Agent8Raw54.RF149
