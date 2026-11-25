import RecursiveCounterCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent16Raw118Nested.M10
open BB6Coverage Agent31Pump Agent40Recursive Agent40Independent

-- Exact one-hole row 10: 1RB1RA_1RC0RB_0RD---_1LD1RE_0LF0LE_1LA1LF
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def O (n : Nat) : List Bool := List.replicate n true
def Z (n : Nat) : List Bool := List.replicate n false

theorem O_add (a b : Nat) : O (a+b) = O a ++ O b := List.replicate_append_replicate.symm
theorem Z_add (a b : Nat) : Z (a+b) = Z a ++ Z b := List.replicate_append_replicate.symm
theorem O_snoc (n : Nat) (L : List Bool) : O n ++ true::L = O (n+1) ++ L := by
  rw [O_add]; simp [List.append_assoc,O]
theorem Z_snoc (n : Nat) (L : List Bool) : Z n ++ false::L = Z (n+1) ++ L := by
  rw [Z_add]; simp [List.append_assoc,Z]

def P (a b : Nat) (L : List Bool) : Z0 := ⟨0,L,O a ++ [false,false,false] ++ O b ++ [false,true]⟩
def Q (b : Nat) (L : List Bool) : Z0 := ⟨0,false::L,[false,false] ++ O b ++ [false,true]⟩
def Root (m : Nat) : Z0 := P (4*m+1) 0 []

def B (L R : List Bool) : Z0 := ⟨1,R.headD false::L,R.tail⟩
theorem bwalk (k : Nat) (L R : List Bool) :
    run0 table k (B L (O k ++ R)) = some (B (Z k ++ L) R) := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h : run0 table 1 (B L (O (k+1) ++ R)) = some (B (false::L) (O k ++ R)) := by rfl
    have hh := join0 h (ih (false::L))
    rw [Z_snoc] at hh
    simpa only [Nat.add_comm 1 k] using hh

theorem fwalk (k : Nat) (L R : List Bool) :
    run0 table k ⟨5,O k ++ L,R⟩ = some ⟨5,L,O k ++ R⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h : run0 table 1 ⟨5,true::(O k ++ L),R⟩ = some ⟨5,O k ++ L,true::R⟩ := by rfl
    have hh := join0 h (ih (true::R))
    rw [O_snoc] at hh
    simpa only [Nat.add_comm 1 k, O, List.replicate_succ,List.cons_append] using hh

theorem awalk (k : Nat) (L R : List Bool) :
    run0 table (k+1) ⟨0,true::L,O k ++ false::R⟩ = some ⟨0,false::(O (k+1) ++ L),R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h : run0 table 1 ⟨0,true::L,O (k+1) ++ false::R⟩ = some ⟨0,true::true::L,O k ++ false::R⟩ := by rfl
    have hh := join0 h (ih (true::L))
    rw [O_snoc] at hh
    simpa only [Nat.add_comm 1 (k+1)] using hh

theorem pbig_from (a b : Nat) (L : List Bool) (z : Z0)
    (h : run0 table 1 z = some (B (true::L) (O (a+3) ++ [false,false,false] ++ O b ++ [false,true]))) :
    PositiveRun table z (P 1 (b+1) (Z (a+1) ++ true::L)) := by
  have h2 := bwalk (a+3) (true::L) ([false,false,false] ++ O b ++ [false,true])
  rw [List.append_assoc, List.append_assoc] at h
  have h3 : run0 table 9 (B (Z (a+3) ++ true::L) ([false,false,false] ++ O b ++ [false,true])) =
      some (P 1 (b+1) (Z (a+1) ++ true::L)) := by
    simp only [P,O,Z,List.replicate_succ,List.cons_append,List.nil_append,List.append_assoc]
    rfl
  exact ⟨1+(a+3)+9,by omega,join0 (join0 h h2) h3⟩

theorem pbig (a b : Nat) (L : List Bool) :
    PositiveRun table (P (a+3) b (false::L)) (P 1 (b+1) (Z (a+1) ++ true::L)) :=
  pbig_from a b L _ (by rfl)
theorem pbig_empty (a b : Nat) :
    PositiveRun table (P (a+3) b []) (P 1 (b+1) (Z (a+1) ++ [true])) :=
  pbig_from a b [] _ (by rfl)

theorem p1 (k b : Nat) (L : List Bool) :
    PositiveRun table (P 1 b (Z (k+3) ++ L)) (P 2 (b+1) (Z (k+1) ++ L)) := by
  refine ⟨12,by decide,?_⟩
  simp only [P,O,Z,List.replicate_succ,List.cons_append,List.nil_append,List.append_assoc]
  rfl
theorem p2 (b : Nat) (L : List Bool) :
    PositiveRun table (P 2 b (false::L)) (Q (b+1) (true::true::L)) := by
  refine ⟨14,by decide,?_⟩
  simp only [P,Q,O,Z,List.replicate_succ,List.cons_append,List.nil_append,List.append_assoc]
  rfl

theorem qentry (b : Nat) (L : List Bool) :
    run0 table 7 (Q (b+2) L) = some ⟨5,true::true::L,[false,false,false] ++ O b ++ [false,true]⟩ := by
  simp only [Q,O,List.replicate_succ,List.cons_append,List.nil_append,List.append_assoc]
  rfl

theorem qgap (t b k : Nat) (L : List Bool) :
    PositiveRun table (Q (b+2) (O t ++ Z (k+2) ++ L)) (P (t+3) b (Z (k+1) ++ L)) := by
  have h1 := qentry b (O t ++ Z (k+2) ++ L)
  have h2 := fwalk (t+2) (Z (k+2) ++ L) ([false,false,false] ++ O b ++ [false,true])
  have h3 : run0 table 1 ⟨5,Z (k+2) ++ L,O (t+2) ++ ([false,false,false] ++ O b ++ [false,true])⟩ =
      some (P (t+3) b (Z (k+1) ++ L)) := by
    unfold P
    simp only [O,Z,List.replicate_succ,List.cons_append,List.append_assoc]
    rfl
  exact ⟨7+(t+2)+1,by omega,join0 (join0 h1 (by simpa only [O,List.replicate_succ,List.cons_append,List.append_assoc] using h2)) h3⟩

theorem qend (t b : Nat) :
    PositiveRun table (Q (b+2) (O t)) (P (t+3) b []) := by
  have h1 := qentry b (O t)
  have h2 := fwalk (t+2) [] ([false,false,false] ++ O b ++ [false,true])
  simp only [List.append_nil] at h2
  have h3 : run0 table 1 ⟨5,[],O (t+2) ++ ([false,false,false] ++ O b ++ [false,true])⟩ =
      some (P (t+3) b []) := by
    unfold P
    simp only [O,List.replicate_succ,List.cons_append,List.append_assoc]
    rfl
  exact ⟨7+(t+2)+1,by omega,join0 (join0 h1 (by simpa only [O,List.replicate_succ,List.cons_append,List.append_assoc] using h2)) h3⟩

theorem qmerge (t b : Nat) (L : List Bool) :
    PositiveRun table (Q (b+2) (O t ++ false::true::L)) (Q b (O (t+4) ++ L)) := by
  have h1 := qentry b (O t ++ false::true::L)
  have h2 := fwalk (t+2) (false::true::L) ([false,false,false] ++ O b ++ [false,true])
  have h3 : run0 table 1 ⟨5,false::true::L,O (t+2) ++ ([false,false,false] ++ O b ++ [false,true])⟩ =
      some ⟨0,true::L,O (t+3) ++ false::false::false::(O b ++ [false,true])⟩ := by rfl
  have h4 := awalk (t+3) L (false::false::(O b ++ [false,true]))
  exact ⟨7+(t+2)+1+(t+3+1),by omega,join0 (join0 (join0 h1 h2) h3) h4⟩

-- Restore a left zero gap. The two phases correspond to lengths 4m+3 and 4m+4.
def Rest0 (m : Nat) : Prop := ∀ b c S,
    PositiveRun table (P 1 b (Z (4*m+3) ++ O (c+1) ++ S))
      (Q (b+2) (O (4*m+3+c) ++ S))
def Rest1 (m : Nat) : Prop := ∀ b c S,
    PositiveRun table (P 1 b (Z (4*m+4) ++ O (c+1) ++ S))
      (Q b (O (4*m+6+c) ++ S))

theorem start_restore (k b : Nat) (L : List Bool) :
    PositiveRun table (P 1 b (Z (k+3) ++ L)) (Q (b+2) (O 2 ++ Z k ++ L)) := by
  exact (p1 k b L).trans (p2 (b+1) (Z k ++ L))

theorem pair (j k b : Nat) (L : List Bool) (h0 : Rest0 j) (h1 : Rest1 j) :
    PositiveRun table (Q (b+2) (O (4*j+2) ++ Z (k+4) ++ L))
      (Q (b+2) (O (4*(j+1)+2) ++ Z k ++ L)) := by
  have h2 := qgap (4*j+2) b (k+2) L
  have h3 := pbig (4*j+2) b (Z (k+2) ++ L)
  have h4 := h0 (b+1) 0 (Z (k+2) ++ L)
  have h5 := qgap (4*j+3) (b+1) k L
  have h6 := pbig (4*j+3) (b+1) (Z k ++ L)
  have h7 := h1 (b+2) 0 (Z k ++ L)
  have h4' : PositiveRun table (P 1 (b+1) (Z (4*j+3) ++ true::(Z (k+2) ++ L)))
      (Q (b+3) (O (4*j+3) ++ Z (k+2) ++ L)) := by
    simpa only [Nat.add_zero,O,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] using h4
  have h7' : PositiveRun table (P 1 (b+2) (Z (4*j+4) ++ true::(Z k ++ L)))
      (Q (b+2) (O (4*j+6) ++ (Z k ++ L))) := by
    simpa only [Nat.add_zero,O,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] using h7
  rw [show 4*(j+1)+2=4*j+6 by omega]
  simpa only [List.append_assoc] using h2.trans (h3.trans (h4'.trans (h5.trans (h6.trans h7'))))

theorem restoration (m : Nat) : Rest0 m ∧ Rest1 m := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    have walk : ∀ k j, j+k=m → ∀ r b (L : List Bool),
        ∃ t, run0 table t (Q (b+2) (O (4*j+2) ++ Z (4*k+r) ++ L)) =
          some (Q (b+2) (O (4*m+2) ++ Z r ++ L)) := by
      intro k
      induction k with
      | zero =>
        intro j hj r b L
        have eq : j=m := by omega
        subst j
        exact ⟨0,by simp [run0]⟩
      | succ k hk =>
        intro j hj r b L
        obtain ⟨h0,h1⟩ := ih j (by omega)
        obtain ⟨t,ht,hp⟩ := pair j (4*k+r) b L h0 h1
        rw [show 4*k+r+4=4*(k+1)+r by omega] at hp
        obtain ⟨v,hv⟩ := hk (j+1) (by omega) r b L
        exact ⟨t+v,join0 hp hv⟩
    constructor
    · intro b c S
      obtain ⟨t,ht,hp⟩ := start_restore (4*m) b (O (c+1) ++ S)
      obtain ⟨v,hv⟩ := walk m 0 (by omega) 0 b (O (c+1) ++ S)
      simp only [Nat.mul_zero,Nat.zero_add,Nat.add_zero,List.append_assoc] at hp hv
      have H := join0 hp hv
      simp only [Z,List.replicate_zero,List.nil_append] at H
      rw [← List.append_assoc (O (4*m+2)),← O_add,show 4*m+2+(c+1)=4*m+3+c by omega] at H
      exact ⟨t+v,by omega,by simpa only [Z,List.append_assoc] using H⟩
    · intro b c S
      obtain ⟨t,ht,hp⟩ := start_restore (4*m+1) b (O (c+1) ++ S)
      obtain ⟨v,hv⟩ := walk m 0 (by omega) 1 b (O (c+1) ++ S)
      simp only [Nat.mul_zero,Nat.zero_add,Nat.add_zero,List.append_assoc] at hp hv
      have H := join0 hp hv
      have h := qmerge (4*m+2) b (O c ++ S)
      rw [← List.append_assoc (O (4*m+2+4)),← O_add] at h
      have h' : run0 table (t+v) (P 1 b (Z (4*m+4) ++ O (c+1) ++ S)) =
          some (Q (b+2) (O (4*m+2) ++ false::true::(O c ++ S))) := by
        simpa only [Z,O,List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append,List.append_assoc] using H
      obtain ⟨u,hu,hr⟩ := h
      exact ⟨t+v+u,by omega,join0 h' hr⟩

theorem grow (m : Nat) : PositiveRun table (Root m) (Root (m+1)) := by
  cases m with
  | zero => exact ⟨38,by decide,by rfl⟩
  | succ m =>
    obtain ⟨h0,h1⟩ := restoration m
    have h2 := pbig_empty (4*m+2) 0
    have h3 := h0 1 0 []
    simp only [List.append_nil] at h3
    have h4 := qend (4*m+3) 1
    have h5 := pbig_empty (4*m+3) 1
    have h6 := h1 2 0 []
    simp only [List.append_nil] at h6
    have h7 := qend (4*m+6) 0
    have h := h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7))))
    simpa only [Root,show 4*(m+1)+1=4*m+2+3 by omega,show 4*(m+1+1)+1=4*m+6+3 by omega] using h

def Inv (z : Z0) : Prop := ∃ m, z = Root m
theorem entry : ∃ t z, run0 table t ⟨0,[],[]⟩ = some z ∧ Inv z :=
  ⟨11,Root 0,by rfl,⟨0,rfl⟩⟩
theorem closed : ∀ z, Inv z → ∃ k z', 0 < k ∧ run0 table k z = some z' ∧ Inv z' := by
  rintro z ⟨n,rfl⟩
  obtain ⟨k,hk,h⟩ := grow n
  exact ⟨k,Root (n+1),hk,h,⟨n+1,rfl⟩⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_closed table Inv entry closed m hm
#print axioms restoration
#print axioms grow
#print axioms entry
#print axioms closed
#print axioms never
end BB6Coverage.Agent16Raw118Nested.M10
