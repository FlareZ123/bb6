import SweepPumping
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled6RBSweeps
open BB6Coverage BB6Coverage.Agent31Pump

inductive Variant | rb | rc
  deriving DecidableEq
def p (v : Variant) : PartialMachine := FAR.fromCodes [7,14,11,3,2,19,8,0,21,(if v == .rb then 7 else 11),24,5]
abbrev A (l r : List Bool) : Z0 := ⟨0,l,r⟩
abbrev E (l r : List Bool) : Z0 := ⟨4,l,r⟩
abbrev P : List Bool := [true,false]
abbrev Q : List Bool := [false,true]
abbrev U : List Bool := [true,true]
abbrev X : List Bool := [true,true,false,false]
abbrev M : List Bool := [false,true,false,false]
abbrev T : List Bool := [true,true,true]
abbrev Z : List Bool := [true,true,true,false]
abbrev W : List Bool := [true,true,true,true,true,false,false]
abbrev S : List Bool := [true,false,true,false,true,true]
abbrev C : List Bool := [true,false,true,true]
abbrev B : List Bool := C++C

theorem rep_add (w : List Bool) (m n : Nat) : rep w (m+n) = rep w m ++ rep w n := by
  induction m with
  | zero => simp [rep]
  | succ m ih => rw [Nat.succ_add,rep,ih,rep,List.append_assoc]

theorem rep_double (w : List Bool) (n : Nat) : rep (w++w) n = rep w (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,ih,show 2*(n+1)=2+2*n by omega,rep_add]; simp [rep,List.append_assoc]

theorem enterP (v : Variant) (R : List Bool) : run0 (p v) 2 (A [] (P++R)) = some (A (false::U) R) := by cases v <;> rfl
theorem stepP (v : Variant) (L R : List Bool) : run0 (p v) 2 (A (false::L) (P++R)) = some (A (false::(U++L)) R) := by cases v <;> rfl

theorem scanP (v : Variant) (n : Nat) (R : List Bool) :
    run0 (p v) (2*(n+1)) (A [] (rep P (n+1)++R)) = some (A (false::rep U (n+1)) R) := by
  have h0 := enterP v (rep P n++R)
  have h1 := sweepR (p v) 0 [false] [] P U 2 (by intro L R; exact stepP v L R) n U R
  have h := join0 h0 h1
  simpa only [List.nil_append,rep_snoc,rep,List.append_assoc,List.cons_append,List.singleton_append,show 2+2*n=2*(n+1) by omega] using h

theorem sweepQ (v : Variant) (n : Nat) (L R : List Bool) : run0 (p v) (2*n) (A (rep U n++L) R) = some (A L (rep Q n++R)) := by
  simpa only [List.nil_append] using sweepL (p v) 0 [] [] U Q 2 (by intro L R; cases v <;> rfl) n L R

theorem collapseFrom (v : Variant) (n : Nat) (R : List Bool) :
    run0 (p v) (2+2*(n+1)+3) (A (false::rep U n) (U++R)) = some (A [] (rep P (n+2)++true::R)) := by
  have rotU : true::rep U n = rep U n++[true] := rotate true [true] n
  have h0 : run0 (p v) 2 (A (false::rep U n) (U++R)) = some (A (rep U (n+1)++[true]) R) := by
    rw [rep,List.append_assoc,←rotU]
    cases v <;> rfl
  have h1 := sweepQ v (n+1) [true] R
  have h2 : run0 (p v) 3 (A [true] (rep Q (n+1)++R)) = some (A [] ([true,false,true]++rep Q (n+1)++R)) := by cases v <;> rfl
  have h := join0 (join0 h0 h1) h2
  have rot : [true]++rep Q (n+1) = rep P (n+1)++[true] := rotate true [false] (n+1)
  have he : [true,false,true]++rep Q (n+1)++R = rep P (n+2)++true::R := by
    change P++([true]++rep Q (n+1))++R = _
    rw [rot]
    simp only [rep,List.append_assoc,List.singleton_append]
  rw [he] at h
  exact h

theorem collapse (v : Variant) (n : Nat) (R : List Bool) : ∃ t, 0<t ∧ run0 (p v) t (A [] (rep P n++U++R)) = some (A [] (rep P (n+2)++true::R)) := by
  cases n with
  | zero => exact ⟨7,by decide,by cases v <;> rfl⟩
  | succ n =>
    have h := join0 (scanP v n (U++R)) (collapseFrom v (n+1) R)
    exact ⟨2*(n+1)+(2+2*(n+1+1)+3),by omega,by simpa only [List.append_assoc] using h⟩

theorem finalOneFrom (v : Variant) (n : Nat) : run0 (p v) (2+3+2*(n+2)) (A (false::rep U n) [true]) = some (A [] (rep Q (n+2)++[true])) := by
  have h0 : run0 (p v) 2 (A (false::rep U n) [true]) = some (A (false::rep U (n+1)) []) := by cases v <;> rfl
  have h1 : run0 (p v) 3 (A (false::rep U (n+1)) []) = some (A (rep U (n+2)) [true]) := by cases v <;> rfl
  have h2 := sweepQ v (n+2) [] [true]
  simp only [List.append_nil] at h2
  exact join0 (join0 h0 h1) h2

theorem finalOne (v : Variant) (n : Nat) : ∃ t, 0<t ∧ run0 (p v) t (A [] (rep P n++[true])) = some (A [] (rep Q (n+2)++[true])) := by
  cases n with
  | zero => exact ⟨9,by decide,by cases v <;> rfl⟩
  | succ n => exact ⟨2*(n+1)+(2+3+2*(n+1+2)),by omega,join0 (scanP v n [true]) (finalOneFrom v (n+1))⟩

theorem finish (v : Variant) (n : Nat) : ∃ t, 0<t ∧ run0 (p v) t (A [] (rep P n++U)) = some (A [] (rep Q (n+4)++[true])) := by
  obtain ⟨t,ht,h⟩ := collapse v n []
  obtain ⟨u,hu,g⟩ := finalOne v (n+2)
  simp only [List.append_nil] at h
  exact ⟨t+u,by omega,join0 h g⟩

theorem collapseC (v : Variant) (n : Nat) (R : List Bool) : ∃ t, 0<t ∧ run0 (p v) t (A [] (rep P n++U++C++R)) = some (A [] (rep P (n+5)++U++R)) := by
  obtain ⟨t,ht,h⟩ := collapse v n (C++R)
  obtain ⟨u,hu,g⟩ := collapse v (n+2) ([false,true,true]++R)
  have h' : run0 (p v) t (A [] (rep P n++U++C++R)) = some (A [] (rep P (n+2)++U++[false,true,true]++R)) := by
    rw [show true::(C++R)=U++[false,true,true]++R by rfl] at h
    simpa only [List.append_assoc] using h
  have g' : run0 (p v) u (A [] (rep P (n+2)++U++[false,true,true]++R)) = some (A [] (rep P (n+5)++U++R)) := by
    have he : rep P (n+2+2)++true::([false,true,true]++R) = rep P (n+5)++U++R := by
      rw [show n+5=(n+2+2)+1 by omega,rep_add P (n+2+2) 1]
      simp only [List.append_assoc]
      rfl
    rw [he] at g
    simpa only [List.append_assoc] using g
  exact ⟨t+u,by omega,join0 h' g'⟩

theorem drainC (v : Variant) (n k : Nat) : ∃ t, run0 (p v) t (A [] (rep P n++U++rep C k)) = some (A [] (rep P (n+5*k)++U)) := by
  induction k generalizing n with
  | zero => exact ⟨0,by simp [rep,run0]⟩
  | succ k ih =>
    obtain ⟨t,_,h⟩ := collapseC v n (rep C k)
    obtain ⟨u,g⟩ := ih (n+5)
    refine ⟨t+u,?_⟩
    simpa only [rep,List.append_assoc,show n+5+5*k=n+5*(k+1) by omega] using join0 h g

def root8 (k : Nat) : Z0 := A [] (rep Q (2*k+2)++[true])

theorem enterEven (v : Variant) (k : Nat) : run0 (p v) (3+4*k+3) (A [] (rep Q (2*k+2)++[true])) = some (A (M++rep X k++T) []) := by
  have h0 : run0 (p v) 3 (A [] ([false,true,false]++(rep (P++P) k++U))) = some (E (false::T) (rep (P++P) k++U)) := by cases v <;> rfl
  have h1 := sweepR (p v) 4 [false] [] (P++P) X 4 (by intro L R; cases v <;> rfl) k T U
  have h2 : run0 (p v) 3 (E (false::(rep X k++T)) U) = some (A (M++rep X k++T) []) := by cases v <;> rfl
  have h1' : run0 (p v) (4*k) (E (false::T) (rep (P++P) k++U)) = some (E (false::(rep X k++T)) U)  := by simpa only [List.nil_append,List.append_assoc,List.cons_append,List.singleton_append] using h1
  have h := join0 (join0 h0 h1') h2
  have he : [false,true,false]++(rep (P++P) k++U) = rep Q (2*k+2)++[true] := by
    rw [rep_double,show 2*k+2=2+2*k by omega,rep_add]
    have hrot : [true]++rep Q (2*k) = rep P (2*k)++[true] := rotate true [false] (2*k)
    change [false,true,false]++(rep P (2*k)++[true,true]) = [false,true,false]++(([true]++rep Q (2*k))++[true])
    rw [hrot,List.append_assoc (rep P (2*k))]
    rfl
  rw [he] at h
  exact h

-- E1=1RC: two remaining 1100 blocks are consumed per left transfer.
theorem leftPump8 (L R : List Bool) : run0 (p .rc) 56 (A (Z++W++(X++X)++L) (S++R)) = some (A (Z++W++L) (S++B++R)) := rfl

theorem leftPumpAll8 (n : Nat) (L R : List Bool) : run0 (p .rc) (56*n) (A (Z++W++rep X (2*n)++L) (S++R)) = some (A (Z++W++L) (S++rep C (2*n)++R)) := by
  rw [←rep_double X,←rep_double C]
  simpa only [List.append_assoc] using sweepL (p .rc) 0 (Z++W) S (X++X) B 56 leftPump8 n L R

theorem leftPrep8 (L : List Bool) : run0 (p .rc) 41 (A (M++X++X++L) []) = some (A (Z++W++L) S) := rfl

theorem exitEven8 (R : List Bool) : run0 (p .rc) (28+160) (A (Z++W++T) (S++R)) = some (A [] (rep P 16++U++R)) := rfl

theorem exitOdd8 (R : List Bool) : run0 (p .rc) (78+554) (A (Z++W++X++T) (S++R)) = some (A [] (rep P 26++U++R)) := rfl

theorem growthEven8 (n : Nat) : ∃ t, 0<t ∧ run0 (p .rc) t (root8 (2*n+2)) = some (root8 (5*n+9)) := by
  have h0 := enterEven .rc (2*n+2)
  have h1 := leftPrep8 (rep X (2*n)++T)
  have h2 := leftPumpAll8 n T []
  have h3 := exitEven8 (rep C (2*n))
  have h0' : run0 (p .rc) (3+4*(2*n+2)+3) (root8 (2*n+2)) = some (A (M++X++X++(rep X (2*n)++T)) []) := by simpa only [root8,show 2*n+2=2+(2*n) by omega,rep_add,rep,List.append_nil,List.append_assoc] using h0
  simp only [List.append_nil,List.append_assoc] at h2 h3 h1
  obtain ⟨t,ht⟩ := drainC .rc 16 (2*n)
  obtain ⟨u,hu,hr⟩ := finish .rc (16+5*(2*n))
  refine ⟨(3+4*(2*n+2)+3)+41+56*n+(28+160)+t+u,by omega,?_⟩
  have h := join0 (join0 (join0 (join0 (join0 (by simpa only [List.append_assoc] using h0') h1) h2) h3) (by simpa only [List.append_assoc] using ht)) hr
  simpa only [root8,show 16+5*(2*n)+4=2*(5*n+9)+2 by omega,List.append_assoc] using h

theorem growthOdd8 (n : Nat) : ∃ t, 0<t ∧ run0 (p .rc) t (root8 (2*n+3)) = some (root8 (5*n+14)) := by
  have h0 := enterEven .rc (2*n+3)
  have h1 := leftPrep8 (rep X (2*n)++X++T)
  have h2 := leftPumpAll8 n (X++T) []
  have h3 := exitOdd8 (rep C (2*n))
  have h0' : run0 (p .rc) (3+4*(2*n+3)+3) (root8 (2*n+3)) = some (A (M++X++X++(rep X (2*n)++X++T)) []) := by
    simpa only [root8,show 2*n+3=2+(2*n+1) by omega,rep_add,rep,List.append_nil,List.append_assoc,rep_snoc] using h0
  simp only [List.append_nil,List.append_assoc] at h2 h3 h1
  obtain ⟨t,ht⟩ := drainC .rc 26 (2*n)
  obtain ⟨u,hu,hr⟩ := finish .rc (26+5*(2*n))
  refine ⟨(3+4*(2*n+3)+3)+41+56*n+(78+554)+t+u,by omega,?_⟩
  have h := join0 (join0 (join0 (join0 (join0 (by simpa only [List.append_assoc] using h0') h1) h2) h3) (by simpa only [List.append_assoc] using ht)) hr
  simpa only [root8,show 26+5*(2*n)+4=2*(5*n+14)+2 by omega,List.append_assoc] using h

theorem growth8 (k : Nat) : ∃ j t, 0<t ∧ run0 (p .rc) t (root8 k) = some (root8 j) := by
  cases k with
  | zero => exact ⟨4,106,by decide,rfl⟩
  | succ k =>
    cases k with
    | zero => exact ⟨9,439,by decide,rfl⟩
    | succ k =>
      have hk : k=2*(k/2) ∨ k=2*(k/2)+1 := by omega
      rcases hk with hk|hk
      · obtain ⟨t,ht,h⟩ := growthEven8 (k/2)
        exact ⟨5*(k/2)+9,t,ht,by rw [←hk] at h; exact h⟩
      · obtain ⟨t,ht,h⟩ := growthOdd8 (k/2)
        exact ⟨5*(k/2)+14,t,ht,by rw [←show 2*(k/2)+3=k+2 by omega] ; exact h⟩

noncomputable def next8 (k : Nat) := Classical.choose (growth8 k)
noncomputable def trajectory8 : Nat → Nat
  | 0 => 4
  | n+1 => next8 (trajectory8 n)
noncomputable def family8 (n : Nat) := root8 (trajectory8 n)
theorem init8 : run0 (p .rc) 120 (A [] []) = some (root8 4) := rfl

theorem never8 (m : Machine) (hm : compatible (p .rc) m) : NeverHalts m := by
  let cost := fun n => Classical.choose (Classical.choose_spec (growth8 (trajectory8 n)))
  exact never_of_growth (p .rc) family8 120 cost init8
    (fun n => (Classical.choose_spec (Classical.choose_spec (growth8 (trajectory8 n)))).1)
    (fun n => (Classical.choose_spec (Classical.choose_spec (growth8 (trajectory8 n)))).2) m hm

#print axioms never8

-- E1=1RB: a two-pass fill converts every pair of 1100 blocks to 1111100.
abbrev Y : List Bool := [true,false,true,false,true,false,true]
abbrev H : List Bool := [true,false,true]
abbrev V : List Bool := [true,true,true,true,true,true,false]

def root4 (k : Nat) : Z0 := A [] (rep Q (2*k+3)++[true])

theorem enterOdd4 (k : Nat) : run0 (p .rb) (3+4*k+17) (root4 k) = some (A (M++Z++rep X k++T) []) := by
  have h0 : run0 (p .rb) 3 (A [] ([false,true,false]++(rep (P++P) k++P++U))) = some (E (false::T) (rep (P++P) k++P++U)) := rfl
  have h1 := sweepR (p .rb) 4 [false] [] (P++P) X 4 (by intro L R; rfl) k T (P++U)
  have h2 : run0 (p .rb) 17 (E (false::(rep X k++T)) (P++U)) = some (A (M++Z++rep X k++T) []) := rfl
  have h1' : run0 (p .rb) (4*k) (E (false::T) (rep (P++P) k++P++U)) = some (E (false::(rep X k++T)) (P++U)) := by
    simpa only [List.nil_append,List.append_assoc,List.cons_append,List.singleton_append] using h1
  have h := join0 (join0 h0 h1') h2
  have he : [false,true,false]++(rep (P++P) k++P++U) = rep Q (2*k+3)++[true] := by
    rw [rep_double,show 2*k+3=2+(2*k+1) by omega,rep_add Q 2 (2*k+1)]
    have hrot : [true]++rep Q (2*k+1) = rep P (2*k+1)++[true] := rotate true [false] (2*k+1)
    change [false,true,false]++(rep P (2*k)++P++U) = [false,true,false]++(([true]++rep Q (2*k+1))++[true])
    rw [hrot,rep_add P (2*k) 1]
    simp only [List.append_assoc]
    rfl
  rw [he] at h
  exact h

theorem fillZ4 (k : Nat) : run0 (p .rb) 23 (A (M++Z++rep X k++T) []) = some (A (M++W++rep X k++T) []) := by cases k <;> rfl

theorem transferW (i : Nat) (L : List Bool) : run0 (p .rb) (8+7*i) (A (M++rep W i++L) []) = some (A L (rep Y i++S)) := by
  have h0 : run0 (p .rb) 8 (A (M++(rep W i++L)) []) = some (A (rep W i++L) S) := rfl
  have h1 := sweepL (p .rb) 0 [] [] W Y 7 (by intro L R; rfl) i L S
  simpa only [List.nil_append,List.append_assoc] using join0 h0 h1

theorem backW (i : Nat) (L : List Bool) : run0 (p .rb) (7*i+10) (E (false::L) (H++rep Y i++S)) = some (A (M++rep W (i+1)++L) []) := by
  have h0 := sweepR (p .rb) 4 [false] H Y W 7 (by intro L R; rfl) i L S
  have h1 : run0 (p .rb) 10 (E (false::(rep W i++L)) (H++S)) = some (A (M++W++rep W i++L) []) := rfl
  have h0' : run0 (p .rb) (7*i) (E (false::L) (H++rep Y i++S)) = some (E (false::(rep W i++L)) (H++S)) := by
    simpa only [List.nil_append,List.append_assoc,List.cons_append,List.singleton_append] using h0
  simpa only [rep,List.append_assoc] using join0 h0' h1

theorem fill1 (i : Nat) (L : List Bool) : ∃ t, 0<t ∧ run0 (p .rb) t (A (M++rep W (i+1)++X++L) []) = some (A (M++rep W (i+1)++V++L) []) := by
  have h0 := transferW (i+1) (X++L)
  have h1 : run0 (p .rb) 8 (A (X++L) (Y++(rep Y i++S))) = some (E (false::(V++L)) (H++(rep Y i++S))) := rfl
  have h2 := backW i (V++L)
  refine ⟨8+7*(i+1)+8+(7*i+10),by omega,?_⟩
  simpa only [List.append_assoc,rep] using join0 (join0 (by simpa only [rep,List.append_assoc] using h0) h1) (by simpa only [rep,List.append_assoc] using h2)

theorem fill2 (i : Nat) (L : List Bool) : ∃ t, 0<t ∧ run0 (p .rb) t (A (M++rep W (i+1)++V++L) []) = some (A (M++rep W (i+2)++T++L) []) := by
  have h0 := transferW (i+1) (V++L)
  have h1 : run0 (p .rb) 9 (A (V++L) (rep Y (i+1)++S)) = some (E (false::(T++L)) (H++(rep Y (i+1)++S))) := rfl
  have h2 := backW (i+1) (T++L)
  refine ⟨8+7*(i+1)+9+(7*(i+1)+10),by omega,?_⟩
  simpa only [List.append_assoc] using join0 (join0 h0 h1) (by simpa only [List.append_assoc] using h2)

theorem fillPair (i : Nat) (L : List Bool) : ∃ t, 0<t ∧ run0 (p .rb) t (A (M++rep W (i+1)++X++X++L) []) = some (A (M++rep W (i+3)++L) []) := by
  obtain ⟨t,ht,h⟩ := fill1 i (X++L)
  obtain ⟨u,hu,g⟩ := fill2 i (X++L)
  have he : M++rep W (i+2)++T++(X++L) = M++rep W (i+3)++L := by
    rw [show i+3=(i+2)+1 by omega,rep_add W (i+2) 1]
    simp only [List.append_assoc]
    rfl
  have g' : run0 (p .rb) u (A (M++rep W (i+1)++V++(X++L)) []) = some (A (M++rep W (i+3)++L) []) := by
    simpa only [←List.append_assoc,he] using g
  exact ⟨t+u,by omega,by simpa only [List.append_assoc] using join0 h g'⟩

theorem fillAll (k i : Nat) (L : List Bool) : ∃ t, run0 (p .rb) t (A (M++rep W (i+1)++rep X (2*k)++L) []) = some (A (M++rep W (i+1+2*k)++L) []) := by
  induction k generalizing i with
  | zero => exact ⟨0,by simp [rep,run0]⟩
  | succ k ih =>
    obtain ⟨t,ht,h⟩ := fillPair i (rep X (2*k)++L)
    obtain ⟨u,g⟩ := ih (i+2)
    refine ⟨t+u,?_⟩
    have g' : run0 (p .rb) u (A (M++rep W (i+3)++(rep X (2*k)++L)) []) = some (A (M++rep W (i+1+2*(k+1))++L) []) := by
      simpa only [show i+2+1=i+3 by omega,show i+2+1+2*k=i+1+2*(k+1) by omega,List.append_assoc] using g
    have hx : rep X (2*(k+1)) = X++X++rep X (2*k) := by
      rw [show 2*(k+1)=2+2*k by omega,rep_add X 2 (2*k)]
      rfl
    rw [hx]
    simpa only [List.append_assoc] using join0 h g' 

theorem collapseY (n : Nat) (R : List Bool) : ∃ t, 0<t ∧ run0 (p .rb) t (A [] (rep P n++[true]++Y++R)) = some (A [] (rep P (n+5)++true::R)) := by
  obtain ⟨t,ht,h⟩ := collapse .rb n ([false,true,false,true,false,true]++R)
  have he : rep P (n+2)++true::([false,true,false,true,false,true]++R) = rep P (n+5)++true::R := by
    rw [show n+5=(n+2)+3 by omega,rep_add P (n+2) 3]
    simp only [List.append_assoc]
    rfl
  rw [he] at h
  exact ⟨t,ht,by simpa only [List.append_assoc,show U++([false,true,false,true,false,true]++R)=[true]++(Y++R) by rfl] using h⟩

theorem drainY (n i : Nat) : ∃ t, run0 (p .rb) t (A [] (rep P n++[true]++rep Y i++S)) = some (A [] (rep P (n+5*i)++[true]++S)) := by
  induction i generalizing n with
  | zero => exact ⟨0,by simp [rep,run0]⟩
  | succ i ih =>
    obtain ⟨t,_,h⟩ := collapseY n (rep Y i++S)
    obtain ⟨u,g⟩ := ih (n+5)
    have g' : run0 (p .rb) u (A [] (rep P (n+5)++true::(rep Y i++S))) = some (A [] (rep P (n+5+5*i)++[true]++S)) := by
      simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using g
    exact ⟨t+u,by simpa only [rep,List.append_assoc,show n+5+5*i=n+5*(i+1) by omega] using join0 h g'⟩

theorem exit4 (i : Nat) : ∃ t, 0<t ∧ run0 (p .rb) t (A (M++rep W i++T) []) = some (A [] (rep Q (5*i+10)++[true])) := by
  have h0 := transferW i T
  have h1 : run0 (p .rb) 5 (A T (rep Y i++S)) = some (A [] (rep P 2++[true]++rep Y i++S)) := rfl
  obtain ⟨t,h2⟩ := drainY 2 i
  obtain ⟨u,hu,h3⟩ := collapse .rb (2+5*i) [false,true,false,true,true]
  have he : rep P (2+5*i+2)++true::[false,true,false,true,true] = rep P (2+5*i+4)++U := by
    rw [show 2+5*i+4=(2+5*i+2)+2 by omega,rep_add P (2+5*i+2) 2]
    simp only [List.append_assoc]
    rfl
  rw [he] at h3
  obtain ⟨v,hv,h4⟩ := finish .rb (2+5*i+4)
  refine ⟨8+7*i+5+t+u+v,by omega,?_⟩
  have h := join0 (join0 (join0 h0 h1) h2) (by simpa only [List.append_assoc,show U++[false,true,false,true,true]=[true]++S by rfl] using h3)
  simpa only [show 2+5*i+4+4=5*i+10 by omega] using join0 h h4

theorem wrap4 (i : Nat) : ∃ t, 0<t ∧ run0 (p .rb) t (A (M++rep W i++T++T) []) = some (A (M++rep W (i+1)++T) []) := by
  have h0 := transferW i (T++T)
  have h1 : run0 (p .rb) 6 (A (T++T) (rep Y i++S)) = some (A [] (rep Q 3++rep Y i++S)) := rfl
  have h2 : run0 (p .rb) 3 (A [] (rep Q 3++rep Y i++S)) = some (E (false::T) (H++rep Y i++S)) := rfl
  have h3 := backW i T
  exact ⟨8+7*i+6+3+(7*i+10),by omega,by simpa only [List.append_assoc] using join0 (join0 (join0 h0 h1) h2) h3⟩

theorem growthEven4 (n : Nat) : ∃ t, 0<t ∧ run0 (p .rb) t (root4 (2*n)) = some (root4 (5*n+6)) := by
  have h0 := enterOdd4 (2*n)
  have h1 := fillZ4 (2*n)
  obtain ⟨t,h2⟩ := fillAll n 0 T
  obtain ⟨u,hu,h3⟩ := exit4 (1+2*n)
  refine ⟨3+4*(2*n)+17+23+t+u,by omega,?_⟩
  have h := join0 (join0 h0 h1) (by simpa only [show rep W 1=W by rfl,List.append_nil,List.append_assoc,Nat.zero_add] using h2)
  simpa only [root4,show 5*(1+2*n)+10=2*(5*n+6)+3 by omega] using join0 h h3

theorem growthOdd4 (n : Nat) : ∃ t, 0<t ∧ run0 (p .rb) t (root4 (2*n+1)) = some (root4 (5*n+11)) := by
  have h0 := enterOdd4 (2*n+1)
  have h1 := fillZ4 (2*n+1)
  obtain ⟨t,h2⟩ := fillAll n 0 (X++T)
  obtain ⟨u,hu,h3⟩ := fill1 (2*n) T
  obtain ⟨v,hv,h4⟩ := fill2 (2*n) T
  obtain ⟨w,hw,h5⟩ := wrap4 (2*n+2)
  obtain ⟨x,hx,h6⟩ := exit4 (2*n+3)
  refine ⟨3+4*(2*n+1)+17+23+t+u+v+w+x,by omega,?_⟩
  have h2' : run0 (p .rb) t (A (M++W++rep X (2*n+1)++T) []) = some (A (M++rep W (2*n+1)++X++T) []) := by
    simpa only [show rep W 1=W by rfl,List.append_nil,List.append_assoc,Nat.zero_add,rep_add X (2*n) 1,show rep X 1=X by rfl,show 1+2*n=2*n+1 by omega] using h2
  have h := join0 (join0 (join0 (join0 (join0 (join0 h0 h1) h2') h3) h4) h5) h6
  simpa only [root4,show 5*(2*n+3)+10=2*(5*n+11)+3 by omega] using h

theorem growth4 (k : Nat) : ∃ j t, 0<t ∧ run0 (p .rb) t (root4 k) = some (root4 j) := by
  have hk : k=2*(k/2) ∨ k=2*(k/2)+1 := by omega
  rcases hk with hk|hk
  · obtain ⟨t,ht,h⟩ := growthEven4 (k/2)
    exact ⟨5*(k/2)+6,t,ht,by rw [←hk] at h; exact h⟩
  · obtain ⟨t,ht,h⟩ := growthOdd4 (k/2)
    exact ⟨5*(k/2)+11,t,ht,by rw [←hk] at h; exact h⟩

noncomputable def next4 (k : Nat) := Classical.choose (growth4 k)
noncomputable def trajectory4 : Nat → Nat
  | 0 => 2
  | n+1 => next4 (trajectory4 n)
noncomputable def family4 (n : Nat) := root4 (trajectory4 n)
theorem init4 : run0 (p .rb) 66 (A [] []) = some (root4 2) := rfl

theorem never4 (m : Machine) (hm : compatible (p .rb) m) : NeverHalts m := by
  let cost := fun n => Classical.choose (Classical.choose_spec (growth4 (trajectory4 n)))
  exact never_of_growth (p .rb) family4 66 cost init4
    (fun n => (Classical.choose_spec (Classical.choose_spec (growth4 (trajectory4 n)))).1)
    (fun n => (Classical.choose_spec (Classical.choose_spec (growth4 (trajectory4 n)))).2) m hm

#print axioms never4
end BB6.Agent46Raw13Coupled6RBSweeps
