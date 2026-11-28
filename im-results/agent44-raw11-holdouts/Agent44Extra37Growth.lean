import SweepPumping
import PhaseTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent44Extra37Growth
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent13BlankDelay

def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,true,4⟩)
  | 3,true => some (some ⟨false,true,5⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,true,3⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def T : List Bool := [true,false]
def U : List Bool := [true,true]
def V : List Bool := [false,true]
def ones (n : Nat) : List Bool := rep [true] n

def B (L R : List Bool) : Z0 := ⟨1, if L.isEmpty then [] else false::L,R⟩
def A (a b : Nat) : Z0 := ⟨0,[],false::(rep T a ++ ones b)⟩
def family (n : Nat) : Z0 := B [] (rep T (2*n+2) ++ ones (3*n+1))

def Reach (x y : Z0) : Prop := ∃ n, run0 p n x = some y

theorem rr (x : Z0) : Reach x x := ⟨0,rfl⟩
theorem rt {x y z : Z0} (h : Reach x y) (g : Reach y z) : Reach x z := by
  obtain ⟨n,hn⟩ := h
  obtain ⟨k,hk⟩ := g
  exact ⟨n+k,join0 hn hk⟩

theorem rep_add (xs : List Bool) (a b : Nat) : rep xs (a+b) = rep xs a ++ rep xs b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => rw [Nat.succ_add]; simp only [rep,ih,List.append_assoc]

theorem ones_add (a b : Nat) : ones (a+b) = ones a ++ ones b := rep_add _ _ _
theorem ones_succ (n : Nat) : ones (n+1) = true::ones n := rfl

theorem pairs_ones (n : Nat) : rep U n = ones (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 2*(n+1)=2+2*n by omega,ones_add,rep,ih]; rfl

theorem repT_snoc (n : Nat) (R : List Bool) : rep T n ++ true::false::R = rep T (n+1) ++ R := by
  change rep T n ++ (T ++ R) = rep T (n+1) ++ R
  rw [rep_add,rep]; simp [rep,List.append_assoc]

theorem dSweep (n : Nat) (L R : List Bool) :
    Reach ⟨3,false::L,rep T n++R⟩ ⟨3,false::(rep U n++L),R⟩ := by
  refine ⟨2*n,?_⟩
  exact sweepR p 3 [false] [] T U 2 (by intro l r; rfl) n L R

theorem bSweep (n : Nat) (L R : List Bool) :
    Reach ⟨1,rep U n++L,R⟩ ⟨1,L,rep T n++R⟩ := by
  refine ⟨2*n,?_⟩
  exact sweepL p 1 [] [] U T 2 (by intro l r; rfl) n L R

theorem aSweep (n : Nat) (L R : List Bool) :
    Reach ⟨0,rep U n++L,R⟩ ⟨0,L,rep V n++R⟩ := by
  refine ⟨2*n,?_⟩
  exact sweepL p 0 [] [] U V 2 (by intro l r; rfl) n L R

theorem enterD (k : Nat) (L R : List Bool) :
    Reach (B L (rep T (k+1)++R)) ⟨3,[false,false,true]++L,rep T k++R⟩ := by
  refine ⟨2,?_⟩
  cases L <;> rfl

/-- A trailing 111 block is consumed, one alternating pair and one left 1 are added. -/
theorem reduce3 (k : Nat) (L R : List Bool) :
    Reach (B L (rep T (k+1)++true::true::true::R))
      (B (true::L) (rep T (k+2)++R)) := by
  apply rt (enterD k L (true::true::true::R))
  apply rt (dSweep k (false::true::L) (true::true::true::R))
  have h : Reach ⟨3,false::(rep U k++false::true::L),true::true::true::R⟩
      ⟨1,rep U (k+1)++false::true::L,true::false::R⟩ := ⟨7,rfl⟩
  apply rt h
  simpa only [B,List.isEmpty_cons,Bool.false_eq_true,ite_false,repT_snoc] using
    bSweep (k+1) (false::true::L) (true::false::R)

/-- With one trailing 1, create the separating zero and a final 1. -/
theorem base1 (k : Nat) (L : List Bool) :
    Reach (B L (rep T (k+1)++[true]))
      (B (true::L) (rep T (k+1)++[false,true])) := by
  apply rt (enterD k L [true])
  apply rt (dSweep k (false::true::L) [true])
  have h : Reach ⟨3,false::(rep U k++false::true::L),[true]⟩
      ⟨1,rep U (k+1)++false::true::L,[false,true]⟩ := ⟨5,rfl⟩
  apply rt h
  exact bSweep (k+1) (false::true::L) [false,true]

/-- With no trailing 1, the same turn consumes one alternating pair. -/
theorem base0 (k : Nat) (L : List Bool) :
    Reach (B L (rep T (k+1)))
      (B (true::L) (rep T k++[false,true])) := by
  have e : Reach (B L (rep T (k+1))) ⟨3,[false,false,true]++L,rep T k⟩ := by
    simpa only [List.append_nil] using enterD k L []
  apply rt e
  have d : Reach ⟨3,[false,false,true]++L,rep T k⟩
      ⟨3,false::(rep U k++false::true::L),[]⟩ := by
    simpa only [List.append_nil,List.cons_append,List.nil_append] using dSweep k (false::true::L) []
  apply rt d
  have h : Reach ⟨3,false::(rep U k++false::true::L),[]⟩
      ⟨1,rep U k++false::true::L,[false,true]⟩ := ⟨3,rfl⟩
  exact rt h (bSweep k (false::true::L) [false,true])

/-- Once a separating zero exists, drain one alternating pair and add one 1 on each side. -/
theorem drain1 (k : Nat) (L R : List Bool) :
    Reach (B L (rep T (k+1)++false::R))
      (B (true::L) (rep T k++false::true::R)) := by
  apply rt (enterD k L (false::R))
  apply rt (dSweep k (false::true::L) (false::R))
  have h : Reach ⟨3,false::(rep U k++false::true::L),false::R⟩
      ⟨1,rep U k++false::true::L,false::true::R⟩ := ⟨3,rfl⟩
  exact rt h (bSweep k (false::true::L) (false::true::R))

theorem reduceMany (a j : Nat) (ha : 0<a) (L R : List Bool) :
    Reach (B L (rep T a++ones (3*j)++R))
      (B (ones j++L) (rep T (a+j)++R)) := by
  induction j generalizing a L with
  | zero => simpa [ones,rep] using rr (B L (rep T a++R))
  | succ j ih =>
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    have e : ones (3*(j+1))++R = true::true::true::(ones (3*j)++R) := by
      rw [show 3*(j+1)=3+3*j by omega,ones_add]; rfl
    rw [List.append_assoc,e]
    have h := reduce3 k L (ones (3*j)++R)
    apply rt h
    have hh := ih (k+2) (by omega) (true::L)
    have eL : ones j++true::L = ones (j+1)++L := by
      rw [ones_add,List.append_assoc]; rfl
    simpa only [eL,show k+2+j=k+1+(j+1) by omega,List.append_assoc] using hh

theorem drainMany (a : Nat) (L R : List Bool) :
    Reach (B L (rep T a++false::R))
      (B (ones a++L) (false::(ones a++R))) := by
  induction a generalizing L R with
  | zero => simpa [ones,rep] using rr (B L (false::R))
  | succ a ih =>
    apply rt (drain1 a L R)
    have hh := ih (true::L) (true::R)
    have e (X : List Bool) : ones a++true::X = ones (a+1)++X := by
      rw [ones_add,List.append_assoc]; rfl
    simpa only [e] using hh

theorem exitA (i b : Nat) : Reach (B (ones (2*i+1)) (false::ones b)) (A (i+1) b) := by
  have h : Reach (B (ones (2*i+1)) (false::ones b))
      ⟨0,rep U (i+1),false::ones b⟩ := by
    refine ⟨2,?_⟩
    rw [pairs_ones,show 2*(i+1)=2*i+2 by omega,ones_succ (2*i+1)]
    rfl
  apply rt h
  have hh := aSweep (i+1) [] (false::ones b)
  have e : rep V (i+1)++false::ones b = false::(rep T (i+1)++ones b) := by
    have hrot := rotate false [true] (i+1)
    change false::rep T (i+1) = rep V (i+1)++[false] at hrot
    change rep V (i+1)++([false]++ones b) = _
    rw [← List.append_assoc,← hrot]
    rfl
  simpa only [List.append_nil,e,A] using hh

theorem exitB (i b : Nat) : Reach (B (ones (2*i)) (false::ones b))
    (B [] (rep T (i+1)++ones b)) := by
  have h : Reach (B (ones (2*i)) (false::ones b))
      ⟨1,rep U i,true::false::ones b⟩ := by
    refine ⟨3,?_⟩
    rw [pairs_ones]
    cases i <;> rfl
  apply rt h
  have hh := bSweep i [] (true::false::ones b)
  simpa only [List.append_nil,repT_snoc,B,List.isEmpty_nil,ite_true] using hh

theorem AtoB (a b : Nat) : Reach (A a b) (B [true] (rep T a++ones b)) := ⟨1,rfl⟩

/-- The first sweep phase of the B(n) family. -/
theorem phaseB (n : Nat) : Reach (family n) (A (2*n+2) (3*n+3)) := by
  unfold family
  have e : ones (3*n+1) = ones (3*n)++[true] := ones_add (3*n) 1
  rw [e,← List.append_assoc]
  apply rt (reduceMany (2*n+2) n (by omega) [] [true])
  have h : Reach (B (ones n++[]) (rep T (2*n+2+n)++[true]))
      (B (ones (n+1)) (rep T (3*n+2)++[false,true])) := by
    simpa only [List.append_nil,ones_succ,show 2*n+2+n=3*n+2 by omega] using base1 (3*n+1) (ones n)
  apply rt h
  have hh := drainMany (3*n+2) (ones (n+1)) [true]
  have e1 : ones (3*n+2)++ones (n+1) = ones (4*n+3) := by rw [← ones_add]; congr 1 <;> omega
  have e2 : ones (3*n+2)++[true] = ones (3*n+3) := (ones_add (3*n+2) 1).symm
  rw [e1,e2] at hh
  apply rt hh
  simpa only [show 2*(2*n+1)+1=4*n+3 by omega,show 2*n+1+1=2*n+2 by omega] using exitA (2*n+1) (3*n+3)

/-- Generic A phase: remove all triples, turn at the blank, and drain the alternating block. -/
theorem phaseAcore (a j : Nat) (ha : 0<a) :
    Reach (A a (3*j)) (B (ones (a+2*j+1)) (false::ones (a+j))) := by
  apply rt (AtoB a (3*j))
  have hh := reduceMany a j ha [true] []
  simp only [List.append_nil] at hh
  apply rt hh
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a+j ≠ 0)
  have h := base0 k (ones j++[true])
  have eL : true::(ones j++[true]) = ones (j+2) := by
    rw [show j+2=(j+1)+1 by omega,ones_succ,ones_add]; rfl
  rw [show k+1=a+j by omega,eL] at h
  apply rt h
  have d := drainMany k (ones (j+2)) [true]
  have e1 : ones k++ones (j+2)=ones (a+2*j+1) := by rw [← ones_add]; congr 1 <;> omega
  have e2 : ones k++[true]=ones (a+j) := by rw [show a+j=k+1 by omega,ones_add]; rfl
  simpa only [e1,e2] using d

theorem phaseA1 (n : Nat) : Reach (A (2*n+2) (3*n+3)) (A (2*n+3) (3*n+3)) := by
  have h := phaseAcore (2*n+2) (n+1) (by omega)
  rw [show 3*(n+1)=3*n+3 by omega,show 2*n+2+2*(n+1)+1=4*n+5 by omega,
      show 2*n+2+(n+1)=3*n+3 by omega] at h
  apply rt h
  simpa only [show 2*(2*n+2)+1=4*n+5 by omega,show 2*n+2+1=2*n+3 by omega] using exitA (2*n+2) (3*n+3)

theorem phaseA2 (n : Nat) : Reach (A (2*n+3) (3*n+3)) (family (n+1)) := by
  have h := phaseAcore (2*n+3) (n+1) (by omega)
  rw [show 3*(n+1)=3*n+3 by omega,show 2*n+3+2*(n+1)+1=4*n+6 by omega,
      show 2*n+3+(n+1)=3*n+4 by omega] at h
  apply rt h
  simpa only [family,show 2*(2*n+3)=4*n+6 by omega,show 2*n+3+1=2*(n+1)+2 by omega,
    show 3*n+4=3*(n+1)+1 by omega] using exitB (2*n+3) (3*n+4)

theorem cycle (n : Nat) : Reach (family n) (family (n+1)) :=
  rt (phaseB n) (rt (phaseA1 n) (phaseA2 n))

theorem rep_length (xs : List Bool) (n : Nat) : (rep xs n).length = xs.length*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rep,ih,Nat.mul_succ,Nat.add_comm]

theorem family_length (n : Nat) : (family n).r.length = 7*n+5 := by
  simp only [family,B,List.length_append,ones,rep_length,T,List.length_cons,List.length_nil]
  omega

theorem positive_cycle (n : Nat) : ∃ t, 0<t ∧ run0 p t (family n)=some (family (n+1)) := by
  obtain ⟨t,h⟩ := cycle n
  refine ⟨t,?_,h⟩
  cases t with
  | zero =>
    have e : family n = family (n+1) := Option.some.inj h
    have he := congrArg (fun z : Z0 => z.r.length) e
    rw [family_length,family_length] at he
    omega
  | succ t => omega

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  let cost (n : Nat) := Classical.choose (positive_cycle n)
  apply never_of_growth p family 16 cost (by decide +kernel)
  · intro n; exact (Classical.choose_spec (positive_cycle n)).1
  · intro n; exact (Classical.choose_spec (positive_cycle n)).2
  · exact hm

theorem cover (Bnd : Nat) : Cover (WeightedBound Bnd) p :=
  .leaf _ fun m hm => weighted_never Bnd m (never m hm)
#print axioms never
#print axioms cover
end BB6.Agent44Extra37Growth

