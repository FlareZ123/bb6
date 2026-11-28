import SweepPumping

namespace BB6Coverage.Agent31Pump.Raw13Coupled6OneRAHierarchy
open BB6Coverage Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,1⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true => some (some ⟨false,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none

def A (L R : List Bool) : Z0 := ⟨0,L,R⟩
def B (L R : List Bool) : Z0 := ⟨1,L,R⟩
def one : List Bool := [true]
def zero : List Bool := [false]
def d0 : List Bool := [false,true,false,true]
def d1 : List Bool := [false,true,true,false]
def pair : List Bool := [false,true]

theorem b_shift (L R : List Bool) :
    run0 p 1 (B (true::L) (true::R)) = some (B (true::false::L) R) := by rfl

theorem b_sweep (n : Nat) (L R : List Bool) :
    run0 p n (B (true::L) (rep one n ++ R)) = some (B (true::(rep zero n ++ L)) R) := by
  simpa [B,one,zero] using sweepR p 1 [true] [] [true] [false] 1 b_shift n L R

theorem b_scan (k : Nat) (L R : List Bool) (b : Bool) :
    run0 p k (B ((rep one k ++ b::R).headD false::L) (rep one k ++ b::R).tail) =
    some (B (b::(rep zero k ++ L)) R) := by
  cases k with
  | zero => rfl
  | succ k =>
    have h := b_sweep k L (b::R)
    have f (X : List Bool) : run0 p 1 (B (true::X) (b::R)) = some (B (b::false::X) R) := by rfl
    have H := join0 h (f (rep zero k ++ L))
    simpa [rep,one,zero] using H

theorem start_scan (k : Nat) (L R : List Bool) (b : Bool) :
    run0 p (k+1) (A (false::L) (rep one k ++ b::R)) =
      some (B (b::(rep zero k ++ true::L)) R) := by
  have h : run0 p 1 (A (false::L) (rep one k ++ b::R)) =
      some (B ((rep one k ++ b::R).headD false::true::L) (rep one k ++ b::R).tail) := by rfl
  have H := join0 h (b_scan k (true::L) R b)
  simpa [Nat.add_comm] using H

theorem left_pair (L R : List Bool) : run0 p 2 (A (true::true::L) R) = some (A L (false::true::R)) := by rfl

theorem left_triple (L R : List Bool) : run0 p 3 (A (true::false::false::L) R) = some (A L (true::true::true::R)) := by rfl

theorem rep_add' (b : List Bool) (n m : Nat) : rep b (n+m) = rep b n ++ rep b m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => rw [show n+1+m=n+m+1 by omega]; simp [rep,ih,List.append_assoc]

theorem rep11_double (j : Nat) : rep [true,true] (2*j) = rep [true,true,true,true] j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [show 2*(j+1)=2+2*j by omega,rep_add',ih]; rfl

theorem pair_double (j : Nat) : rep pair (2*j) = rep d0 j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [show 2*(j+1)=2+2*j by omega,rep_add',ih]; rfl

theorem left_pairs (n : Nat) (L R : List Bool) :
    run0 p (2*n) (A (rep [true,true] n ++ L) R) = some (A L (rep pair n ++ R)) := by
  simpa [A,pair] using sweepL p 0 [] [] [true,true] [false,true] 2 left_pair n L R

theorem d1_scan (j : Nat) (L R : List Bool) :
    run0 p (4*j) (A (false::L) (rep d1 j ++ R)) = some (A (false::(rep [true,true,true,true] j ++ L)) R) := by
  have h (X Y : List Bool) : run0 p 4 (A (false::X) (d1 ++ Y)) = some (A (false::true::true::true::true::X) Y) := by rfl
  simpa [A] using sweepR p 0 [false] [] d1 [true,true,true,true] 4 h j L R

/-- A uniform increment interface, parametrized by the entire protected right word. -/
def Good (R S : List Bool) : Prop := ∀ k L,
  ∃ t, 0<t ∧ run0 p t (A (false::L) (rep one k ++ R)) =
    some (A (rep zero k ++ true::L) S)

inductive Steps : Nat → List Bool → List Bool → Prop where
  | nil (R) : Steps 0 R R
  | cons {n R S T} : Good R S → Steps n S T → Steps (n+1) R T

theorem split {m n : Nat} {R T : List Bool} (h : Steps (m+n) R T) :
    ∃ S, Steps m R S ∧ Steps n S T := by
  induction m generalizing R with
  | zero => exact ⟨R,.nil R,by simpa using h⟩
  | succ m ih =>
    rw [show m+1+n=m+n+1 by omega] at h
    cases h with
    | cons hi hs =>
      obtain ⟨S,hm,hn⟩ := ih hs
      exact ⟨S,.cons hi hm,hn⟩

def Drain (k : Nat) : Prop := ∀ (L : List Bool) {R S : List Bool},
  Steps (2^k-1) R S → ∃ t, run0 p t (A (rep zero (3*k) ++ L) R) =
    some (A L (rep one (3*k) ++ S))

def Fill (k : Nat) : Prop := ∀ (L : List Bool) {R S : List Bool},
  Steps (2^k) R S → ∃ t, 0<t ∧ run0 p t (A (false::L) (rep one (3*k) ++ R)) =
    some (A (true::L) (rep one (3*k) ++ S))

theorem fill_of_drain {k : Nat} (hd : Drain k) : Fill k := by
  intro L R S hs
  have hp := Nat.two_pow_pos k
  have eq : 2^k=2^k-1+1 := by omega
  rw [eq] at hs
  cases hs with
  | cons hi hn =>
    obtain ⟨a,ha,h⟩ := hi (3*k) L
    obtain ⟨b,hb⟩ := hd (true::L) hn
    exact ⟨a+b,by omega,join0 h hb⟩

theorem drain_all (k : Nat) : Drain k := by
  induction k with
  | zero =>
    intro L R S hs
    cases hs
    exact ⟨0,rfl⟩
  | succ k ih =>
    intro L R S hs
    have hp := Nat.two_pow_pos k
    have eq : 2^(k+1)-1=(2^k-1)+2^k := by rw [Nat.pow_succ]; omega
    rw [eq] at hs
    obtain ⟨mid,hm,hn⟩ := split hs
    obtain ⟨a,ha⟩ := ih (false::false::false::L) hm
    obtain ⟨b,hbp,hb⟩ := fill_of_drain ih (false::false::L) hn
    have hc := left_triple L (rep one (3*k) ++ S)
    have h := join0 (join0 ha hb) hc
    refine ⟨a+b+3,?_⟩
    have e : 3*(k+1)=3*k+3 := by omega
    rw [e,rep_add']
    simpa [rep,zero,one,List.append_assoc] using h

theorem fill_all (k : Nat) : Fill k := fill_of_drain (drain_all k)

theorem first_d1 (k : Nat) (L R : List Bool) :
    run0 p (k+4) (A (false::L) (rep one k ++ d1 ++ R)) =
      some (A (false::true::true::true::(rep zero k ++ true::L)) R) := by
  have h := start_scan k L (true::true::false::R) false
  have f (X : List Bool) : run0 p 3 (B (false::X) (true::true::false::R)) =
    some (A (false::true::true::true::X) R) := by rfl
  simpa [d1,Nat.add_assoc] using join0 h (f (rep zero k ++ true::L))

theorem ones_commute (j : Nat) (X : List Bool) :
    true::(rep [true,true,true,true] j ++ true::true::true::X) =
      rep [true,true,true,true] (j+1) ++ X := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change true::true::true::true::(true::(rep [true,true,true,true] j ++ true::true::true::X)) =
      true::true::true::true::(rep [true,true,true,true] (j+1) ++ X)
    rw [ih]

/-- An all-ones low block overflows through a delimiter of 3*m ones, provided
    the high word supports exactly 2^m successful increments. -/
theorem overflow_delimiter (j m : Nat) {R S : List Bool} (hs : Steps (2^m) R S) :
    Good (rep d1 (j+1) ++ rep one (3*m) ++ R)
         (rep d0 (j+1) ++ rep one (3*m) ++ S) := by
  intro k L
  have h := first_d1 k L (rep d1 j ++ rep one (3*m) ++ R)
  have h' := d1_scan j (true::true::true::(rep zero k ++ true::L)) (rep one (3*m) ++ R)
  have h1 := join0 h (by simpa only [List.append_assoc] using h')
  obtain ⟨a,ha,h2⟩ := fill_all m (rep [true,true,true,true] j ++ true::true::true::(rep zero k ++ true::L)) hs
  have h3 := join0 h1 h2
  rw [ones_commute,←rep11_double] at h3
  have h4 := join0 h3 (left_pairs (2*(j+1)) (rep zero k ++ true::L) (rep one (3*m) ++ S))
  refine ⟨k+4+4*j+a+2*(2*(j+1)),by omega,?_⟩
  simpa [rep,pair_double,List.append_assoc] using h4

theorem good_zero (R : List Bool) : Good (d0 ++ R) (d1 ++ R) := by
  intro k L
  have h := start_scan k L (true::false::true::R) false
  have f (X : List Bool) : run0 p 5 (B (false::X) (true::false::true::R)) =
      some (A (true::true::X) (true::false::R)) := by rfl
  have H := join0 (join0 h (f (rep zero k ++ true::L))) (left_pair (rep zero k ++ true::L) (true::false::R))
  exact ⟨k+8,by omega,by simpa [d0,d1,Nat.add_assoc] using H⟩

theorem good_carry (j : Nat) (R : List Bool) :
    Good (rep d1 j ++ d0 ++ R) (rep d0 j ++ d1 ++ R) := by
  cases j with
  | zero => simpa [rep] using good_zero R
  | succ j =>
    have h : Steps (2^0) (d0++R) (d1++R) := .cons (good_zero R) (.nil _)
    simpa only [Nat.mul_zero, Nat.zero_mul, rep, List.nil_append, List.append_assoc] using overflow_delimiter j 0 h

#print axioms overflow_delimiter
#print axioms good_carry
end BB6Coverage.Agent31Pump.Raw13Coupled6OneRAHierarchy
