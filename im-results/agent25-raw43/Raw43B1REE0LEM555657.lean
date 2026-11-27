import SweepPumping
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B1REE0LEM555657
open BB6Coverage BB6Coverage.Agent31Pump

inductive V where | a | b | c
  deriving DecidableEq

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,false => some (some (match v with
    | .a => ⟨false,true,0⟩
    | .b => ⟨false,true,1⟩
    | .c => ⟨true,false,2⟩))
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none

def ones (n : Nat) := List.replicate n true
def zeros (n : Nat) := List.replicate n false
def pad : List Bool := [false,false]
def base : V → Nat | .a => 0 | _ => 2
def startCost : V → Nat | .a => 0 | .b => 14 | .c => 16
def finishCost : V → Nat | .a => 1 | .b => 17 | .c => 23

def A (v : V) (k : Nat) (R : List Bool) : Z0 :=
  ⟨0,false::(ones (3*k+base v)++pad),R⟩
def F (n : Nat) (R : List Bool) : Z0 := ⟨5,ones n++pad,R⟩

inductive Digit where | zero | one | two
  deriving DecidableEq

def bits : Digit → List Bool
  | .zero => [false,false,false]
  | .one => [true,false,false]
  | .two => [false,true,false]

def encode : List Digit → List Bool
  | [] => []
  | d::ds => bits d ++ encode ds

theorem carry (v : V) (k : Nat) (U : List Bool) :
    run0 (table v) 3 (A v k (bits .two++U)) = some (A v (k+1) U) := by
  have he : 3*(k+1)+base v = (3*k+base v)+3 := by omega
  simp only [A,he,ones,List.replicate_succ,List.cons_append]
  cases v <;> rfl

theorem zero_local (v : V) (k : Nat) (U : List Bool) :
    run0 (table v) 10 (A v k (bits .zero++U)) =
      some (F (3*k+base v+1) (bits .one++U)) := by
  simp only [A,F,ones,List.replicate_succ,List.cons_append]
  cases v <;> rfl

theorem one_local (v : V) (k : Nat) (U : List Bool) :
    run0 (table v) 3 (A v k (bits .one++U)) =
      some (F (3*k+base v+2) ([true,false]++U)) := by
  simp only [A,F,ones,List.replicate_succ,List.cons_append]
  cases v <;> rfl

theorem sweep (v : V) (n : Nat) (R : List Bool) :
    run0 (table v) n (F n R) = some (F 0 (zeros n++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 (table v) 1 (F (n+1) R) = some (F n (false::R)) := by
      simp only [F,ones,List.replicate_succ,List.cons_append]
      cases v <;> rfl
    have H := join0 h (ih (false::R))
    rw [Nat.add_comm 1 n] at H
    simpa only [zeros,List.replicate_succ',List.append_assoc,List.singleton_append] using H

theorem finish (v : V) (U : List Bool) :
    run0 (table v) (finishCost v) (F 0 (zeros (base v+1)++U)) = some (A v 0 U) := by
  cases v <;> rfl

theorem zero_reset (v : V) (k : Nat) (U : List Bool) :
    ∃ t, 0<t ∧ run0 (table v) t (A v k (bits .zero++U)) =
      some (A v 0 (zeros (3*k)++bits .one++U)) := by
  have h1 := zero_local v k U
  have h2 := sweep v (3*k+base v+1) (bits .one++U)
  have H := join0 h1 h2
  have he : zeros (3*k+base v+1) = zeros (base v+1)++zeros (3*k) := by
    simp only [zeros,List.replicate_append_replicate]; congr 1 <;> omega
  rw [he] at H
  have H' := join0 H (by simpa only [List.append_assoc] using finish v (zeros (3*k)++bits .one++U))
  exact ⟨10+(3*k+base v+1)+finishCost v,by omega,by simpa only [List.append_assoc] using H'⟩

theorem one_reset (v : V) (k : Nat) (U : List Bool) :
    ∃ t, 0<t ∧ run0 (table v) t (A v k (bits .one++U)) =
      some (A v 0 (zeros (3*k)++bits .two++U)) := by
  have h1 := one_local v k U
  have h2 := sweep v (3*k+base v+2) ([true,false]++U)
  have H := join0 h1 h2
  have he : zeros (3*k+base v+2)++([true,false]++U) =
      zeros (base v+1)++(zeros (3*k)++bits .two++U) := by
    have h : zeros (3*k+base v+2) = zeros (base v+1)++zeros (3*k)++[false] := by
      simp only [zeros,← List.replicate_succ',List.replicate_append_replicate]; congr 1 <;> omega
    rw [h]
    simp only [bits,List.append_assoc,List.singleton_append]
    rfl
  rw [he] at H
  exact ⟨3+(3*k+base v+2)+finishCost v,by omega,join0 H (finish v _)⟩

theorem carry_reset (v : V) (ds : List Digit) (k : Nat) (U : List Bool) :
    ∃ t ds', 0<t ∧ run0 (table v) t (A v k (encode ds++bits .zero++U)) =
      some (A v 0 (zeros (3*k)++encode ds'++U)) := by
  induction ds generalizing k with
  | nil =>
    obtain ⟨t,ht,h⟩ := zero_reset v k U
    exact ⟨t,[.one],ht,by simpa only [encode,List.nil_append,List.append_nil] using h⟩
  | cons d ds ih =>
    cases d with
    | zero =>
      obtain ⟨t,ht,h⟩ := zero_reset v k (encode ds++bits .zero++U)
      refine ⟨t,.one::(ds++[.zero]),ht,?_⟩
      have he : ∀ xs ys, encode (xs++ys) = encode xs++encode ys := by
        intro xs ys; induction xs with
        | nil => rfl
        | cons x xs ih => simp only [List.cons_append,encode,ih,List.append_assoc]
      simpa only [encode,he,List.append_nil,List.append_assoc] using h
    | one =>
      obtain ⟨t,ht,h⟩ := one_reset v k (encode ds++bits .zero++U)
      refine ⟨t,.two::(ds++[.zero]),ht,?_⟩
      have he : ∀ xs ys, encode (xs++ys) = encode xs++encode ys := by
        intro xs ys; induction xs with
        | nil => rfl
        | cons x xs ih => simp only [List.cons_append,encode,ih,List.append_assoc]
      simpa only [encode,he,List.append_nil,List.append_assoc] using h
    | two =>
      have h1 := carry v k (encode ds++bits .zero++U)
      obtain ⟨t,ds',ht,h2⟩ := ih (k+1)
      have H := join0 h1 h2
      have he : zeros (3*(k+1)) = zeros (3*k)++bits .zero := by
        change List.replicate (3*(k+1)) false = List.replicate (3*k) false ++ List.replicate 3 false
        rw [List.replicate_append_replicate]; congr 1 <;> omega
      rw [he] at H
      exact ⟨3+t,.zero::ds',by omega,by simpa only [encode,List.append_assoc] using H⟩

theorem epochs (v : V) (N : Nat) (ds : List Digit) (U : List Bool) :
    ∃ t z, N≤t ∧ run0 (table v) t (A v 0 (encode ds++zeros (3*N)++U)) = some z := by
  induction N generalizing ds with
  | zero => exact ⟨0,_,by omega,rfl⟩
  | succ N ih =>
    have hpad : zeros (3*(N+1)) = bits .zero++zeros (3*N) := by
      change List.replicate (3*(N+1)) false = List.replicate 3 false ++ List.replicate (3*N) false
      rw [List.replicate_append_replicate]; congr 1 <;> omega
    obtain ⟨a,ds',ha,h1⟩ := carry_reset v ds 0 (zeros (3*N)++U)
    obtain ⟨b,z,hb,h2⟩ := ih ds'
    have H := join0 h1 (by simpa only [zeros,Nat.mul_zero,List.replicate_zero,List.nil_append,List.append_assoc] using h2)
    exact ⟨a+b,z,by omega,by simpa only [hpad,List.append_assoc] using H⟩

theorem first (v : V) (U : List Bool) :
    run0 (table v) (startCost v) ⟨0,zeros 3,zeros (base v+1)++U⟩ =
      some (A v 0 (false::U)) := by
  cases v <;> rfl

theorem padded_live (v : V) (N : Nat) :
    ∃ t z, N≤t ∧ run0 (table v) t ⟨0,zeros 3,zeros (base v+1+3*N)⟩ = some z := by
  -- Use N reserved digits plus one trailing zero.  For the initial macro,
  -- the leading zero of that reserve is kept at the next section.
  have h1 := first v (zeros (3*N))
  have h2 : ∃ t z, N≤t ∧ run0 (table v) t (A v 0 (false::zeros (3*N))) = some z := by
    obtain ⟨t,z,ht,h⟩ := epochs v N [] [false]
    refine ⟨t,z,ht,?_⟩
    have he : false::zeros (3*N) = zeros (3*N)++[false] := by
      simp only [zeros,← List.replicate_succ,List.replicate_succ']
    simpa only [he,encode,List.nil_append] using h
  obtain ⟨t,z,ht,h⟩ := h2
  have H := join0 h1 h
  exact ⟨startCost v+t,z,by omega,by simpa only [zeros,List.replicate_append_replicate] using H⟩

#print axioms padded_live
open BB6Coverage.Agent50Zipper

private theorem getD_zeros (k i : Nat) : (zeros k).getD i false = false := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

private theorem padded_blank (a b : Nat) : embed ⟨0,0,zeros a,zeros b⟩ = blank := by
  unfold embed blank
  congr 1
  funext x
  unfold atCell
  split <;> simp only [getD_zeros]

/-- All 25 completions of each of the three literal tables are nonhalting. -/
theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr⟩ := padded_live v n
  let start : Z := ⟨0,0,zeros 3,zeros (base v+1+3*n)⟩
  have hz : (zrun (table v) t start).map project = some z :=
    (run_project (table v) t start).trans hr
  cases hZ : zrun (table v) t start with
  | none => simp [hZ] at hz
  | some z' =>
    have H := zrun_sound (table v) m hm t start z' hZ
    have hb : embed start = blank := padded_blank _ _
    rw [hb] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms never
end BB6.Agent25Raw43B1REE0LEM555657
