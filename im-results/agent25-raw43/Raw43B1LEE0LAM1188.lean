import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B1LEE0LAM1188
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def ones (n : Nat) := List.replicate n true
def zeros (n : Nat) := List.replicate n false
def P : List Bool := [false,true,false,true]
def Q : List Bool := [true,false,true,false]
def K : List Bool := [false,false,false,true]
def A (k n : Nat) (L : List Bool) : Z0 := ⟨0,L,rep P k++false::ones n⟩
def B (k n : Nat) (L : List Bool) : Z0 := ⟨1,false::L,rep Q k++ones n⟩
def C (n : Nat) (L : List Bool) : Z0 := ⟨2,(ones n).headD false::L,(ones n).tail⟩
def D (n : Nat) (L R : List Bool) : Z0 := ⟨3,zeros n++true::L,R⟩

private theorem frame (k : Nat) (R : List Bool) : rep P k++false::R = false::(rep Q k++R) := by
  have h := rotate false [true,false,true] k
  change [false]++rep Q k = rep P k++[false] at h
  have H := congrArg (fun x => x++R) h.symm
  simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using H

private theorem C_sweep (n : Nat) (L : List Bool) :
    run0 table n (C n L) = some ⟨2,false::(zeros n++L),[]⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 1 (C (n+1) L) = some (C n (false::L)) := by
      simp only [C,ones,List.replicate_succ,List.headD_cons,List.tail_cons]
      rfl
    have H := join0 h (ih (false::L))
    rw [Nat.add_comm 1 n] at H
    simpa only [zeros,List.replicate_succ',List.append_assoc,List.singleton_append] using H

private theorem D_sweep (n : Nat) (L R : List Bool) :
    run0 table n (D n L R) = some (D 0 L (ones n++R)) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h : run0 table 1 (D (n+1) L R) = some (D n L (true::R)) := by
      simp only [D,zeros,List.replicate_succ,List.cons_append]
      rfl
    have H := join0 h (ih (true::R))
    rw [Nat.add_comm 1 n] at H
    simpa only [ones,List.replicate_succ',List.append_assoc,List.singleton_append] using H

private theorem B_finish (n : Nat) (L : List Bool) :
    run0 table (2*n+7) (B 0 n L) = some (A 0 (n+2) L) := by
  have h1 : run0 table 1 (B 0 n L) = some (C n (true::L)) := by rfl
  have h2 := C_sweep n (true::L)
  have h3 : run0 table 1 ⟨2,false::(zeros n++true::L),[]⟩ = some (D (n+2) L []) := by
    simp only [D,zeros,List.replicate_succ,List.cons_append]
    rfl
  have h4 := D_sweep (n+2) L []
  have h5 : run0 table 3 (D 0 L (ones (n+2)++[])) = some (A 0 (n+2) L) := by
    simp only [D,A,rep,ones,List.replicate_succ,List.nil_append,List.append_nil]
    rfl
  have H := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  rw [show 2*n+7 = 1+n+1+(n+2)+3 by omega]
  exact H

private theorem B_block (L R : List Bool) :
    run0 table 4 ⟨1,[false]++L,Q++R⟩ = some ⟨1,[false]++K++L,R⟩ := by rfl

private theorem B_return (k n : Nat) (L : List Bool) :
    run0 table (4*k+2*n+7) (B k n L) = some (A 0 (n+2) (rep K k++L)) := by
  have h1 := sweepR table 1 [false] [] Q K 4 B_block k L (ones n)
  have h1' : run0 table (4*k) (B k n L) = some (B 0 n (rep K k++L)) := by
    simpa only [B,rep,List.nil_append,List.singleton_append,List.cons_append,List.append_assoc] using h1
  have H := join0 h1' (B_finish n (rep K k++L))
  rw [show 4*k+2*n+7 = 4*k+(2*n+7) by omega]
  exact H

def Digit := Bool × Bool × Bool
def bits (d : Digit) : List Bool := [d.1,false,d.2.1,d.2.2]
def encode : List Digit → List Bool
  | [] => []
  | d::ds => bits d ++ encode ds

def z : Digit := (false,false,false)
def reset : Digit := (false,false,true)

private theorem a_zero (k n : Nat) (b c : Bool) (L : List Bool) :
    run0 table 1 (A k n (bits (false,b,c)++L)) = some (B k n (bits (true,b,c)++L)) := by
  simp only [A,B,frame]
  rfl
private theorem a_one (k n : Nat) (c : Bool) (L : List Bool) :
    run0 table 5 (A k n (bits (true,false,c)++L)) = some (B k n (bits (false,true,c)++L)) := by
  simp only [A,B,frame]
  rfl
private theorem a_full (k n : Nat) (L : List Bool) :
    run0 table 7 (A k n (bits (true,true,true)++L)) = some (B k n (bits z++L)) := by
  simp only [A,B,frame]
  rfl
private theorem a_carry (k n : Nat) (L : List Bool) :
    run0 table 4 (A k n (bits (true,true,false)++L)) = some (A (k+1) n L) := by
  simp only [A,rep,List.append_assoc]
  rfl

/-- Carry through any finite prefix, with one reserved zero digit. -/
theorem carry_reset (ds : List Digit) (k n : Nat) (U : List Bool) :
    ∃ t ds', 0<t ∧ run0 table t (A k n (encode ds++bits z++U)) =
      some (A 0 (n+2) (rep K k++encode ds'++U)) := by
  induction ds generalizing k with
  | nil =>
    have H := join0 (a_zero k n false false U) (B_return k n (bits (true,false,false)++U))
    exact ⟨1+(4*k+2*n+7),[(true,false,false)],by omega,by simpa only [encode,z,List.nil_append,List.append_nil,List.append_assoc] using H⟩
  | cons d ds ih =>
    rcases d with ⟨a,b,c⟩
    cases a with
    | false =>
      have H := join0 (a_zero k n b c (encode ds++bits z++U)) (B_return k n (bits (true,b,c)++(encode ds++bits z++U)))
      have he : ∀ xs ys : List Digit, encode (xs++ys) = encode xs++encode ys := by
        intro xs ys; induction xs with
        | nil => rfl
        | cons x xs ih => simp only [List.cons_append,encode,ih,List.append_assoc]
      exact ⟨1+(4*k+2*n+7),(true,b,c)::(ds++[z]),by omega,by simpa only [encode,he,List.append_nil,List.append_assoc] using H⟩
    | true =>
      cases b with
      | false =>
        have H := join0 (a_one k n c (encode ds++bits z++U)) (B_return k n (bits (false,true,c)++(encode ds++bits z++U)))
        have he : ∀ xs ys : List Digit, encode (xs++ys) = encode xs++encode ys := by
          intro xs ys; induction xs with
          | nil => rfl
          | cons x xs ih => simp only [List.cons_append,encode,ih,List.append_assoc]
        exact ⟨5+(4*k+2*n+7),(false,true,c)::(ds++[z]),by omega,by simpa only [encode,he,List.append_nil,List.append_assoc] using H⟩
      | true =>
        cases c with
        | false =>
          obtain ⟨t,ds',ht,h⟩ := ih (k+1)
          have H := join0 (a_carry k n (encode ds++bits z++U)) h
          have he : rep K (k+1) = rep K k++bits reset := by
            rw [rep,← rep_snoc]; rfl
          rw [he] at H
          exact ⟨4+t,reset::ds',by omega,by simpa only [encode,List.append_assoc] using H⟩
        | true =>
          have H := join0 (a_full k n (encode ds++bits z++U)) (B_return k n (bits z++(encode ds++bits z++U)))
          have he : ∀ xs ys : List Digit, encode (xs++ys) = encode xs++encode ys := by
            intro xs ys; induction xs with
            | nil => rfl
            | cons x xs ih => simp only [List.cons_append,encode,ih,List.append_assoc]
          exact ⟨7+(4*k+2*n+7),z::(ds++[z]),by omega,by simpa only [encode,he,List.append_nil,List.append_assoc] using H⟩

theorem epochs (N n : Nat) (ds : List Digit) :
    ∃ t u, N≤t ∧ run0 table t (A 0 n (encode ds++zeros (4*N))) = some u := by
  induction N generalizing n ds with
  | zero => exact ⟨0,_,by omega,rfl⟩
  | succ N ih =>
    have hpad : zeros (4*(N+1)) = bits z++zeros (4*N) := by
      change List.replicate (4*(N+1)) false = List.replicate 4 false ++ List.replicate (4*N) false
      rw [List.replicate_append_replicate]; congr 1 <;> omega
    obtain ⟨a,ds',ha,h1⟩ := carry_reset ds 0 n (zeros (4*N))
    obtain ⟨b,u,hb,h2⟩ := ih (n+2) ds'
    have H := join0 h1 h2
    exact ⟨a+b,u,by omega,by simpa only [hpad,List.append_assoc] using H⟩

theorem padded_live (N : Nat) :
    ∃ t u, N≤t ∧ run0 table t ⟨0,zeros (4*N),[false]⟩ = some u := by
  simpa only [A,encode,List.nil_append,rep,ones,List.replicate_zero] using epochs N 0 []
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

/-- All 25 completions of the literal one-hole table are nonhalting. -/
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,hr⟩ := padded_live n
  let start : Z := ⟨0,0,zeros (4*n),zeros 1⟩
  have hz : (zrun table t start).map project = some z :=
    (run_project table t start).trans hr
  cases hZ : zrun table t start with
  | none => simp [hZ] at hz
  | some z' =>
    have H := zrun_sound table m hm t start z' hZ
    have hb : embed start = blank := padded_blank _ _
    rw [hb] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms never
end BB6.Agent25Raw43B1LEE0LAM1188
