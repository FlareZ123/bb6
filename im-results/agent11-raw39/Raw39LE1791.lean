import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39LE1791
open BB6Coverage BB6Coverage.Agent31Pump

/-- The two leaves differ only in the bit written by E1. -/
def table (b : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨b,false,1⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

abbrev zz : List Bool := [false,false]
abbrev ones (n : Nat) : List Bool := List.replicate n true

def F (L R : List Bool) : Z0 := ⟨5,L,R⟩
def D (L R : List Bool) : Z0 := ⟨3,true::false::L,R⟩
def scan (L R : List Bool) : Z0 := F (false::L) (zz++R)

def bits : List Nat → List Bool
  | [] => []
  | n::ns => zz ++ ones n ++ bits ns

/-- The ready/carry modes alternate after ignoring residue-two digits.
    The last run is exactly one, allowing unbounded width extension. -/
inductive Digits : Bool → List Nat → Prop
  | last : Digits true [1]
  | two {c xs} (n : Nat) : Digits c xs → Digits c ((3*n+2)::xs)
  | one {xs} (n : Nat) : Digits true xs → Digits false ((3*n+1)::xs)
  | zero {xs} (n : Nat) : Digits false xs → Digits true ((3*n+3)::xs)

private theorem ones_add (a b : Nat) : ones (a+b) = ones a ++ ones b := by
  exact List.replicate_append_replicate.symm
private theorem trip_rep (n : Nat) : rep [true,true,true] n = ones (3*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,ih,show 3*(n+1)=3+3*n by omega,ones_add]; rfl
private theorem one_rep (n : Nat) : rep [true] n = ones n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,ih,show n+1=1+n by omega,ones_add]; rfl

private theorem prepend (b : Bool) (R : List Bool) :
    run0 (table b) 10 (F [] (true::R)) = some (F [] (zz++true::R)) := by cases b <;> rfl
private theorem shift_sep (b : Bool) (L R : List Bool) :
    run0 (table b) 10 (F (zz++L) (true::R)) = some (F L (zz++true::R)) := by cases b <;> rfl
private theorem shift_one (b : Bool) (L R : List Bool) :
    run0 (table b) 1 (F (true::L) R) = some (F L (true::R)) := by cases b <;> rfl
private theorem shift_ones (b : Bool) (n : Nat) (L R : List Bool) :
    run0 (table b) n (F (ones n++L) R) = some (F L (ones n++R)) := by
  have H := sweepL (table b) 5 [] [] [true] [true] 1 (shift_one b) n L R
  simpa only [F,List.nil_append,one_rep,Nat.one_mul] using H

private def Restores (b : Bool) (L P : List Bool) : Prop :=
  ∀ R, ∃ k, run0 (table b) k (F L R) = some (F [] (P++R))
private theorem restore_first (b : Bool) (n : Nat) : Restores b (ones n) (ones n) := by
  intro R
  exact ⟨n,by simpa only [List.append_nil] using shift_ones b n [] R⟩
private theorem restore_extend (b : Bool) (n : Nat) {L P : List Bool}
    (h : Restores b L P) : Restores b (ones (n+1)++zz++L) (P++zz++ones (n+1)) := by
  intro R
  have h1 := shift_ones b (n+1) (zz++L) R
  have h2 := shift_sep b L (ones n++R)
  obtain ⟨k,h3⟩ := h (zz++ones (n+1)++R)
  refine ⟨n+1+10+k,?_⟩
  have h2' : run0 (table b) 10 (F (zz++L) (ones (n+1)++R)) = some (F L (zz++ones (n+1)++R)) := by
    simpa only [List.replicate_succ,List.cons_append,List.append_assoc] using h2
  simpa only [List.append_assoc] using join0 (join0 (by simpa only [List.append_assoc,show ones 3 = [true,true,true] by rfl,show ones 2 = [true,true] by rfl] using h1) h2') h3

private theorem trip (b : Bool) (L R : List Bool) :
    run0 (table b) 7 (scan L ([true,true,true]++R)) = some (scan ([true,true,true]++L) R) := by cases b <;> rfl
private theorem trip_first (b : Bool) (R : List Bool) :
    run0 (table b) 7 (F [] (zz++[true,true,true]++R)) = some (scan [true,true,true] R) := by cases b <;> rfl
private theorem sweep_trips (b : Bool) (n : Nat) (L R : List Bool) :
    run0 (table b) (7*n) (scan L (ones (3*n)++R)) = some (scan (ones (3*n)++L) R) := by
  have H := sweepR (table b) 5 [false] zz [true,true,true] [true,true,true] 7 (trip b) n L R
  simpa only [scan,F,trip_rep,List.append_assoc,List.cons_append,List.nil_append] using H

private theorem start_two (b : Bool) (R : List Bool) :
    run0 (table b) 4 (F [] (zz++[true,true]++R)) = some (D [true,true,true] R) := by cases b <;> rfl
private theorem scan_two (b : Bool) (L R : List Bool) :
    run0 (table b) 4 (scan L ([true,true]++R)) = some (D ([true,true,true]++L) R) := by cases b <;> rfl
private theorem d_two (b : Bool) (L R : List Bool) :
    run0 (table b) 4 (D L (zz++[true,true]++R)) = some (D ([true,true]++zz++L) R) := by cases b <;> rfl
private theorem d_trip (b : Bool) (L R : List Bool) :
    run0 (table b) 7 (D L (zz++[true,true,true]++R)) = some (scan ([true,true]++zz++L) R) := by cases b <;> rfl
private theorem scan_zero (b : Bool) (L R : List Bool) :
    run0 (table b) 9 (scan L (zz++R)) = some (F ([true,true]++L) (zz++true::R)) := by cases b <;> rfl
private theorem d_last (b : Bool) (L : List Bool) :
    run0 (table b) 9 (D L (bits [1])) = some (F ([true]++zz++L) (bits [1])) := by cases b <;> rfl

-- A ready word has a first digit. Incrementing it switches to carry mode.
private theorem inc_bits {xs : List Nat} (h : Digits false xs) :
    ∃ R ys, bits xs = zz++R ∧ bits ys = zz++true::R ∧ Digits true ys := by
  cases h with
  | two n h => exact ⟨_,_,rfl,rfl,Digits.zero n h⟩
  | one n h => exact ⟨_,_,rfl,rfl,Digits.two n h⟩

private theorem d_skip (b : Bool) (n : Nat) (L R : List Bool) :
    ∃ k, 0 < k ∧ run0 (table b) k (D L (zz++ones (3*n+2)++R)) =
      some (D (ones (3*n+2)++zz++L) R) := by
  cases n with
  | zero => exact ⟨4,by decide,d_two b L R⟩
  | succ n =>
    have h1 := d_trip b L (ones (3*n)++[true,true]++R)
    have h2 := sweep_trips b n ([true,true]++zz++L) ([true,true]++R)
    have h3 := scan_two b (ones (3*n)++([true,true]++zz++L)) R
    have h1' : run0 (table b) 7 (D L (zz++ones (3*(n+1)+2)++R)) =
        some (scan ([true,true]++zz++L) (ones (3*n)++([true,true]++R))) := by
      rw [show 3*(n+1)+2 = 3+(3*n+2) by omega,ones_add,ones_add (3*n) 2]
      simpa only [List.append_assoc,show ones 3 = [true,true,true] by rfl,show ones 2 = [true,true] by rfl] using h1
    have H := join0 (join0 h1' h2) h3
    refine ⟨7+7*n+4,by omega,?_⟩
    have out : ones (3*(n+1)+2) = [true,true,true] ++ ones (3*n) ++ [true,true] := by
      rw [show 3*(n+1)+2 = 3+(3*n+2) by omega,ones_add,ones_add (3*n) 2]
      simp only [List.append_assoc,show ones 3 = [true,true,true] by rfl,show ones 2 = [true,true] by rfl]
    rw [show D (ones (3*(n+1)+2)++zz++L) R = D ([true,true,true]++(ones (3*n)++([true,true]++zz++L))) R by rw [out]; simp only [List.append_assoc]]
    exact H

private theorem d_stop (b : Bool) (n : Nat) (L R : List Bool) :
    ∃ k, 0 < k ∧ run0 (table b) k (D L (zz++ones (3*n+3)++zz++R)) =
      some (F (ones (3*n+4)++zz++L) (zz++true::R)) := by
  have h1 := d_trip b L (ones (3*n)++zz++R)
  have h2 := sweep_trips b n ([true,true]++zz++L) (zz++R)
  have h3 := scan_zero b (ones (3*n)++([true,true]++zz++L)) R
  have h1' : run0 (table b) 7 (D L (zz++ones (3*n+3)++zz++R)) =
      some (scan ([true,true]++zz++L) (ones (3*n)++(zz++R))) := by
    rw [show 3*n+3 = 3+3*n by omega,ones_add]
    simpa only [List.append_assoc,show ones 3 = [true,true,true] by rfl,show ones 2 = [true,true] by rfl] using h1
  refine ⟨7+7*n+9,by omega,?_⟩
  have H := join0 (join0 h1' h2) h3
  have out : ones (3*n+4) = [true,true] ++ ones (3*n) ++ [true,true] := by
    rw [show 3*n+4 = 2+(3*n+2) by omega,ones_add,ones_add (3*n) 2]
    simp only [List.append_assoc,show ones 2 = [true,true] by rfl]
  rw [show F (ones (3*n+4)++zz++L) (zz++true::R) = F ([true,true]++(ones (3*n)++([true,true]++zz++L))) (zz++true::R) by rw [out]; simp only [List.append_assoc]]
  exact H

private theorem carry_exec (b : Bool) {xs : List Nat} (hd : Digits true xs)
    (L P : List Bool) (h : Restores b L P) :
    ∃ k ys, 0 < k ∧ Digits false ys ∧
      run0 (table b) k (D L (bits xs)) = some (F [] (P++bits ys)) := by
  cases hd with
  | last =>
    obtain ⟨t,ht⟩ := restore_extend b 0 h (bits [1])
    refine ⟨9+t,[1,1],by omega,Digits.one 0 Digits.last,?_⟩
    have H := join0 (d_last b L) ht
    simpa only [bits,List.append_assoc] using H
  | two n hd =>
    obtain ⟨t,ht,he⟩ := d_skip b n L (bits _)
    have hg := restore_extend b (3*n+1) h
    have hg' : Restores b (ones (3*n+2)++zz++L) (P++zz++ones (3*n+2)) := by exact hg
    obtain ⟨k,ys,hk,hy,hr⟩ := carry_exec b hd _ _ hg'
    refine ⟨t+k,_,by omega,Digits.two n hy,?_⟩
    have H := join0 he hr
    simpa only [bits,List.append_assoc] using H
  | zero n hd =>
    obtain ⟨R,ys,hR,hys,hy⟩ := inc_bits hd
    obtain ⟨t,ht,he⟩ := d_stop b n L R
    obtain ⟨k,hk⟩ := restore_extend b (3*n+3) h (zz++true::R)
    refine ⟨t+k,_,by omega,Digits.one (n+1) hy,?_⟩
    rw [bits,hR,← List.append_assoc]
    have H := join0 he hk
    simp only [bits,hys,show 3*(n+1)+1 = 3*n+4 by omega]
    simpa only [List.append_assoc] using H
termination_by xs.length

private theorem prepend_ones (b : Bool) (n : Nat) (R : List Bool) :
    run0 (table b) 10 (F [] (ones (n+1)++R)) = some (F [] (zz++ones (n+1)++R)) := by
  simpa only [List.replicate_succ,List.cons_append,List.append_assoc] using prepend b (ones n++R)

private theorem first_trips (b : Bool) (n : Nat) (R : List Bool) :
    run0 (table b) (7+7*n) (F [] (zz++ones (3*(n+1))++R)) =
      some (scan (ones (3*(n+1))) R) := by
  have h1 := trip_first b (ones (3*n)++R)
  have h2 := sweep_trips b n [true,true,true] R
  have h1' : run0 (table b) 7 (F [] (zz++ones (3*(n+1))++R)) =
      some (scan [true,true,true] (ones (3*n)++R)) := by
    rw [show 3*(n+1)=3+3*n by omega,ones_add]
    simpa only [List.append_assoc,show ones 3=[true,true,true] by rfl] using h1
  have H := join0 h1' h2
  rw [show scan (ones (3*(n+1))) R=scan (ones (3*n)++[true,true,true]) R by rw [show 3*(n+1)=3*n+3 by omega,ones_add];rfl]
  exact H

private theorem first_ready (b : Bool) (n : Nat) {xs : List Nat} (hd : Digits false xs) :
    ∃ k ys, 0 < k ∧ Digits true ys ∧
      run0 (table b) k (F [] (ones (3*n+3)++bits xs)) =
        some (F [] (ones (3*(n+1)+2)++bits ys)) := by
  obtain ⟨R,ys,hR,hys,hy⟩ := inc_bits hd
  have h0 := prepend_ones b (3*n+2) (bits xs)
  have h1 := first_trips b n (bits xs)
  have h1' : run0 (table b) (7+7*n) (F [] (zz++ones (3*n+3)++bits xs)) =
      some (scan (ones (3*n+3)) (bits xs)) := by
    simpa only [show 3*(n+1)=3*n+3 by omega] using h1
  have h2 := scan_zero b (ones (3*n+3)) R
  rw [← hR] at h2
  have h2' : run0 (table b) 9 (scan (ones (3*n+3)) (bits xs)) =
      some (F (ones (3*(n+1)+2)) (zz++true::R)) := by
    have he : ones (3*(n+1)+2) = [true,true]++ones (3*n+3) := by
      rw [show 3*(n+1)+2=2+(3*n+3) by omega,ones_add];rfl
    rw [he]
    exact h2
  obtain ⟨t,ht⟩ := restore_first b (3*(n+1)+2) (zz++true::R)
  refine ⟨10+(7+7*n)+9+t,ys,by omega,hy,?_⟩
  rw [hys]
  exact join0 (join0 (join0 h0 h1') h2') ht

private theorem first_carry_start (b : Bool) (n : Nat) (R : List Bool) :
    ∃ k, 0 < k ∧ run0 (table b) k (F [] (ones (3*n+2)++R)) =
      some (D (ones (3*n+3)) R) := by
  have h0 := prepend_ones b (3*n+1) R
  cases n with
  | zero => exact ⟨14,by decide,join0 h0 (start_two b R)⟩
  | succ n =>
    have h1 := first_trips b n ([true,true]++R)
    have h1' : run0 (table b) (7+7*n) (F [] (zz++ones (3*(n+1)+2)++R)) =
        some (scan (ones (3*(n+1))) ([true,true]++R)) := by
      rw [ones_add (3*(n+1)) 2]
      simpa only [List.append_assoc,show ones 2=[true,true] by rfl] using h1
    have h2 := scan_two b (ones (3*(n+1))) R
    refine ⟨10+(7+7*n)+4,by omega,?_⟩
    have H := join0 (join0 h0 h1') h2
    have he : ones (3*(n+1)+3) = [true,true,true]++ones (3*(n+1)) := by
      rw [show 3*(n+1)+3=3+3*(n+1) by omega,ones_add];rfl
    rw [he]
    exact H

inductive Good : Z0 → Prop
  | ready (n : Nat) {xs : List Nat} : Digits false xs → Good (F [] (ones (3*n+3)++bits xs))
  | carry (n : Nat) {xs : List Nat} : Digits true xs → Good (F [] (ones (3*n+2)++bits xs))

/-- Every ready/carry visit leads to a new visit in the same unbounded grammar. -/
theorem next (b : Bool) {z : Z0} (h : Good z) :
    ∃ k z', 0 < k ∧ Good z' ∧ run0 (table b) k z = some z' := by
  cases h with
  | ready n hd =>
    obtain ⟨k,ys,hk,hy,hr⟩ := first_ready b n hd
    exact ⟨k,_,hk,Good.carry (n+1) hy,hr⟩
  | carry n hd =>
    obtain ⟨t,ht,he⟩ := first_carry_start b n (bits _)
    obtain ⟨k,ys,hk,hy,hr⟩ := carry_exec b hd _ _ (restore_first b (3*n+3))
    exact ⟨t+k,_,by omega,Good.ready n hy,join0 he hr⟩

private theorem entry (b : Bool) : run0 (table b) 177 ⟨0,[],[]⟩ =
    some (F [] (ones 6++bits [2,2,1,1])) := by cases b <;> rfl
private theorem entry_good : Good (F [] (ones 6++bits [2,2,1,1])) :=
  Good.ready 1 (Digits.two 0 (Digits.two 0 (Digits.one 0 Digits.last)))

theorem live (b : Bool) (n : Nat) : ∃ k z, n ≤ k ∧ Good z ∧ run0 (table b) k ⟨0,[],[]⟩ = some z := by
  induction n with
  | zero => exact ⟨177,_,by decide,entry_good,entry b⟩
  | succ n ih =>
    obtain ⟨t,z,ht,hz,hr⟩ := ih
    obtain ⟨k,z',hk,hz',he⟩ := next b hz
    exact ⟨t+k,z',by omega,hz',join0 hr he⟩

theorem never (b : Bool) (m : Machine) (hm : compatible (table b) m) : NeverHalts m := by
  intro n
  obtain ⟨t,z,ht,_,hr⟩ := live b n
  have hz : (BB6Coverage.Agent50Zipper.zrun (table b) t start).map project = some z :=
    (run_project (table b) t start).trans hr
  cases h : BB6Coverage.Agent50Zipper.zrun (table b) t start with
  | none => simp [h] at hz
  | some z =>
    have H := BB6Coverage.Agent50Zipper.zrun_sound (table b) m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms never
end BB6.Agent11Raw39LE1791
