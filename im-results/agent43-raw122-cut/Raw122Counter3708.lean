import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw122Counter3708
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

abbrev b4 : List Bool := [true,false,false,true]
abbrev ones : List Bool := [true,true]
abbrev zeros : List Bool := [false,false]
def enc : List Bool → List Bool
  | [] => []
  | b::bs => false :: b :: enc bs
def headEnc : List Bool → List Bool
  | [] => []
  | b::bs => b :: enc bs

def family (k : Nat) (ds : List Bool) : Z0 :=
  ⟨1,[false,true,false,true] ++ rep b4 k ++ [true,false] ++ enc ds,[]⟩

theorem entry : run0 table 17 ⟨0,[],[]⟩ = some (family 0 [true]) := by rfl

theorem enter (L : List Bool) :
  run0 table 7 ⟨1,[false,true,false,true]++L,[]⟩ =
    some ⟨1,[true,false,true]++L,[false,false,true]⟩ := by rfl

theorem left_one (L R : List Bool) :
  run0 table 16 ⟨1,[true,false,true]++b4++L,[false,false,true]++R⟩ =
    some ⟨1,[true,false,true]++L,[false,false,true]++b4++R⟩ := by rfl

theorem left_all (k : Nat) (L : List Bool) :
  run0 table (16*k) ⟨1,[true,false,true]++rep b4 k++L,[false,false,true]⟩ =
    some ⟨1,[true,false,true]++L,[false,false,true]++rep b4 k⟩ := by
  simpa only [List.append_nil] using sweepL table 1 [true,false,true] [false,false,true] b4 b4 16 left_one k L []

theorem prep (ds R : List Bool) :
  run0 table 18 ⟨1,[true,false,true,true,false]++enc ds,[false,false,true]++R⟩ =
    some ⟨1,headEnc ds,ones++[false,false,true]++b4++R⟩ := by
  cases ds <;> rfl

theorem carryOne (ds R : List Bool) :
  run0 table 2 ⟨1,headEnc (true::ds),R⟩ = some ⟨1,headEnc ds,ones++R⟩ := by
  cases ds <;> rfl

theorem stop_first (L R : List Bool) :
  run0 table 2 ⟨1,false::L,ones++R⟩ = some ⟨0,[true,false,true]++L,R⟩ := by rfl

theorem clear_one (L R : List Bool) :
  run0 table 2 ⟨0,[true]++L,ones++R⟩ = some ⟨0,[true]++zeros++L,R⟩ := by rfl

theorem stop_last (L R : List Bool) :
  run0 table 2 ⟨0,[true]++L,[false,false,true]++R⟩ =
    some ⟨1,[false,true,false]++L,true::R⟩ := by rfl

theorem zeros_comm (k : Nat) : false :: rep zeros k = rep zeros k ++ [false] := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rep,zeros,List.cons_append,List.nil_append]; rw [← ih]

theorem stop (n : Nat) (L R : List Bool) :
  run0 table (2*n+4) ⟨1,false::L,rep ones (n+1)++[false,false,true]++R⟩ =
    some ⟨1,[false,true]++rep zeros (n+1)++[true]++L,true::R⟩ := by
  have h1 := stop_first L (rep ones n ++ [false,false,true] ++ R)
  have h2 := sweepR table 0 [true] [] ones zeros 2 (by simpa only [List.nil_append] using clear_one) n ([false,true]++L) ([false,false,true]++R)
  have h3 := stop_last (rep zeros n++[false,true]++L) R
  simp only [List.nil_append,List.append_assoc] at h1 h2 h3
  have h := join0 (join0 h1 h2) h3
  rw [show 2+2*n+2=2*n+4 by omega] at h
  simp only [rep,List.append_assoc,zeros,ones,List.cons_append,List.nil_append] at h ⊢
  have hz := congrArg (fun x : List Bool => x ++ true::L) (zeros_comm n)
  simp only [zeros,List.cons_append,List.append_assoc,List.nil_append] at hz
  rw [← hz] at h
  exact h

theorem stop_nil (n : Nat) (R : List Bool) :
  run0 table (2*n+4) ⟨1,[],rep ones (n+1)++[false,false,true]++R⟩ =
    some ⟨1,[false,true]++rep zeros (n+1)++[true],true::R⟩ := by
  have h := stop n [] R
  have he : run0 table (2*n+4) ⟨1,[],rep ones (n+1)++[false,false,true]++R⟩ =
    run0 table (2*n+4) ⟨1,[false],rep ones (n+1)++[false,false,true]++R⟩ := by rfl
  rw [he]
  simpa only [List.append_nil] using h

theorem carry (ds : List Bool) (n : Nat) (R : List Bool) :
    ∃ t N tail, n ≤ N ∧ 0<t ∧
      run0 table t ⟨1,headEnc ds,rep ones (n+1)++[false,false,true]++R⟩ =
        some ⟨1,[false,true]++rep zeros (N+1)++[true]++enc tail,true::R⟩ := by
  induction ds generalizing n with
  | nil =>
    exact ⟨2*n+4,n,[],Nat.le_refl _,by omega,by simpa only [headEnc,enc,List.append_nil] using stop_nil n R⟩
  | cons b bs ih =>
    cases b with
    | false => exact ⟨2*n+4,n,bs,Nat.le_refl _,by omega,stop n (enc bs) R⟩
    | true =>
      obtain ⟨t,N,tail,hN,ht,h⟩ := ih (n+1)
      have h1 := carryOne bs (rep ones (n+1)++[false,false,true]++R)
      have h1' : run0 table 2 ⟨1,headEnc (true::bs),rep ones (n+1)++[false,false,true]++R⟩ =
        some ⟨1,headEnc bs,rep ones (n+1+1)++[false,false,true]++R⟩ := by
        simpa only [rep,List.append_assoc] using h1
      exact ⟨2+t,N,tail,by omega,by omega,join0 h1' h⟩

theorem right_one (L R : List Bool) :
  run0 table 4 ⟨1,[false]++L,[true]++b4++R⟩ =
    some ⟨1,[false]++b4++L,[true]++R⟩ := by rfl

theorem right_all (k : Nat) (L : List Bool) :
  run0 table (4*k) ⟨1,[false]++L,[true]++rep b4 k⟩ =
    some ⟨1,[false]++rep b4 k++L,[true]⟩ := by
  simpa only [List.append_nil] using sweepR table 1 [false] [true] b4 b4 4 right_one k L []

theorem exit3 (L : List Bool) :
  run0 table 3 ⟨1,false::L,[true]⟩ = some ⟨1,[false,true,false,true]++L,[]⟩ := by rfl

theorem enc_rep (N : Nat) (ds : List Bool) :
  enc (List.replicate N false ++ true::ds) = rep zeros N ++ [false,true] ++ enc ds := by
  induction N with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.cons_append,enc,rep,zeros,ih,List.append_assoc]; rfl

theorem suffix (N : Nat) (ds : List Bool) :
  [true]++rep zeros (N+1)++[true]++enc ds = [true,false]++enc (List.replicate N false ++ true::ds) := by
  rw [enc_rep]
  simp only [rep,zeros,List.cons_append,List.nil_append,List.append_assoc]
  have hz := congrArg (fun x : List Bool => x ++ true::enc ds) (zeros_comm N)
  simp only [zeros,List.cons_append,List.append_assoc,List.nil_append] at hz
  rw [hz]

theorem recur (k : Nat) (ds : List Bool) : ∃ t k' ds', 0<t ∧ run0 table t (family k ds)=some (family k' ds') := by
  let R := rep b4 (k+1)
  have h1 := enter (rep b4 k++[true,false]++enc ds)
  have h2 := left_all k ([true,false]++enc ds)
  have h3 := prep ds (rep b4 k)
  simp only [List.append_assoc] at h1 h2 h3
  have h12 := join0 h1 h2
  have h123 := join0 h12 h3
  have hp : run0 table (7+16*k+18) (family k ds) =
      some ⟨1,headEnc ds,rep ones (0+1)++[false,false,true]++R⟩ := by
    simpa only [family,R,rep,List.append_assoc,List.append_nil] using h123
  obtain ⟨t,N,tail,_,ht,hc⟩ := carry ds 0 R
  have h4 := right_all (k+1) ([true]++rep zeros (N+1)++[true]++enc tail)
  have h5 := exit3 (rep b4 (k+1)++[true]++rep zeros (N+1)++[true]++enc tail)
  simp only [List.append_assoc,List.cons_append,List.nil_append] at h4 h5 hc hp
  have hh := join0 (join0 (join0 hp hc) h4) h5
  refine ⟨7+16*k+18+t+4*(k+1)+3,k+1,List.replicate N false++true::tail,by omega,?_⟩
  unfold family
  simp only [List.append_assoc]
  rw [← suffix N tail]
  simpa only [family,List.append_assoc,List.cons_append,List.nil_append] using hh

/-- Recurrent set, with no prescribed next counter value or cost. -/
theorem never_of_recurrent (p : PartialMachine) (I : Z0 → Prop) (entryTime : Nat) (first : Z0)
    (hfirst : run0 p entryTime ⟨0,[],[]⟩ = some first) (hI : I first)
    (hstep : ∀ z, I z → ∃ t z', 0<t ∧ run0 p t z = some z' ∧ I z')
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have arbitrary : ∀ k, ∃ t z, k≤t ∧ run0 p t ⟨0,[],[]⟩ = some z ∧ I z := by
    intro k
    induction k with
    | zero => exact ⟨entryTime,first,by omega,hfirst,hI⟩
    | succ k ih =>
      obtain ⟨t,z,ht,hr,hi⟩ := ih
      obtain ⟨u,z',hu,hru,hi'⟩ := hstep z hi
      exact ⟨t+u,z',by omega,join0 hr hru,hi'⟩
  intro n
  obtain ⟨t,z,ht,hr,_⟩ := arbitrary n
  have hz : (zrun p t start).map project = some z := (run_project p t start).trans hr
  cases h : zrun p t start with
  | none => simp [h] at hz
  | some z' =>
    have H := zrun_sound p m hm t start z' h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply never_of_recurrent table (fun z => ∃ k ds, z = family k ds) 17 (family 0 [true]) entry ⟨0,[true],rfl⟩ _ m hm
  intro z hz
  obtain ⟨k,ds,rfl⟩ := hz
  obtain ⟨t,k',ds',ht,hr⟩ := recur k ds
  exact ⟨t,family k' ds',ht,hr,k',ds',rfl⟩

#print axioms recur
#print axioms never_of_recurrent
#print axioms never
end BB6Coverage.Agent31Pump.Raw122Counter3708
