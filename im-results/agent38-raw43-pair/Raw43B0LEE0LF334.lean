import SweepPumping
set_option maxHeartbeats 0
namespace BB6.Agent38Raw43B0LEE0LF334
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def enc : List Bool → List Bool
  | [] => [false,false,false,false,false,false,true]
  | b::bs => false::false::false::false::false::false::b::enc bs

def half : List Bool → List Bool
  | [] => [false,false,false,true]
  | b::bs => false::false::false::b::enc bs

def sect (ds : List Bool) : Z0 := ⟨2,[false],[true,false,false,true]++enc ds⟩

theorem repAdd (b : Bool) (a c : Nat) : List.replicate (a+c) b = List.replicate a b ++ List.replicate c b := by
  induction a with
  | zero => simp
  | succ a ih => rw [show a+1+c=(a+c)+1 by omega]; simp only [List.replicate_succ,ih,List.cons_append]

theorem enc_half (ds : List Bool) : enc ds = false::false::false::half ds := by cases ds <;> rfl

theorem enc_pre (n : Nat) (ds : List Bool) : enc (List.replicate n false ++ ds) = List.replicate (7*n) false ++ enc ds := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 7*(n+1)=7+7*n by omega]
    rw [repAdd false 7 (7*n)]
    change false::false::false::false::false::false::false::enc (List.replicate n false ++ ds) = _
    rw [ih]
    rfl

theorem sweep (k : Nat) (R : List Bool) : run0 table k ⟨0,List.replicate k true ++ [false,false],R⟩ =
    some ⟨0,[false,false],List.replicate k false ++ R⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h : run0 table 1 ⟨0,List.replicate (k+1) true ++ [false,false],R⟩ =
      some ⟨0,List.replicate k true ++ [false,false],false::R⟩ := rfl
    have hh := join0 h (ih (false::R))
    rw [show 1+k=k+1 by omega] at hh
    rw [repAdd false k 1]
    simpa [List.append_assoc] using hh

theorem ret (k : Nat) (R : List Bool) : run0 table (k+3+9) ⟨0,List.replicate (k+3) true++[false,false],R⟩ =
    some ⟨2,[false],[true,false,false,true]++List.replicate k false++R⟩ := by
  have h := sweep (k+3) R
  rw [show k+3=3+k by omega] at h
  rw [repAdd false 3 k] at h
  have g : run0 table 9 ⟨0,[false,false],false::false::false::(List.replicate k false++R)⟩ =
    some ⟨2,[false],[true,false,false,true]++List.replicate k false++R⟩ := rfl
  have hh := join0 h g
  rw [show 3+k=k+3 by omega] at hh
  exact hh

theorem carry (ds : List Bool) (n : Nat) : ∃ t ds', 0<t ∧
    run0 table t ⟨2,List.replicate (7*n+6) true++[false,false],half ds⟩ =
      some (sect (List.replicate n false++ds')) := by
  induction ds generalizing n with
  | nil =>
    have h : run0 table 28 ⟨2,List.replicate (7*n+6) true++[false,false],half []⟩ =
      some ⟨0,List.replicate (7*n+11+3) true++[false,false],[false,false,true]⟩ := by
      rw [show 7*n+6=6+7*n by omega,show 7*n+11+3=14+7*n by omega,repAdd,repAdd]
      rfl
    have g := ret (7*n+11) [false,false,true]
    refine ⟨28+(7*n+11+3+9),[false],by omega,?_⟩
    have hg := join0 h g
    simp only [sect,enc_pre,enc,List.append_assoc] at ⊢
    rw [repAdd false (7*n) 11] at hg
    simpa [List.append_assoc] using hg
  | cons b ds ih =>
    cases b with
    | false =>
      have h : run0 table 11 ⟨2,List.replicate (7*n+6) true++[false,false],half (false::ds)⟩ =
        some ⟨0,List.replicate (7*n+4+3) true++[false,false],false::false::true::enc ds⟩ := by
        rw [show 7*n+6=6+7*n by omega,show 7*n+4+3=7+7*n by omega,repAdd,repAdd];rfl
      have g := ret (7*n+4) (false::false::true::enc ds)
      refine ⟨11+(7*n+4+3+9),true::ds,by omega,?_⟩
      have hg := join0 h g
      simp only [sect,enc_pre,enc,List.append_assoc]
      rw [repAdd false (7*n) 4] at hg
      simpa [List.append_assoc] using hg
    | true =>
      have h : run0 table 17 ⟨2,List.replicate (7*n+6) true++[false,false],half (true::ds)⟩ =
        some ⟨2,List.replicate (7*(n+1)+6) true++[false,false],half ds⟩ := by
        rw [show 7*n+6=6+7*n by omega,show 7*(n+1)+6=13+7*n by omega,repAdd,repAdd]
        simp only [half]
        rw [enc_half ds]
        rfl
      obtain ⟨t,ds',ht,g⟩ := ih (n+1)
      refine ⟨17+t,false::ds',by omega,?_⟩
      have hh := join0 h g
      rw [repAdd false n 1] at hh
      simpa [List.append_assoc] using hh

theorem epoch (ds : List Bool) : ∃ t ds', 0<t ∧ run0 table t (sect ds) = some (sect ds') := by
  have h : run0 table 17 (sect ds) = some ⟨2,List.replicate 6 true++[false,false],half ds⟩ := by cases ds <;> rfl
  obtain ⟨t,ds',ht,g⟩ := carry ds 0
  exact ⟨17+t,ds',by omega,join0 h g⟩

theorem live_prefix (n : Nat) : ∃ t ds, n≤t ∧ run0 table t ⟨0,[],[]⟩ = some (sect ds) := by
  induction n with
  | zero => exact ⟨53,[],by decide,rfl⟩
  | succ n ih =>
    obtain ⟨t,ds,ht,h⟩ := ih
    obtain ⟨u,ds',hu,g⟩ := epoch ds
    exact ⟨t+u,ds',by omega,join0 h g⟩

open BB6Coverage.Agent50Zipper

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,ds,ht,hr⟩ := live_prefix n
  have hz : (zrun table t start).map project = some (sect ds) := (run_project table t start).trans hr
  cases h : zrun table t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound table m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms never
end BB6.Agent38Raw43B0LEE0LF334
