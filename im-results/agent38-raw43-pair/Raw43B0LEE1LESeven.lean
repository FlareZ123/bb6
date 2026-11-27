import SweepPumping
set_option maxHeartbeats 0
namespace BB6.Agent38Raw43B0LEE1LESeven
open BB6Coverage BB6Coverage.Agent31Pump

inductive V where
  | m172 | m174 | m180 | m336 | m453 | m455 | m461

def table (v : V) : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => match v with
    | .m180 | .m461 => some (some ⟨true,false,5⟩)
    | .m336 => some (some ⟨false,true,5⟩)
    | _ => some (some ⟨false,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => match v with
    | .m336 => none
    | _ => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | 4,true => match v with
    | .m172 | .m174 | .m180 => some (some ⟨false,true,2⟩)
    | .m336 => some (some ⟨true,true,0⟩)
    | _ => some (some ⟨true,true,1⟩)
  | 5,false => match v with
    | .m336 => some (some ⟨false,false,1⟩)
    | _ => none
  | 5,true => match v with
    | .m172 | .m453 => some (some ⟨true,false,4⟩)
    | .m174 | .m455 => some (some ⟨true,true,3⟩)
    | .m180 | .m461 => some (some ⟨false,true,1⟩)
    | .m336 => some (some ⟨false,false,3⟩)
  | _,_ => none

def enc : List (Bool × Bool) → List Bool
  | [] => []
  | (a,c)::ds => a::false::c::enc ds

def rewindCost : V → Nat
  | .m174 | .m455 => 13
  | .m180 | .m461 => 11
  | _ => 9

def outCost (v : V) := rewindCost v + 1

theorem carry (v : V) (ds : List (Bool × Bool)) (L : List Bool) :
    ∃ t ds', 0<t ∧ run0 (table v) t ⟨3,true::false::true::L,enc ds⟩ =
      some ⟨4,true::L,true::true::enc ds'⟩ := by
  induction ds generalizing L with
  | nil => exact ⟨10,[(true,true)],by decide,by cases v <;> rfl⟩
  | cons d ds ih =>
    rcases d with ⟨a,c⟩
    cases a with
    | true => exact ⟨4,(false,c)::ds,by decide,by cases v <;> rfl⟩
    | false =>
      cases c with
      | false => exact ⟨10,(true,true)::ds,by decide,by cases v <;> rfl⟩
      | true =>
        have h1 : run0 (table v) 3 ⟨3,true::false::true::L,enc ((false,true)::ds)⟩ =
          some ⟨3,true::false::true::false::false::true::L,enc ds⟩ := by cases v <;> rfl
        obtain ⟨t,ds',ht,h2⟩ := ih (false::false::true::L)
        have h3 : run0 (table v) (rewindCost v)
            ⟨4,true::false::false::true::L,true::true::enc ds'⟩ =
          some ⟨4,true::L,true::true::enc ((true,false)::ds')⟩ := by cases v <;> rfl
        exact ⟨3+t+rewindCost v,(true,false)::ds',by omega,join0 (join0 h1 h2) h3⟩

def sect (b : Bool) (ds : List (Bool × Bool)) : Z0 :=
  ⟨1,[false,true],false::b::enc ds⟩

theorem epoch (v : V) (b : Bool) (ds : List (Bool × Bool)) :
    ∃ t b' ds', 0<t ∧ run0 (table v) t (sect b ds) = some (sect b' ds') := by
  cases b with
  | false => exact ⟨10,true,ds,by decide,by cases v <;> rfl⟩
  | true =>
    have h1 : run0 (table v) 2 (sect true ds) = some ⟨3,[true,false,true,true],enc ds⟩ := by cases v <;> rfl
    obtain ⟨t,ds',ht,h2⟩ := carry v ds [true]
    have h3 : run0 (table v) (outCost v) ⟨4,[true,true],true::true::enc ds'⟩ = some (sect false ds') := by cases v <;> rfl
    exact ⟨2+t+outCost v,false,ds',by omega,join0 (join0 h1 h2) h3⟩

theorem live_prefix (v : V) (n : Nat) :
    ∃ t b ds, n≤t ∧ run0 (table v) t ⟨0,[],[]⟩ = some (sect b ds) := by
  induction n with
  | zero => exact ⟨11,true,[],by decide,by cases v <;> rfl⟩
  | succ n ih =>
    obtain ⟨t,b,ds,ht,h⟩ := ih
    obtain ⟨u,b',ds',hu,h'⟩ := epoch v b ds
    exact ⟨t+u,b',ds',by omega,join0 h h'⟩

open BB6Coverage.Agent50Zipper

theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  intro n
  obtain ⟨t,b,ds,ht,hr⟩ := live_prefix v n
  have hz : (zrun (table v) t start).map project = some (sect b ds) :=
    (run_project (table v) t start).trans hr
  cases h : zrun (table v) t start with
  | none => simp [h] at hz
  | some z =>
    have H := zrun_sound (table v) m hm t start z h
    rw [start_embed] at H
    rw [show t=n+(t-n) by omega,run_append] at H
    cases he : run m n blank with
    | none => simp [he] at H
    | some c => rfl

#print axioms never
end BB6.Agent38Raw43B0LEE1LESeven
