import SweepPumping
set_option maxHeartbeats 0
namespace BB6.Agent38Raw43B0LEE0LC15
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun (q,b) =>
  match q.val,b with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨false,false,2⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def enc : List Bool → List Bool
  | [] => [true]
  | b::bs => true::b::false::enc bs

def scan (q : Fin 6) (L W : List Bool) : Z0 := ⟨q,W.headD false::L,W.tail⟩
def dsStart (L ds : List Bool) := scan 3 (false::L) (enc ds)
def sect (L ds : List Bool) : Z0 := ⟨0,false::L,false::false::enc ds⟩

theorem rewind (L R : List Bool) :
    run0 table 7 ⟨3,false::true::false::L,true::R⟩ = some ⟨3,L,true::true::false::true::R⟩ := by rfl

/-- Decrement the finite little-endian right word; a borrow beyond the
    terminator extends the word. The left frame is restored exactly. -/
theorem carry (ds L : List Bool) : ∃ t ds', 0<t ∧
    run0 table t (dsStart L ds) = some ⟨3,false::L,enc ds'⟩ := by
  induction ds generalizing L with
  | nil => exact ⟨11,[true],by decide,rfl⟩
  | cons b ds ih =>
    cases b with
    | true => cases ds <;> exact ⟨5,false::_,by decide,rfl⟩
    | false =>
      have h1 : run0 table 3 (dsStart L (false::ds)) = some (dsStart (true::false::false::L) ds) := by
        cases ds <;> rfl
      obtain ⟨t,ds',ht,h2⟩ := ih (true::false::false::L)
      have h3 : run0 table 7 ⟨3,false::true::false::false::L,enc ds'⟩ = some ⟨3,false::L,enc (true::ds')⟩ := by
        cases ds' <;> rfl
      exact ⟨3+t+7,true::ds',by omega,join0 (join0 h1 h2) h3⟩

def ones (n : Nat) : List Bool := List.replicate n true

theorem a_scan (n : Nat) (L R : List Bool) : ∃ L',
    run0 table n (scan 0 L (ones n ++ false::false::false::R)) = some ⟨0,false::L',false::false::R⟩ := by
  induction n generalizing L with
  | zero => exact ⟨L,rfl⟩
  | succ n ih =>
    obtain ⟨L',h⟩ := ih (false::L)
    have h1 : run0 table 1 (scan 0 L (ones (n+1) ++ false::false::false::R)) = some (scan 0 (false::L) (ones n ++ false::false::false::R)) := by rfl
    exact ⟨L',by simpa only [Nat.add_comm 1 n] using join0 h1 h⟩

/-- Increment the left binary word with its implicit zero extension. -/
theorem f_return (L : List Bool) (n : Nat) (R : List Bool) : ∃ t L', 0<t ∧
    run0 table t ⟨5,L,ones n ++ false::false::false::R⟩ = some ⟨0,false::L',false::false::R⟩ := by
  induction L generalizing n with
  | nil =>
    obtain ⟨L',h⟩ := a_scan n [true] R
    have h1 : run0 table 1 ⟨5,[],ones n ++ false::false::false::R⟩ = some (scan 0 [true] (ones n ++ false::false::false::R)) := by rfl
    exact ⟨1+n,L',by omega,join0 h1 h⟩
  | cons b L ih =>
    cases b with
    | false =>
      obtain ⟨L',h⟩ := a_scan n (true::L) R
      have h1 : run0 table 1 ⟨5,false::L,ones n ++ false::false::false::R⟩ = some (scan 0 (true::L) (ones n ++ false::false::false::R)) := by rfl
      exact ⟨1+n,L',by omega,join0 h1 h⟩
    | true =>
      obtain ⟨t,L',ht,h⟩ := ih (n+1)
      have h1 : run0 table 1 ⟨5,true::L,ones n ++ false::false::false::R⟩ = some ⟨5,L,ones (n+1) ++ false::false::false::R⟩ := by rfl
      exact ⟨1+t,L',by omega,join0 h1 h⟩

theorem epoch (L ds : List Bool) : ∃ t L' ds', 0<t ∧ run0 table t (sect L ds) = some (sect L' ds') := by
  have h1 : run0 table 3 (sect L ds) = some (dsStart (true::true::L) ds) := by cases ds <;> rfl
  obtain ⟨t,ds',ht,h2⟩ := carry ds (true::true::L)
  have h3 : run0 table 5 ⟨3,false::true::true::L,enc ds'⟩ = some ⟨5,L,false::false::false::enc ds'⟩ := by cases ds' <;> rfl
  obtain ⟨u,L',hu,h4⟩ := f_return L 0 (enc ds')
  exact ⟨3+t+5+u,L',ds',by omega,join0 (join0 (join0 h1 h2) h3) h4⟩

theorem live_prefix (n : Nat) : ∃ t L ds, n≤t ∧ run0 table t ⟨0,[],[]⟩ = some (sect L ds) := by
  induction n with
  | zero => exact ⟨10,[true],[],by decide,rfl⟩
  | succ n ih =>
    obtain ⟨t,L,ds,ht,h⟩ := ih
    obtain ⟨u,L',ds',hu,h'⟩ := epoch L ds
    exact ⟨t+u,L',ds',by omega,join0 h h'⟩

open BB6Coverage.Agent50Zipper

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,L,ds,ht,hr⟩ := live_prefix n
  have hz : (zrun table t start).map project = some (sect L ds) :=
    (run_project table t start).trans hr
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
end BB6.Agent38Raw43B0LEE0LC15
