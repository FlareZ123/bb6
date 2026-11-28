import Q0151SourceMacro

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent5Q0151SourceMacro
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent13PackedZipper
open BB6.Agent5PackedSweep

inductive Scan : List Bool → Prop where
  | nil : Scan []
  | one : Scan xs → Scan (true::xs)
  | pair : Scan xs → Scan (false::true::xs)

theorem Scan.append {xs ys : List Bool} (hx : Scan xs) (hy : Scan ys) : Scan (xs++ys) := by
  induction hx with
  | nil => exact hy
  | one _ ih => exact .one ih
  | pair _ ih => exact .pair ih

theorem scanAlt (n : Nat) : Scan (revAlt n) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .pair ih

theorem scanOnes (n : Nat) : Scan (ones n) := by
  induction n with
  | zero => exact .nil
  | succ n ih => exact .one ih

def scanCost : List Bool → Nat
  | [] => 0
  | true::xs => 5+scanCost xs
  | false::true::xs => 2+scanCost xs
  | false::xs => 0

theorem scan1 (x : Bool) (L R : List Bool) :
    run0 p 5 ⟨2,true::x::L,[true,false]++R⟩ =
      some ⟨2,x::L,[true,false,true]++R⟩ := by
  have h : Auto.knownRun p 5 ⟨2,[true,x],[true,false]⟩ = some ⟨2,[x],[true,false,true]⟩ := by
    cases x <;> decide +kernel
  simpa [Auto.extend] using Auto.knownRun_sound p 5 h L R

theorem scan2 (x : Bool) (L R : List Bool) :
    run0 p 2 ⟨2,false::true::x::L,[true,false]++R⟩ =
      some ⟨2,x::L,[true,false,true,false]++R⟩ := by
  have h : Auto.knownRun p 2 ⟨2,[false,true,x],[true,false]⟩ = some ⟨2,[x],[true,false,true,false]⟩ := by
    cases x <;> decide +kernel
  simpa [Auto.extend] using Auto.knownRun_sound p 2 h L R

theorem scanRun (S : List Bool) (hs : Scan S) (x : Bool) (L R : List Bool) :
    run0 p (scanCost S) ⟨2,S++x::L,[true,false]++R⟩ =
      some ⟨2,x::L,[true,false]++S.reverse++R⟩ := by
  induction hs generalizing R with
  | nil => rfl
  | @one xs hx ih =>
    have h1 : run0 p 5 ⟨2,true::(xs++x::L),[true,false]++R⟩ =
      some ⟨2,xs++x::L,[true,false]++true::R⟩ := by
      cases xs with
      | nil => exact scan1 x L R
      | cons y ys => exact scan1 y (ys++x::L) R
    have h := join0 h1 (ih (true::R))
    simpa [scanCost,List.reverse_cons,List.append_assoc] using h
  | @pair xs hx ih =>
    have h1 : run0 p 2 ⟨2,false::true::(xs++x::L),[true,false]++R⟩ =
      some ⟨2,xs++x::L,[true,false]++[true,false]++R⟩ := by
      cases xs with
      | nil => exact scan2 x L R
      | cons y ys => exact scan2 y (ys++x::L) R
    have h := join0 h1 (by simpa [List.append_assoc] using ih ([true,false]++R))
    simpa [scanCost,List.reverse_cons,List.append_assoc] using h

theorem pop (L R : List Bool) :
    runP p 5 (encode0 ⟨2,[false,false]++L,[true,false]++R⟩) =
      some (frame 1 ([true,true,true,true]++L) R) := by
  have h (x : Bool) : Auto.knownRun p 5 ⟨2,[false,false],[true,false,x]⟩ =
      some ⟨1,[x,true,true,true,true],[]⟩ := by cases x <;> decide +kernel
  cases R with
  | nil =>
    have hh := knownPacked 5 (h false) L []
    have he : encode0 ⟨2,[false,false]++L,[true,false,false]⟩ = encode0 ⟨2,[false,false]++L,[true,false]⟩ := rfl
    change runP p 5 (encode0 ⟨2,[false,false]++L,[true,false,false]⟩) =
        some (frame 1 ([true,true,true,true]++L) [false]) at hh
    rw [he] at hh
    exact hh
  | cons x xs => simpa [Auto.extend,frame] using knownPacked 5 (h x) L xs

theorem retreat (S L R : List Bool) (hs : Scan S) :
    Goes (encode0 ⟨2,S++[false,false]++L,[true,false]++R⟩)
      (frame 1 ([true,true,true,true]++L) (S.reverse++R)) := by
  have h := scanRun S hs false (false::L) R
  have h1 : runP p (scanCost S) (encode0 ⟨2,S++[false,false]++L,[true,false]++R⟩) =
      some (encode0 ⟨2,[false,false]++L,[true,false]++(S.reverse++R)⟩) := by
    have hm := congrArg (Option.map encode0) h
    rw [encode0_run] at hm
    simpa only [List.cons_append,List.nil_append,List.append_assoc,Option.map_some] using hm
  exact ⟨scanCost S+5,by omega,joinP h1 (pop L (S.reverse++R))⟩

theorem bBlank (L : List Bool) : runP p 3 (frame 1 L []) = some (encode0 ⟨2,L,[true,false]⟩) := by
  have h (x : Bool) : Auto.knownRun p 3 ⟨1,[false,x],[false]⟩ = some ⟨2,[x],[true,false]⟩ := by
    cases x <;> decide +kernel
  cases L with
  | nil => simpa [Auto.extend,frame,encode0,pack] using knownPacked 3 (h false) [] []
  | cons x xs =>
    have hh := knownPacked 3 (h x) xs []
    simpa [Auto.extend,frame,encode0,pack] using hh

theorem cBlank (L : List Bool) : runP p 2 (frame 2 (true::L) []) = some (encode0 ⟨2,L,[true,false]⟩) := by
  have h (x : Bool) : Auto.knownRun p 2 ⟨2,[false,true,x],[]⟩ = some ⟨2,[x],[true,false]⟩ := by
    cases x <;> decide +kernel
  cases L with
  | nil => simpa [Auto.extend,frame,encode0,pack] using knownPacked 2 (h false) [] []
  | cons x xs => simpa [Auto.extend,frame] using knownPacked 2 (h x) xs []

theorem eTurn (L R : List Bool) : runP p 3 (frame 4 ([false,true]++L) (false::R)) =
    some (encode0 ⟨2,L,[true,false,true]++R⟩) := by
  have h (x : Bool) : Auto.knownRun p 3 ⟨4,[false,false,true,x],[]⟩ =
      some ⟨2,[x],[true,false,true]⟩ := by cases x <;> decide +kernel
  cases L with
  | nil => simpa [Auto.extend,frame,encode0,pack] using knownPacked 3 (h false) [] R
  | cons x xs => simpa [Auto.extend,frame] using knownPacked 3 (h x) xs R

theorem repairOne (L R : List Bool) : runP p 6 (frame 4 ([false,false]++L) ([false,true]++R)) =
    some (frame 4 ([false,true,true,true]++L) R) := by
  have h (x : Bool) : Auto.knownRun p 6 ⟨4,[false,false,false],[true,x]⟩ =
      some ⟨4,[x,false,true,true,true],[]⟩ := by cases x <;> decide +kernel
  cases R with
  | nil => simpa [Auto.extend,frame,encode0,pack] using knownPacked 6 (h false) L []
  | cons x xs => simpa [Auto.extend,frame] using knownPacked 6 (h x) L xs

theorem repairEmpty (L : List Bool) : runP p 6 (frame 4 ([false,false]++L) []) =
    some (frame 1 ([true,true,true,true]++L) []) := by
  have h : Auto.knownRun p 6 ⟨4,[false,false,false],[false,false]⟩ =
      some ⟨1,[false,true,true,true,true],[]⟩ := by decide +kernel
  simpa [Auto.extend,frame,encode0,pack] using knownPacked 6 h L []

#print axioms retreat
#print axioms repairOne
#print axioms repairEmpty
end BB6.Agent5Q0151SourceMacro
