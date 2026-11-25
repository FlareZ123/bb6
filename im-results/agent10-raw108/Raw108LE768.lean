import SweepPumping

namespace BB6.Agent10Raw108LE768
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact paired-bit counter with an arbitrary finite stack of paired digits.
    The A1 hole is unreachable in every compatible completion. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev C (L R : List Bool) : Z0 := ⟨2,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
abbrev Q : List Bool := [true,true]
abbrev Z : List Bool := [false,false]
abbrev T : List Bool := [true,true,true,true,true,true,true]
def enc : List Bool → List Bool
  | [] => []
  | b::bs => b::b::enc bs
def data (ds : Option (List Bool)) : List Bool := ds.getD []
def left : Option (List Bool) → List Bool
  | none => []
  | some bs => false::enc bs
def right (j : Nat) : List Bool := false::(rep Q j ++ false::T)

structure Section where
  j : Nat
  ds : Option (List Bool)

def cfg (s : Section) : Z0 := A (left s.ds) (right s.j)

theorem base (L : List Bool) :
    run0 table 7 (A (false::L) (right 0)) =
      some (F (Q++L) (false::T)) := by rfl

theorem baseBlank : run0 table 7 (A [] (right 0)) =
    some (F Q (false::T)) := by rfl

theorem start (R L : List Bool) :
    run0 table 2 (A (false::L) (false::true::R)) =
      some (C (true::Q++L) R) := by rfl

theorem startBlank (R : List Bool) :
    run0 table 2 (A [] (false::true::R)) =
      some (C (true::Q) R) := by rfl

theorem scanPair (L R : List Bool) :
    run0 table 2 (C (true::L) (Q++R)) =
      some (C (true::Z++L) R) := by rfl

theorem tailPair (L : List Bool) :
    run0 table 7 (C (true::L) (true::false::T)) =
      some (F (Z++L) (false::T)) := by rfl

theorem pairSweep (j : Nat) (L : List Bool) :
    run0 table (2*j+7) (C (true::L) (rep Q j++true::false::T)) =
      some (F (rep Z (j+1)++L) (false::T)) := by
  have h := sweepR table 2 [true] [] Q Z 2 scanPair j L (true::false::T)
  have h' : run0 table (2*j) (C (true::L) (rep Q j++true::false::T)) =
      some (C (true::(rep Z j++L)) (true::false::T)) := by
    simpa only [List.nil_append,List.append_nil,List.append_assoc,List.cons_append,C] using h
  have H := join0 h' (tailPair (rep Z j++L))
  simpa only [rep,List.append_assoc] using H

theorem toF (j : Nat) (ds : Option (List Bool)) :
    run0 table (7+2*j) (cfg ⟨j,ds⟩) =
      some (F (rep Z j++Q++enc (data ds)) (false::T)) := by
  cases j with
  | zero =>
    cases ds with
    | none => exact baseBlank
    | some bs => exact base (enc bs)
  | succ j =>
    have eqR : right (j+1) = false::true::(rep Q j++true::false::T) := by
      have rot : ∀ (k : Nat) (R : List Bool), rep Q k++true::R = true::(rep Q k++R) := by
        intro k R
        induction k with
        | zero => rfl
        | succ k ih => simp only [rep,Q,List.cons_append,List.nil_append,ih]
      simp only [right,rep,Q,List.cons_append,List.nil_append,rot]
    have h : run0 table 2 (cfg ⟨j+1,ds⟩) =
        some (C (true::Q++enc (data ds)) (rep Q j++true::false::T)) := by
      cases ds with
      | none =>
        simpa only [cfg,left,data,Option.getD,enc,List.append_nil,eqR] using startBlank (rep Q j++true::false::T)
      | some bs =>
        simpa only [cfg,left,data,Option.getD,eqR] using start (rep Q j++true::false::T) (enc bs)
    have H := join0 h (pairSweep j (Q++enc (data ds)))
    rw [show 2+(2*j+7)=7+2*(j+1) by omega] at H
    simpa only [List.append_assoc] using H

theorem finishZero (L R : List Bool) :
    run0 table 1 (F (false::L) R) = some (A L (false::R)) := by rfl
theorem finishBlank (R : List Bool) :
    run0 table 1 (F [] R) = some (A [] (false::R)) := by rfl
theorem drainPair (L R : List Bool) :
    run0 table 2 (F (Q++L) R) = some (F L (Q++R)) := by rfl

def drainNext (j : Nat) : List Bool → Section
  | [] => ⟨j,none⟩
  | false::bs => ⟨j,some bs⟩
  | true::bs => drainNext (j+1) bs

def drainCost : List Bool → Nat
  | [] => 1
  | false::_ => 1
  | true::bs => 2+drainCost bs

theorem drain (j : Nat) (bs : List Bool) :
    run0 table (drainCost bs) (F (enc bs) (rep Q j++false::T)) =
      some (cfg (drainNext j bs)) := by
  induction bs generalizing j with
  | nil => exact finishBlank _
  | cons b bs ih =>
    cases b with
    | false => exact finishZero (false::enc bs) _
    | true =>
      have h := drainPair (enc bs) (rep Q j++false::T)
      have H := join0 h (ih (j+1))
      simpa only [drainCost,enc,drainNext,rep,List.append_assoc,Q,List.cons_append,List.nil_append] using H

theorem encZeros (j : Nat) (bs : List Bool) :
    enc (List.replicate j false ++ bs) = rep Z j++enc bs := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [List.replicate_succ,List.cons_append,enc,rep,ih]; rfl

def next (s : Section) : Section :=
  match s.j with
  | 0 => drainNext 1 (data s.ds)
  | j+1 => ⟨0,some (List.replicate j false ++ true::data s.ds)⟩

def cost (s : Section) : Nat :=
  match s.j with
  | 0 => 9+drainCost (data s.ds)
  | j+1 => 8+2*(j+1)

theorem advance (s : Section) :
    run0 table (cost s) (cfg s) = some (cfg (next s)) := by
  rcases s with ⟨j,ds⟩
  cases j with
  | zero =>
    have h := toF 0 ds
    have h' := drainPair (enc (data ds)) (false::T)
    have H := join0 (join0 h h') (drain 1 (data ds))
    simpa only [next,cost,rep,List.nil_append,List.append_nil,List.append_assoc] using H
  | succ j =>
    have h := toF (j+1) ds
    have h' := finishZero (false::(rep Z j++Q++enc (data ds))) (false::T)
    have H := join0 h h'
    rw [show 7+2*(j+1)+1=8+2*(j+1) by omega] at H
    simpa only [cost,next,cfg,left,right,encZeros,enc,rep,List.nil_append,List.append_nil,List.append_assoc,Z,Q,List.cons_append] using H

def sections : Nat → Section
  | 0 => ⟨0,none⟩
  | n+1 => next (sections n)

def family (n : Nat) := cfg (sections n)
theorem entry : run0 table 26 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) :
    run0 table (cost (sections n)) (family n) = some (family (n+1)) :=
  advance (sections n)

theorem posCost (s : Section) : 0 < cost s := by
  rcases s with ⟨j,ds⟩
  cases j <;> simp [cost] <;> omega

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 26 (fun k => cost (sections k)) entry
    (fun k => posCost (sections k)) growth m hm

#print axioms toF
#print axioms advance
#print axioms growth
#print axioms never
end BB6.Agent10Raw108LE768
