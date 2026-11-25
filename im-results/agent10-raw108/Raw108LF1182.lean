import SweepPumping

namespace BB6.Agent10Raw108LF1182
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact binary countdown sections, including overflow, for raw108/1LF leaf 1182. -/
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,false,1⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

abbrev A (L R : List Bool) : Z0 := ⟨0,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
abbrev P : List Bool := [false,true]
abbrev Q : List Bool := [true,true]
abbrev Z : List Bool := [true,false]
abbrev S : List Bool := [true,true,true,false]

theorem scanZero (L R : List Bool) :
    run0 table 4 (A (P++L) (Z++R)) = some (A (P++P++L) R) := by rfl

theorem scanOne (L R : List Bool) :
    run0 table 4 (A (P++L) (Q++R)) = some (A (Q++P++L) R) := by rfl

theorem scanEnd (L : List Bool) :
    run0 table 4 (A (P++L) [true]) = some (A (P++P++L) []) := by rfl

theorem overflow (L : List Bool) :
    run0 table 10 (A (P++L) []) = some (A (Q++P++L) [true]) := by rfl

theorem startReturn (L R : List Bool) :
    run0 table 2 (A (Q++L) R) = some (F L (Z++R)) := by rfl

theorem pairReturn (L R : List Bool) :
    run0 table 2 (F (P++L) R) = some (F L (Q++R)) := by rfl

theorem reset (R : List Bool) :
    run0 table 20 (F S (Q++R)) = some (A (P++S) R) := by rfl

theorem returnAll (j : Nat) (R : List Bool) :
    run0 table (24+2*j) (A (Q++rep P (j+1)++S) R) =
      some (A (P++S) (rep Q j++Z++R)) := by
  have h := startReturn (rep P (j+1)++S) R
  have hd := sweepL table 5 [] [] P Q 2 pairReturn (j+1) S (Z++R)
  have hd' : run0 table (2*(j+1)) (F (rep P (j+1)++S) (Z++R)) =
      some (F S (Q++(rep Q j++Z++R))) := by
    simpa only [List.nil_append,List.append_nil,rep,List.append_assoc] using hd
  have H := join0 (join0 h hd') (reset (rep Q j++Z++R))
  rw [show 2+2*(j+1)+20=24+2*j by omega] at H
  simpa only [List.append_assoc] using H

def enc : List Bool → List Bool
  | [] => [true]
  | b::bs => true::b::enc bs

theorem repeatOnes (j : Nat) (bs : List Bool) :
    enc (List.replicate j true ++ bs) = rep Q j ++ enc bs := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [List.replicate_succ,List.cons_append,enc,rep,ih]
    rfl

inductive Section where
  | scan (j : Nat) (bs : List Bool)
  | edge (j : Nat)

def cfg : Section → Z0
  | .scan j bs => A (rep P (j+1)++S) (enc bs)
  | .edge j => A (rep P (j+1)++S) []

def next : Section → Section
  | .scan j [] => .edge (j+1)
  | .scan j (false::bs) => .scan (j+1) bs
  | .scan j (true::bs) => .scan 0 (List.replicate j true ++ false::bs)
  | .edge j => .scan 0 (List.replicate j true ++ [false])

def cost : Section → Nat
  | .scan _ [] => 4
  | .scan _ (false::_) => 4
  | .scan j (true::_) => 28+2*j
  | .edge j => 34+2*j

theorem advance (s : Section) :
    run0 table (cost s) (cfg s) = some (cfg (next s)) := by
  cases s with
  | scan j bs =>
    cases bs with
    | nil =>
      simpa only [cost,cfg,next,enc,rep,List.append_assoc] using scanEnd (rep P j++S)
    | cons b bs =>
      cases b with
      | false =>
        simpa only [cost,cfg,next,enc,rep,List.append_assoc,List.cons_append,List.nil_append,P,Z] using scanZero (rep P j++S) (enc bs)
      | true =>
        have h := scanOne (rep P j++S) (enc bs)
        have h' : run0 table 4 (cfg (.scan j (true::bs))) =
            some (A (Q++rep P (j+1)++S) (enc bs)) := by
          simpa only [cfg,enc,rep,List.append_assoc,List.cons_append,List.nil_append,P,Q] using h
        have H := join0 h' (returnAll j (enc bs))
        rw [show 4+(24+2*j)=28+2*j by omega] at H
        simpa only [cost,cfg,next,repeatOnes,enc,rep,List.nil_append,List.append_nil,List.append_assoc,List.cons_append,Z] using H
  | edge j =>
    have h := overflow (rep P j++S)
    have h' : run0 table 10 (cfg (.edge j)) =
        some (A (Q++rep P (j+1)++S) [true]) := by
      simpa only [cfg,rep,List.append_assoc] using h
    have H := join0 h' (returnAll j [true])
    rw [show 10+(24+2*j)=34+2*j by omega] at H
    simpa only [cost,cfg,next,repeatOnes,enc,rep,List.nil_append,List.append_nil,List.append_assoc,List.cons_append,Z] using H

def sections : Nat → Section
  | 0 => .edge 0
  | n+1 => next (sections n)

def family (n : Nat) : Z0 := cfg (sections n)

theorem entry : run0 table 22 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem growth (n : Nat) :
    run0 table (cost (sections n)) (family n) = some (family (n+1)) :=
  advance (sections n)

theorem posCost (s : Section) : 0 < cost s := by
  cases s with
  | scan j bs => cases bs with
    | nil => simp [cost]
    | cons b bs => cases b <;> simp [cost] <;> omega
  | edge j => simp [cost] <;> omega

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 22 (fun k => cost (sections k)) entry
    (fun k => posCost (sections k)) growth m hm

#print axioms never
#print axioms returnAll
#print axioms advance
#print axioms growth
end BB6.Agent10Raw108LF1182
