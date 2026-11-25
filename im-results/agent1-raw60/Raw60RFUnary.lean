import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw60RFUnary
open BB6Coverage BB6Coverage.Agent31Pump
inductive V | a390 | a498 | a502 deriving DecidableEq

def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some (match v with | .a390 => ⟨false,false,0⟩ | _ => ⟨true,false,1⟩))
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some (match v with | .a498 => ⟨false,true,1⟩ | _ => ⟨true,true,2⟩))
  | _,_ => none
abbrev B (L R : List Bool) : Z0 := ⟨1,L,R⟩
abbrev C (L R : List Bool) : Z0 := ⟨2,L,R⟩
abbrev F (L R : List Bool) : Z0 := ⟨5,L,R⟩
abbrev U (n : Nat) := List.replicate n true

def off (v : V) : Nat := match v with | .a390 => 1 | _ => 0
def startCost (v : V) (k : Nat) : Nat := match v with | .a390 => 3*k+4 | _ => k+2
def cycleCost (v : V) : Nat := match v with | .a498 => 7 | _ => 5

theorem repU (k n : Nat) : rep (U k) n = U (k*n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,ih,Nat.mul_succ,List.replicate_append_replicate]; rw [Nat.add_comm k]

theorem left390 (L R : List Bool) :
    run0 (table .a390) 3 (F (false::true::true::L) R) = some (F (false::true::L) (true::R)) := by rfl

theorem leftB (v : V) (h : v ≠ .a390) (L R : List Bool) :
    run0 (table v) 1 (B (true::L) R) = some (B L (true::R)) := by cases v <;> first | contradiction | rfl

theorem start390 (k : Nat) :
    run0 (table .a390) (3*k+4) (F (false::U (k+1)) []) = some (C (U 3) (U k)) := by
  have h1 := sweepL (table .a390) 5 [false,true] [] [true] [true] 3 left390 k [] []
  simp only [List.append_nil,List.nil_append,show [true] = U 1 by rfl,repU,Nat.one_mul] at h1
  have h2 : run0 (table .a390) 4 (F [false,true] (U k)) = some (C (U 3) (U k)) := by rfl
  exact join0 h1 h2

theorem startOther (v : V) (hv : v ≠ .a390) (k : Nat) :
    run0 (table v) (k+2) (F (false::U k) []) = some (C (U 2) (U k)) := by
  have h1 : run0 (table v) 1 (F (false::U k) []) = some (B (U k) [true]) := by cases v <;> rfl
  have h2 := sweepL (table v) 1 [] [] [true] [true] 1 (leftB v hv) k [] [true]
  simp only [List.append_nil,List.nil_append,show [true] = U 1 by rfl,repU,Nat.one_mul] at h2
  have hh : U k ++ U 1 = U (k+1) := List.replicate_append_replicate
  rw [hh] at h2
  have h3 : run0 (table v) 1 (B [] (U (k+1))) = some (C (U 2) (U k)) := by cases v <;> rfl
  have H := join0 (join0 h1 h2) h3
  rw [show 1+k+1=k+2 by omega] at H
  exact H

theorem startC (v : V) (k : Nat) :
    run0 (table v) (startCost v k) (F (false::U (k+off v)) []) = some (C (U (2+off v)) (U k)) := by
  cases v with
  | a390 => exact start390 k
  | a498 => exact startOther .a498 (by decide) k
  | a502 => exact startOther .a502 (by decide) k

theorem oneC (v : V) (L R : List Bool) :
    run0 (table v) (cycleCost v) (C (true::L) (U 5++R)) = some (C (true::(U 5++L)) R) := by cases v <;> rfl

theorem sweepC (v : V) (n r : Nat) :
    run0 (table v) (cycleCost v*n) (C (U (2+off v)) (U (5*n+r))) = some (C (U (5*n+2+off v)) (U r)) := by
  have H := sweepR (table v) 2 [true] [] (U 5) (U 5) (cycleCost v) (oneC v) n (U (1+off v)) (U r)
  simp only [List.singleton_append,List.nil_append,repU,List.replicate_append_replicate] at H
  have h : true::U (5*n+(1+off v)) = U (5*n+2+off v) := by
    rw [show 5*n+2+off v=5*n+(1+off v)+1 by omega]; rfl
  have ha : U (5*n) ++ U (1+off v) = U (5*n+(1+off v)) := List.replicate_append_replicate
  rw [List.cons_append,ha,h] at H
  have hb : true::U (1+off v) = U (2+off v) := by rw [show 2+off v=1+off v+1 by omega]; rfl
  rw [hb] at H
  exact H

inductive Remainder | zero | two | three
def rem : Remainder → Nat | .zero => 0 | .two => 2 | .three => 3
def gain : Remainder → Nat | .zero => 5 | .two => 6 | .three => 3
def endCost : Remainder → Nat | .zero => 12 | .two => 11 | .three => 4

theorem terminal (v : V) (r : Remainder) (L : List Bool) :
    run0 (table v) (endCost r) (C (true::L) (U (rem r))) = some (F (false::(U (gain r+1)++L)) []) := by cases v <;> cases r <;> rfl

def epochCost (v : V) (n : Nat) (r : Remainder) := startCost v (5*n+rem r)+cycleCost v*n+endCost r

theorem epoch (v : V) (n : Nat) (r : Remainder) :
    run0 (table v) (epochCost v n r) (F (false::U (5*n+rem r+off v)) []) =
      some (F (false::U (5*n+2+off v+gain r)) []) := by
  have h1 := startC v (5*n+rem r)
  have h2 := sweepC v n (rem r)
  have h3 := terminal v r (U (5*n+1+off v))
  have he : true::U (5*n+1+off v) = U (5*n+2+off v) := by rw [show 5*n+2+off v=5*n+1+off v+1 by omega]; rfl
  rw [he,List.replicate_append_replicate,show gain r+1+(5*n+1+off v)=5*n+2+off v+gain r by omega] at h3
  exact join0 (join0 h1 h2) h3

def base (v : V) : Nat := match v with | .a390 => 1 | _ => 2
def entryTime (v : V) : Nat := match v with | .a390 => 25 | .a498 => 35 | .a502 => 44
def family (v : V) (n : Nat) := F (false::U (5*(3*n+base v)+off v)) []
def cost (v : V) (n : Nat) := epochCost v (3*n+base v) .zero + epochCost v (3*n+base v+1) .two + epochCost v (3*n+base v+2) .three

theorem growth (v : V) (n : Nat) : run0 (table v) (cost v n) (family v n) = some (family v (n+1)) := by
  have h1 := epoch v (3*n+base v) .zero
  have h2 := epoch v (3*n+base v+1) .two
  have h3 := epoch v (3*n+base v+2) .three
  simp only [rem,gain,Nat.add_zero] at h1 h2 h3
  rw [show 5*(3*n+base v)+2+off v+5=5*(3*n+base v+1)+2+off v by omega] at h1
  rw [show 5*(3*n+base v+1)+2+off v+6=5*(3*n+base v+2)+3+off v by omega] at h2
  have H := join0 (join0 h1 h2) h3
  unfold family cost
  rw [show 5*(3*(n+1)+base v)+off v=5*(3*n+base v+2)+2+off v+3 by omega]
  exact H

theorem entry (v : V) : run0 (table v) (entryTime v) ⟨0,[],[]⟩ = some (family v 0) := by cases v <;> rfl
theorem positive (v : V) (n : Nat) : 0 < cost v n := by cases v <;> simp [cost,epochCost,startCost,cycleCost,endCost] <;> omega
theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := never_of_growth (table v) (family v) (entryTime v) (cost v) (entry v) (positive v) (growth v) m hm
namespace M390
abbrev table := _root_.BB6.Agent1Raw60RFUnary.table .a390
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RFUnary.never .a390 m hm
end M390
namespace M498
abbrev table := _root_.BB6.Agent1Raw60RFUnary.table .a498
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RFUnary.never .a498 m hm
end M498
namespace M502
abbrev table := _root_.BB6.Agent1Raw60RFUnary.table .a502
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := _root_.BB6.Agent1Raw60RFUnary.never .a502 m hm
end M502
#print axioms epoch
#print axioms growth
#print axioms never
end BB6.Agent1Raw60RFUnary
