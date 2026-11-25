import C1ZeroLAFour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent6C1ZeroLASweeps
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent6C1ZeroLAFour (h f z u rep_add z_add)

theorem rep_succ_right (P : List Bool) (n : Nat) : rep P (n+1)=rep P n++P := by
  have H := rep_add P n 1
  simpa only [rep,List.append_nil] using H

theorem forward {p : PartialMachine} {q : Fin 6} {A B P W : List Bool} {c : Nat}
    (macroStep : ∀ L R : List Bool, run0 p c ⟨q,A++L,B++W++R⟩ = some ⟨q,A++P++L,B++R⟩)
    (n : Nat) (L R : List Bool) :
    run0 p (c*n) ⟨q,A++L,B++rep W n++R⟩ = some ⟨q,A++rep P n++L,B++R⟩ := by
  induction n generalizing L with
  | zero => simp [rep,run0]
  | succ n ih =>
    have H := join0 (macroStep L (rep W n++R)) (by simpa only [List.append_assoc] using ih (P++L))
    rw [show c+c*n=c*(n+1) by rw [Nat.mul_succ,Nat.add_comm]] at H
    rw [rep_succ_right P]
    simpa only [rep,List.append_assoc] using H

theorem backward {p : PartialMachine} {q : Fin 6} {A B P W : List Bool} {c : Nat}
    (macroStep : ∀ L R : List Bool, run0 p c ⟨q,A++P++L,B++R⟩ = some ⟨q,A++L,B++W++R⟩)
    (n : Nat) (L R : List Bool) :
    run0 p (c*n) ⟨q,A++rep P n++L,B++R⟩ = some ⟨q,A++L,B++rep W n++R⟩ := by
  induction n generalizing R with
  | zero => simp [rep,run0]
  | succ n ih =>
    have H := join0 (macroStep (rep P n++L) R) (by simpa only [List.append_assoc] using ih (W++R))
    rw [show c+c*n=c*(n+1) by rw [Nat.mul_succ,Nat.add_comm]] at H
    rw [rep_succ_right W]
    simpa only [rep,List.append_assoc] using H

namespace Pair96
abbrev W : List Bool := [true,true,false,false,true]
abbrev P : List Bool := [false,true,true,true,true]
def ctr (b : Bool) := if b then FAR.fromCodes [7,23,11,1,14,0,3,16,12,11,7,24] else FAR.fromCodes [7,21,11,1,14,0,3,16,12,11,12,24]
def q (b : Bool) : Fin 6 := if b then 5 else 3
def A (b : Bool) : List Bool := if b then [false,true,true,true] else [false,true,true]
def B (b : Bool) : List Bool := if b then [] else f
def startCost (b : Bool) := if b then 9 else 10
def scanCost (b : Bool) := if b then 7 else 11
def turnCost (b : Bool) := if b then 6 else 7

theorem start (b : Bool) (R : List Bool) : run0 (ctr b) (startCost b) ⟨4,h,f++R⟩ = some ⟨q b,A b,B b++R⟩ := by cases b <;> rfl
theorem scan (b : Bool) (L R : List Bool) : run0 (ctr b) (scanCost b) ⟨q b,A b++L,B b++W++R⟩ = some ⟨q b,A b++P++L,B b++R⟩ := by cases b <;> rfl
theorem turn (b : Bool) (L : List Bool) : run0 (ctr b) (turnCost b) ⟨q b,A b++L,B b++h⟩ = some ⟨4,h++P++L,f++h⟩ := by cases b <;> rfl
theorem pop (b : Bool) (L R : List Bool) : run0 (ctr b) 11 ⟨4,h++P++L,f++R⟩ = some ⟨4,h++L,f++W++R⟩ := by cases b <;> rfl

def family (n : Nat) : Z0 := ⟨4,h,f++rep W (n+1)++h⟩
def cost (b : Bool) (n : Nat) := startCost b+scanCost b*(n+1)+turnCost b+11*(n+2)
theorem entry (b : Bool) : run0 (ctr b) (if b then 30 else 32) ⟨0,[],[]⟩ = some (family 0) := by cases b <;> rfl

theorem growth (b : Bool) (n : Nat) : run0 (ctr b) (cost b n) (family n) = some (family (n+1)) := by
  have H1 := start b (rep W (n+1)++h)
  have H2 := forward (scan b) (n+1) [] h
  have H3 := turn b (rep P (n+1))
  have H4 := backward (pop b) (n+2) [] h
  have H := join0 H1 (by simpa only [List.append_nil,List.append_assoc] using H2)
  have H := join0 H (by simpa only [List.append_assoc] using H3)
  have H := join0 H (by simpa only [rep,List.append_assoc,List.append_nil] using H4)
  exact H
open BB6.Agent13BlankDelay
theorem never (b : Bool) (m : Machine) (hm : compatible (ctr b) m) : NeverHalts m :=
  never_of_growth (ctr b) family (if b then 30 else 32) (cost b) (entry b)
    (fun n => by unfold cost; omega) (growth b) m hm
theorem cover (b : Bool) (B : Nat) : Cover (WeightedBound B) (ctr b) :=
  .leaf _ (fun m hm => weighted_never B m (never b m hm))
#print axioms entry
#print axioms growth
#print axioms never
#print axioms cover
end Pair96

namespace GroupD
inductive V | v107 | v108 | v110
open V
def ctr : V → PartialMachine
  | v107 => FAR.fromCodes [7,21,11,9,14,0,3,16,12,11,15,24]
  | v108 => FAR.fromCodes [7,21,11,11,14,0,3,16,12,11,15,24]
  | v110 => FAR.fromCodes [7,21,11,19,14,0,3,16,12,11,15,24]
def X : V → List Bool | v108 => [true,false,false] | _ => [true,true,false,false]
def W (v : V) := h++X v
def W' (v : V) := X v++h
def P : V → List Bool | v108 => [false,true,true,true] | _ => [false,true,true,true,true]
abbrev A : List Bool := [false,true]
abbrev base : List Bool := [false,true,true]
def sc : V → Nat | v107 => 9 | v108 => 6 | v110 => 7
def pc : V → Nat | v108 => 8 | _ => 11

theorem start (v : V) (R : List Bool) : run0 (ctr v) 10 ⟨4,h,z 3++R⟩ = some ⟨3,A++base,f++R⟩ := by cases v <;> rfl
theorem scan (v : V) (L R : List Bool) : run0 (ctr v) (sc v) ⟨3,A++L,f++W v++R⟩ = some ⟨3,A++P v++L,f++R⟩ := by cases v <;> rfl
theorem pop (v : V) (L R : List Bool) : run0 (ctr v) (pc v) ⟨4,h++P v++L,f++R⟩ = some ⟨4,h++L,f++W' v++R⟩ := by cases v <;> rfl
theorem finish (v : V) (R : List Bool) : run0 (ctr v) 5 ⟨4,h++base,f++R⟩ = some ⟨4,h,z 3++h++R⟩ := by cases v <;> rfl

theorem rotate (v : V) (n : Nat) : h++rep (W' v) n = rep (W v) n++h := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,W,W',List.append_assoc] at *; rw [ih]

def cfg (v : V) (n : Nat) (S : List Bool) : Z0 := ⟨4,h,z 3++rep (W v) n++S⟩
def cost (v : V) (n extra k : Nat) := 10+sc v*n+k+pc v*(n+extra)+5

theorem phase (v : V) (n extra k : Nat) (S U : List Bool)
    (turn : ∀ L : List Bool, run0 (ctr v) k ⟨3,A++L,f++S⟩ = some ⟨4,h++rep (P v) extra++L,f++U⟩) :
    run0 (ctr v) (cost v n extra k) (cfg v n S) = some (cfg v (n+extra) (h++U)) := by
  have H1 := start v (rep (W v) n++S)
  have H2 := forward (scan v) n base S
  have H3 := turn (rep (P v) n++base)
  have H4 := backward (pop v) (n+extra) base U
  have H5 := finish v (rep (W' v) (n+extra)++U)
  have H := join0 H1 (by simpa only [List.append_assoc] using H2)
  have H := join0 H (by simpa only [List.append_assoc] using H3)
  have hrep : rep (P v) (n+extra)=rep (P v) extra++rep (P v) n := by rw [Nat.add_comm,rep_add]
  rw [hrep] at H4
  have H := join0 H (by simpa only [List.append_assoc] using H4)
  have H := join0 H (by simpa only [List.append_assoc] using H5)
  unfold cfg cost
  simp only [List.append_assoc] at H ⊢
  rw [←List.append_assoc h,rotate,List.append_assoc] at H
  simpa only [List.append_assoc] using H

theorem turn107a (L : List Bool) : run0 (ctr v107) 10 ⟨3,A++L,f++u 4⟩ = some ⟨4,h++rep (P v107) 1++L,f++[]⟩ := rfl
theorem turn107b (L : List Bool) : run0 (ctr v107) 18 ⟨3,A++L,f++h⟩ = some ⟨4,h++rep (P v107) 1++L,f++u 3⟩ := rfl
theorem turn108a (L : List Bool) : run0 (ctr v108) 7 ⟨3,A++L,f++u 4⟩ = some ⟨4,h++rep (P v108) 1++L,f++h⟩ := rfl
theorem turn108b (L : List Bool) : run0 (ctr v108) 17 ⟨3,A++L,f++u 2⟩ = some ⟨4,h++rep (P v108) 1++L,f++u 3⟩ := rfl
theorem turn110a (L : List Bool) : run0 (ctr v110) 8 ⟨3,A++L,f++u 4⟩ = some ⟨4,h++rep (P v110) 1++L,f++[]⟩ := rfl
theorem turn110b (L : List Bool) : run0 (ctr v110) 11 ⟨3,A++L,f++h⟩ = some ⟨4,h++rep (P v110) 0++L,f++[true,true,false]⟩ := rfl
theorem turn110c (L : List Bool) : run0 (ctr v110) 18 ⟨3,A++L,f++[true,true,true,false]⟩ = some ⟨4,h++rep (P v110) 1++L,f++u 3⟩ := rfl

def family : V → Nat → Z0
  | v107,n => cfg v107 (2*n+1) (u 4)
  | v108,n => cfg v108 (2*n) (u 4)
  | v110,n => cfg v110 (2*n) [true,true,true,false]
def cycleCost : V → Nat → Nat
  | v107,n => cost v107 (2*n+1) 1 10 + cost v107 (2*n+2) 1 18
  | v108,n => cost v108 (2*n) 1 7 + cost v108 (2*n+1) 1 17
  | v110,n => cost v110 (2*n) 1 18 + cost v110 (2*n+1) 1 8 + cost v110 (2*n+2) 0 11

def entryCost : V → Nat | v107 => 64 | _ => 46
theorem entry (v : V) : run0 (ctr v) (entryCost v) ⟨0,[],[]⟩ = some (family v 0) := by cases v <;> rfl

theorem growth (v : V) (n : Nat) : run0 (ctr v) (cycleCost v n) (family v n) = some (family v (n+1)) := by
  cases v
  case v107 =>
    have H1 := phase v107 (2*n+1) 1 10 (u 4) [] turn107a
    have H2 := phase v107 (2*n+2) 1 18 h (u 3) turn107b
    have H := join0 H1 H2
    simpa only [family,cycleCost,show h++u 3=u 4 by rfl,show h++[true,true,false]=[true,true,true,false] by rfl,show 2*(n+1)+1=2*n+2+1 by omega] using H
  case v108 =>
    have H1 := phase v108 (2*n) 1 7 (u 4) h turn108a
    have H2 := phase v108 (2*n+1) 1 17 (u 2) (u 3) turn108b
    have H := join0 H1 H2
    simpa only [family,cycleCost,show h++u 3=u 4 by rfl,show h++[true,true,false]=[true,true,true,false] by rfl,show 2*(n+1)=2*n+1+1 by omega] using H
  case v110 =>
    have H1 := phase v110 (2*n) 1 18 [true,true,true,false] (u 3) turn110c
    have H2 := phase v110 (2*n+1) 1 8 (u 4) [] turn110a
    have H3 := phase v110 (2*n+2) 0 11 h [true,true,false] turn110b
    have H := join0 (join0 H1 H2) H3
    simpa only [family,cycleCost,show h++u 3=u 4 by rfl,show h++[true,true,false]=[true,true,true,false] by rfl,show 2*(n+1)=2*n+2 by omega,Nat.add_zero] using H
open BB6.Agent13BlankDelay
theorem never (v : V) (m : Machine) (hm : compatible (ctr v) m) : NeverHalts m :=
  never_of_growth (ctr v) (family v) (entryCost v) (cycleCost v) (entry v)
    (fun n => by cases v <;> simp [cycleCost,cost] <;> omega) (growth v) m hm
theorem cover (v : V) (B : Nat) : Cover (WeightedBound B) (ctr v) :=
  .leaf _ (fun m hm => weighted_never B m (never v m hm))
#print axioms entry
#print axioms growth
#print axioms never
#print axioms cover
end GroupD

namespace Single137
abbrev W : List Bool := [true,false,false,true]
abbrev P : List Bool := [false,true,true,true]
def ctr := FAR.fromCodes [7,23,11,3,14,0,3,16,12,11,5,24]
theorem start (R : List Bool) : run0 ctr 9 ⟨4,h,f++R⟩ = some ⟨5,P,R⟩ := rfl
theorem scan (L R : List Bool) : run0 ctr 6 ⟨5,P++L,[]++W++R⟩ = some ⟨5,P++P++L,[]++R⟩ := rfl
theorem pop (L R : List Bool) : run0 ctr 8 ⟨4,h++P++L,f++R⟩ = some ⟨4,h++L,f++W++R⟩ := rfl
theorem turnA (L : List Bool) : run0 ctr 9 ⟨5,P++L,u 2⟩ = some ⟨4,h++P++L,f++[false,false,true]⟩ := rfl
theorem turnB (L : List Bool) : run0 ctr 9 ⟨5,P++L,[false,false,true]⟩ = some ⟨4,h++L,f++W++h⟩ := rfl
theorem turnC (L : List Bool) : run0 ctr 9 ⟨5,P++L,h⟩ = some ⟨4,h++P++L,f++u 2⟩ := rfl

def cfg (n : Nat) (S : List Bool) : Z0 := ⟨4,h,f++rep W n++S⟩
def cost (n extra : Nat) := 9+6*n+9+8*(n+extra)
theorem phase (n extra : Nat) (S U : List Bool)
    (turn : ∀ L : List Bool, run0 ctr 9 ⟨5,P++L,S⟩ = some ⟨4,h++rep P extra++L,f++U⟩) :
    run0 ctr (cost n extra) (cfg n S) = some (cfg (n+extra) U) := by
  have H1 := start (rep W n++S)
  have H2 := forward scan n [] S
  have H3 := turn (rep P n)
  have H4 := backward pop (n+extra) [] U
  have H := join0 H1 (by simpa only [List.nil_append,List.append_nil,List.append_assoc] using H2)
  have H := join0 H (by simpa only [List.append_assoc] using H3)
  have hr : rep P (n+extra)=rep P extra++rep P n := by rw [Nat.add_comm,rep_add]
  rw [hr] at H4
  have H := join0 H (by simpa only [List.append_nil,List.append_assoc] using H4)
  simpa only [cfg,cost,List.append_assoc] using H

def family (n : Nat) := cfg (3*n+1) (u 2)
def cycleCost (n : Nat) := cost (3*n+1) 1 + cost (3*n+2) 0 + cost (3*n+3) 1
theorem entry : run0 ctr 30 ⟨0,[],[]⟩ = some (family 0) := rfl
theorem growth (n : Nat) : run0 ctr (cycleCost n) (family n) = some (family (n+1)) := by
  have H1 := phase (3*n+1) 1 (u 2) [false,false,true] turnA
  have H2 := phase (3*n+2) 0 [false,false,true] (W++h) turnB
  have H2' : run0 ctr (cost (3*n+2) 0) (cfg (3*n+2) [false,false,true]) = some (cfg (3*n+3) h) := by
    unfold cfg at H2 ⊢
    rw [rep_succ_right W (3*n+2)]
    simpa only [Nat.add_zero,List.append_assoc] using H2
  have H3 := phase (3*n+3) 1 h (u 2) turnC
  have H := join0 (join0 H1 H2') H3
  simpa only [family,cycleCost,show 3*(n+1)+1=3*n+3+1 by omega] using H
open BB6.Agent13BlankDelay
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr family 30 cycleCost entry (fun n => by unfold cycleCost cost; omega) growth m hm
theorem cover (B : Nat) : Cover (WeightedBound B) ctr :=
  .leaf _ (fun m hm => weighted_never B m (never m hm))
#print axioms entry
#print axioms growth
#print axioms never
#print axioms cover
end Single137

namespace Single139
abbrev W : List Bool := [true,false,false]
abbrev W' : List Bool := [false,false,true]
abbrev P : List Bool := [false,true,true]
def ctr := FAR.fromCodes [7,23,11,9,14,0,3,16,12,11,5,24]
theorem start (R : List Bool) : run0 ctr 9 ⟨4,h,f++R⟩ = some ⟨5,P++h,R⟩ := rfl
theorem scan (L R : List Bool) : run0 ctr 5 ⟨5,P++L,[]++W++R⟩ = some ⟨5,P++P++L,[]++R⟩ := rfl
theorem turn (L : List Bool) : run0 ctr 11 ⟨5,P++L,h⟩ = some ⟨4,h++P++L,f++W'⟩ := rfl
theorem pop (L R : List Bool) : run0 ctr 5 ⟨4,h++P++L,f++R⟩ = some ⟨4,h++L,f++W'++R⟩ := rfl
theorem finish (R : List Bool) : run0 ctr 3 ⟨4,h++h,f++R⟩ = some ⟨4,h,f++h++R⟩ := rfl
theorem rotate (n : Nat) : h++rep W' n = rep W n++h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change h++(([false,false]++h)++rep W' n) = (h++[false,false]++rep W n)++h
    simp only [List.append_assoc]
    rw [ih]

def family (n : Nat) : Z0 := ⟨4,h,f++rep W (2*n+2)++h⟩
def cycleCost (n : Nat) := 9+5*(2*n+2)+11+5*(2*n+3)+3
theorem entry : run0 ctr 32 ⟨0,[],[]⟩ = some (family 0) := rfl
theorem growth (n : Nat) : run0 ctr (cycleCost n) (family n) = some (family (n+1)) := by
  have H1 := start (rep W (2*n+2)++h)
  have H2 := forward scan (2*n+2) h h
  have H3 := turn (rep P (2*n+2)++h)
  have H4 := backward pop (2*n+3) h W'
  have H5 := finish (rep W' (2*n+3)++W')
  have H := join0 H1 (by simpa only [List.nil_append,List.append_assoc] using H2)
  have H := join0 H (by simpa only [List.append_assoc] using H3)
  have H := join0 H (by simpa only [rep,List.append_assoc] using H4)
  have H := join0 H (by simpa only [rep,List.append_assoc] using H5)
  unfold family cycleCost
  change run0 ctr (9+5*(2*n+2)+11+5*(2*n+3)+3) ⟨4,h,f++rep W (2*n+2)++h⟩ = some ⟨4,h,f++rep W (2*(n+1)+2)++h⟩
  have he : rep W (2*(n+1)+2)++h=h++(rep W' (2*n+3)++W') := by
    rw [show 2*(n+1)+2=2*n+3+1 by omega,←rotate,rep_succ_right W']
  simp only [List.append_assoc]
  rw [he]
  simpa only [List.append_assoc,rep] using H
open BB6.Agent13BlankDelay
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr family 32 cycleCost entry (fun n => by unfold cycleCost; omega) growth m hm
theorem cover (B : Nat) : Cover (WeightedBound B) ctr :=
  .leaf _ (fun m hm => weighted_never B m (never m hm))
#print axioms entry
#print axioms growth
#print axioms never
#print axioms cover
end Single139

namespace Single140
def ctr := FAR.fromCodes [7,23,11,13,14,0,3,16,12,11,5,24]
abbrev A : List Bool := [false,true,true]
theorem start (R : List Bool) : run0 ctr 9 ⟨4,h,f++R⟩ = some ⟨5,A++h,R⟩ := rfl
theorem scan (L R : List Bool) : run0 ctr 9 ⟨5,A++L,[]++u 3++R⟩ = some ⟨5,A++u 3++L,[]++R⟩ := rfl
theorem turn (L : List Bool) : run0 ctr 9 ⟨5,A++L,u 2⟩ = some ⟨4,u 4++L,f++h⟩ := rfl
theorem pop (L R : List Bool) : run0 ctr 3 ⟨4,h++h++L,f++R⟩ = some ⟨4,h++L,f++h++R⟩ := rfl

theorem u_add (a b : Nat) : u (a+b)=u a++u b := by
  induction a with
  | zero => simp [u]
  | succ a ih => rw [show a+1+b=a+b+1 by omega]; change true :: u (a+b)=true :: (u a++u b); rw [ih]
theorem rep_u (k n : Nat) : rep (u k) n = u (k*n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rep,ih,Nat.mul_succ]; rw [←u_add,Nat.add_comm]

def family (n : Nat) : Z0 := ⟨4,h,f++u (3*n+8)⟩
def cycleCost (n : Nat) := 9+9*(n+2)+9+3*(3*n+10)
theorem entry : run0 ctr 62 ⟨0,[],[]⟩ = some (family 0) := rfl
theorem growth (n : Nat) : run0 ctr (cycleCost n) (family n) = some (family (n+1)) := by
  have H1 := start (u (3*n+8))
  have H2 := forward scan (n+2) h (u 2)
  have H3 := turn (u (3*(n+2))++h)
  have H4 := backward pop (3*n+10) [] h
  simp only [rep_u,List.nil_append] at H2
  rw [←u_add,show 3*(n+2)+2=3*n+8 by omega] at H2
  have H := join0 H1 (by simpa only [List.nil_append,List.append_assoc] using H2)
  have H := join0 H (by simpa only [List.append_assoc] using H3)
  have hl : u 4++(u (3*(n+2))++h)=h++u (3*n+10) := by
    change u 4++(u (3*(n+2))++u 1)=u 1++u (3*n+10)
    rw [←u_add,←u_add,←u_add]; congr 1 <;> omega
  rw [hl] at H
  change run0 ctr (3*(3*n+10)) ⟨4,h++rep (u 1) (3*n+10)++[],f++h⟩ = some ⟨4,h++[],f++rep (u 1) (3*n+10)++h⟩ at H4
  simp only [rep_u,Nat.one_mul,List.append_nil] at H4
  have H := join0 H H4
  unfold family cycleCost
  have hr : f++u (3*n+10)++h=f++u (3*(n+1)+8) := by
    change f++u (3*n+10)++u 1=f++u (3*(n+1)+8)
    rw [List.append_assoc,←u_add]; congr 2 <;> omega
  rw [hr] at H
  exact H
open BB6.Agent13BlankDelay
theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=
  never_of_growth ctr family 62 cycleCost entry (fun n => by unfold cycleCost; omega) growth m hm
theorem cover (B : Nat) : Cover (WeightedBound B) ctr :=
  .leaf _ (fun m hm => weighted_never B m (never m hm))
#print axioms entry
#print axioms growth
#print axioms never
#print axioms cover
end Single140

end BB6.Agent6C1ZeroLASweeps
