import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B0RCC1REM155
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none

def P : List Bool := [false,true,false,true]
def K : List Bool := [false,true,false,true,false,true]
def I : List Bool := [true,false,true,false,true,false]
def J : List Bool := [true,false,true,false,true]
def F : List Bool := [false,true,true,false,false,false]
def O : List Bool := [false,false,false,true,false,false]
def Q : List Bool := [false,false,false,false,false,true]
def H : List Bool := [false,true,false,false,false,false,false,true]
def U : List Bool := [false,true]
def V : List Bool := [false,false,true]
def S (n : Nat) : Z0 := ⟨4,[true],P++rep K n⟩
def cost : Nat := 6

theorem first : run0 table 12 ⟨0,[],[]⟩ = some (S 0) := by rfl
private theorem start0 : run0 table 7 (S 0) = some ⟨4,F++[true],[]⟩ := by rfl
private theorem start1 (R : List Bool) :
    run0 table 7 ⟨4,[true],[false,true,false,true,false]++R⟩ = some ⟨4,F++[true],R⟩ := by rfl
private theorem push (L R : List Bool) :
    run0 table 12 ⟨4,F++L,[]++I++R⟩ = some ⟨4,F++O++L,[]++R⟩ := by rfl
private theorem pushLast (L : List Bool) :
    run0 table 12 ⟨4,F++L,J⟩ = some ⟨4,F++O++L,[]⟩ := by rfl
private theorem turn (L : List Bool) :
    run0 table 14 ⟨4,F++L,[]⟩ = some ⟨4,H++[false,false]++L,[]⟩ := by rfl
private theorem firstSweep (L R : List Bool) :
    run0 table 6 ⟨4,H++L,R⟩ = some ⟨4,U++L,K++R⟩ := by rfl
private theorem pop (L R : List Bool) :
    run0 table (cost) ⟨4,U++Q++L,K++R⟩ = some ⟨4,U++L,K++K++R⟩ := by rfl
private theorem finish (R : List Bool) :
    run0 table (cost-2) ⟨4,U++V,K++R⟩ = some ⟨4,[true],P++K++R⟩ := by rfl
private theorem rotate2 (n : Nat) : [false,false]++rep O n = rep Q n++[false,false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rep,List.append_assoc]
    have h : [false,false]++O = Q++[false,false] := by rfl
    rw [← List.append_assoc [false,false] O, h, List.append_assoc, ih]
private theorem pushAll (n : Nat) :
    ∃ k, run0 table k (S n) = some ⟨4,F++rep O n++[true],[]⟩ := by
  cases n with
  | zero => exact ⟨7,start0⟩
  | succ n =>
    have hr : P++rep K (n+1) = [false,true,false,true,false]++(rep I n++J) := by
      change P++(K++rep K n) = _
      have hr' : P++K = [false,true,false,true,false]++J := by rfl
      have hJ : J++rep K n = rep I n++J := by
        induction n with
        | zero => rfl
        | succ n ih =>
          have hh : J++K = I++J := by rfl
          simp only [rep,← List.append_assoc J K,hh,List.append_assoc,ih]
      rw [← List.append_assoc,hr',List.append_assoc,hJ]
    have h1 : run0 table 7 (S (n+1)) = some ⟨4,F++[true],rep I n++J⟩ := by
      simp only [S,hr]; exact start1 _
    have h2 := sweepR table 4 F [] I O 12 push n [true] J
    have h2' : run0 table (12*n) ⟨4,F++[true],rep I n++J⟩ = some ⟨4,F++(rep O n++[true]),J⟩ := by
      simpa only [List.nil_append,List.append_assoc] using h2
    have h3 := pushLast (rep O n++[true])
    have h4 := join0 (join0 h1 h2') h3
    exact ⟨_,by simpa only [rep,List.append_assoc] using h4⟩
private theorem popAll (n : Nat) (R : List Bool) :
    run0 table (cost*n) ⟨4,U++rep Q n++V,K++R⟩ = some ⟨4,U++V,K++rep K n++R⟩ := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have h1 := pop (rep Q n++V) R
    have h2 := ih (K++R)
    have h1' : run0 table (cost) ⟨4,U++rep Q (n+1)++V,K++R⟩ = some ⟨4,U++rep Q n++V,K++(K++R)⟩ := by
      simpa only [rep,List.append_assoc] using h1
    have h := join0 h1' h2
    rw [Nat.mul_succ,Nat.add_comm (cost*n)]
    simpa only [rep,List.append_assoc,← List.append_assoc (rep K n) K R,rep_snoc K n] using h

theorem growth (n : Nat) : ∃ k, 0 < k ∧ run0 table k (S n) = some (S (n+1)) := by
  obtain ⟨k,h1⟩ := pushAll n
  have h2 := turn (rep O n++[true])
  have h2' : run0 table 14 ⟨4,F++rep O n++[true],[]⟩ = some ⟨4,H++rep Q n++V,[]⟩ := by
    have h : H++[false,false]++(rep O n++[true]) = H++rep Q n++V := by
      calc
        _ = H++(([false,false]++rep O n)++[true]) := by simp only [List.append_assoc]
        _ = _ := by rw [rotate2]; simp only [List.append_assoc]; rfl
    rw [h] at h2
    simpa only [List.append_assoc] using h2
  have h3 := firstSweep (rep Q n++V) []
  have h3' : run0 table 6 ⟨4,H++rep Q n++V,[]⟩ = some ⟨4,U++rep Q n++V,K⟩ := by
    simpa only [List.append_assoc,List.append_nil] using h3
  have h4 := popAll n []
  have h5 := finish (rep K n)
  have h4' : run0 table (cost*n) ⟨4,U++rep Q n++V,K⟩ = some ⟨4,U++V,K++rep K n⟩ := by
    simpa only [List.append_nil] using h4
  have h := join0 (join0 (join0 (join0 h1 h2') h3') h4') h5
  refine ⟨k+14+6+cost*n+(cost-2),by omega,?_⟩
  simpa only [S,rep,rep_snoc,List.append_assoc] using h

theorem live_prefix (n : Nat) : ∃ t j, n ≤ t ∧ run0 table t ⟨0,[],[]⟩ = some (S j) := by
  induction n with
  | zero => exact ⟨12,0,by decide,first⟩
  | succ n ih =>
    obtain ⟨t,j,ht,hr⟩ := ih
    obtain ⟨k,hk,hs⟩ := growth j
    exact ⟨t+k,j+1,by omega,join0 hr hs⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨t,j,ht,hr⟩ := live_prefix n
  have hz : (zrun table t start).map project = some (S j) :=
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
#print axioms live_prefix
#print axioms never
end BB6.Agent25Raw43B0RCC1REM155
