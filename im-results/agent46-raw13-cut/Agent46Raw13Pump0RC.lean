import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Raw13Pump0RC
open BB6Coverage Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,true,2⟩)
  | 3,true => some (some ⟨true,false,4⟩)
  | 4,false => some (some ⟨false,false,0⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none

def T : List Bool := [true,false]
def P : List Bool := [false,true]
def Q : List Bool := [true,true]
def F (a b : Nat) : Z0 := ⟨0,[],[false]++rep T a++rep Q b++[true]⟩
private theorem rep_add (X : List Bool) (a b : Nat) : rep X (a+b) = rep X a++rep X b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => simp only [show a+1+b=(a+b)+1 by omega,rep,ih,List.append_assoc]
private theorem rep_double (X : List Bool) (n : Nat) : rep (X++X) n = rep X (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rep,ih,show 2*(n+1)=2+2*n by omega,rep_add]; simp only [rep,List.append_nil]
private theorem startF (a b : Nat) : run0 table 1 (F a b) = some ⟨1,[false,true],rep T a++rep Q b++[true]⟩ := by rfl
private theorem rightOne (L R : List Bool) : run0 table 2 ⟨1,[false]++L,T++R⟩ = some ⟨1,[false]++P++L,R⟩ := by rfl
private theorem rightSweep (a b : Nat) : run0 table (1+2*a) (F a b) = some ⟨1,[false]++rep P a++[true],rep Q b++[true]⟩ := by
  have h := sweepR table 1 [false] [] T P 2 rightOne a [true] (rep Q b++[true])
  simp only [List.nil_append] at h
  have h0 := startF a b
  simp only [List.append_assoc] at h0
  exact join0 h0 h
private theorem toLeft (L R : List Bool) : run0 table 2 ⟨1,[false]++L,Q++R⟩ = some ⟨1,[true]++P++L,R⟩ := by rfl
private theorem leftTwo (L R : List Bool) : run0 table 8 ⟨1,[true]++(P++P)++L,R⟩ = some ⟨1,[true]++L,(T++T)++R⟩ := by rfl
private theorem endLeft (R : List Bool) : run0 table 3 ⟨1,[true,true],R⟩ = some ⟨0,[],[false]++T++R⟩ := by rfl
private theorem toA (L : List Bool) : run0 table 4 ⟨1,[false]++L,[true]⟩ = some ⟨0,[true]++P++L,[true]⟩ := by rfl
private theorem aLeft (L R : List Bool) : run0 table 2 ⟨0,[true]++P++L,R⟩ = some ⟨0,[true]++L,Q++R⟩ := by rfl
private theorem endA (R : List Bool) : run0 table 9 ⟨0,[true,true],R⟩ = some ⟨0,[],[false]++T++R⟩ := by rfl

theorem reduce (k b : Nat) : run0 table (12*k+16) (F (2*k+1) (b+1)) = some (F (2*k+3) b) := by
  have h0 := rightSweep (2*k+1) (b+1)
  rw [rep, List.append_assoc] at h0
  have h1 := toLeft (rep P (2*k+1)++[true]) (rep Q b++[true])
  have h01 := join0 h0 h1
  have hl : [true]++P++(rep P (2*k+1)++[true]) = [true]++rep (P++P) (k+1)++[true] := by
    rw [rep_double, show 2*(k+1)=2*k+1+1 by omega]
    simp only [rep,List.append_assoc]
  rw [hl] at h01
  have h2 := sweepL table 1 [true] [] (P++P) (T++T) 8 leftTwo (k+1) [true] (rep Q b++[true])
  simp only [List.nil_append] at h2
  have h012 := join0 h01 h2
  have h3 := endLeft (rep (T++T) (k+1)++(rep Q b++[true]))
  have h := join0 h012 h3
  rw [rep_double] at h
  have hh : 2*k+3 = 2*(k+1)+1 := by omega
  rw [hh]
  have hc : 1+2*(2*k+1)+2+8*(k+1)+3=12*k+16 := by omega
  rw [hc] at h
  simpa only [F,rep,List.append_assoc] using h

theorem reset (a : Nat) : run0 table (4*a+16) (F a 0) = some (F 1 (a+1)) := by
  have h0 := rightSweep a 0
  simp only [rep,List.nil_append] at h0
  have h1 := toA (rep P a++[true])
  have h01 := join0 h0 h1
  have h2 := sweepL table 0 [true] [] P Q 2 aLeft (a+1) [true] [true]
  simp only [List.nil_append] at h2
  have hl : [true]++P++(rep P a++[true]) = [true]++rep P (a+1)++[true] := by simp only [rep,List.append_assoc]
  rw [hl] at h01
  have h012 := join0 h01 h2
  have h3 := endA (rep Q (a+1)++[true])
  have h := join0 h012 h3
  rw [show 1+2*a+4+2*(a+1)+9=4*a+16 by omega] at h
  simpa only [F,rep,List.append_assoc,List.append_nil] using h

def drainCost (k : Nat) : Nat → Nat
  | 0 => 8*k+20
  | b+1 => 12*k+16+drainCost (k+1) b

theorem drain (k b : Nat) : run0 table (drainCost k b) (F (2*k+1) b) = some (F 1 (2*(k+b)+2)) := by
  induction b generalizing k with
  | zero => simpa only [drainCost,Nat.add_zero,show 4*(2*k+1)+16=8*k+20 by omega,show 2*k+1+1=2*k+2 by omega] using reset (2*k+1)
  | succ b ih =>
    have h := reduce k b
    have h' : F (2*k+3) b = F (2*(k+1)+1) b := by rw [show 2*k+3=2*(k+1)+1 by omega]
    rw [h'] at h
    simpa only [drainCost,show k+1+b=k+(b+1) by omega] using join0 h (ih (k+1))

theorem cost_closed (k b : Nat) : drainCost k b = 6*b*b+(12*k+18)*b+8*k+20 := by
  induction b generalizing k with
  | zero => simp [drainCost]
  | succ b ih =>
    rw [drainCost,ih]
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_assoc]
    omega

def orbit : Nat → Nat
  | 0 => 0
  | i+1 => 2*orbit i+2

theorem orbit_first : run0 table 12 ⟨0,[],[]⟩ = some (F 1 (orbit 0)) := by rfl

theorem orbit_step (i : Nat) : run0 table (drainCost 0 (orbit i)) (F 1 (orbit i)) = some (F 1 (orbit (i+1))) := by
  simpa only [orbit,Nat.zero_add,Nat.mul_zero] using drain 0 (orbit i)

theorem cost_pos (k b : Nat) : 0 < drainCost k b := by
  cases b <;> simp only [drainCost] <;> omega

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table (fun i => F 1 (orbit i)) 12
    (fun i => drainCost 0 (orbit i)) orbit_first
    (fun i => cost_pos 0 (orbit i)) orbit_step m hm

#print axioms reduce
#print axioms reset
#print axioms drain
#print axioms orbit_first
#print axioms orbit_step
#print axioms cost_pos
#print axioms cost_closed
#print axioms never
end BB6Coverage.Agent31Pump.Raw13Pump0RC
