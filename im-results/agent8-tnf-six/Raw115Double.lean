import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw115Double
open BB6Coverage BB6Coverage.Agent31Pump
def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,3⟩)
  | 5,true => some (some ⟨true,true,1⟩)
  | _,_ => none
abbrev P (n : Nat) := rep [true,false] n
abbrev O (n : Nat) := List.replicate n true
def E (k : Nat) (L R : List Bool) : Z0 := ⟨4,false::(P k ++ L),R⟩
def H (k : Nat) (L R : List Bool) : Z0 := ⟨4,true::(P k ++ L),R⟩
def B (k : Nat) (R : List Bool) : Z0 := ⟨1,O (2+k),R⟩
def A (h : Nat) : Z0 := ⟨0,[],O (6*h+1)⟩
theorem leftSweep (k : Nat) (L R : List Bool) :
    run0 p (2*k) (E k L R) = some (E 0 L (O (2*k) ++ R)) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h : run0 p 2 (E (k+1) L R) = some (E k L (true::true::R)) := by rfl
    have g := join0 h (ih (true::true::R))
    rw [show 2+2*k=2*(k+1) by omega] at g
    have hw : O (2*k) ++ true::true::R = O (2*(k+1)) ++ R := by
      change O (2*k) ++ ([true,true]++R) = _
      rw [← List.append_assoc]
      change (O (2*k) ++ O 2) ++ R = _
      rw [List.replicate_append_replicate, show 2*k+2=2*(k+1) by omega]
    rw [hw] at g
    exact g

theorem rightSweep (k j : Nat) (L R : List Bool) :
    run0 p (2*k) (H j L (O (2*k)++R)) = some (H (k+j) L R) := by
  induction k generalizing j with
  | zero => simp [run0]
  | succ k ih =>
    have h : run0 p 2 (H j L (O (2*(k+1))++R)) = some (H (j+1) L (O (2*k)++R)) := by
      rw [show 2*(k+1)=2*k+1+1 by omega]
      rfl
    have g := join0 h (ih (j+1))
    rw [show 2+2*k=2*(k+1) by omega,show k+(j+1)=k+1+j by omega] at g
    exact g

theorem convert (k : Nat) (L : List Bool) :
    run0 p (4*k+10) (E k (true::true::L) []) = some (E (k+2) L []) := by
  have h := leftSweep k (true::true::L) []
  have g : run0 p 2 (E 0 (true::true::L) (O (2*k)++[])) = some (H 0 L (O (2*(k+1))++[])) := by
    rw [show 2*(k+1)=2*k+1+1 by omega];rfl
  have z := rightSweep (k+1) 0 L []
  simp only [Nat.add_zero] at z
  have tail : run0 p 6 (H (k+1) L []) = some (E (k+2) L []) := by
    cases k <;> rfl
  have q := join0 (join0 (join0 h g) z) tail
  rw [show 2*k+2+2*(k+1)+6=4*k+10 by omega] at q
  exact q

theorem finish (k : Nat) : run0 p (2*k+1) (E k [] []) = some ⟨0,[],O (2*k+1)⟩ := by
  have h := leftSweep k [] []
  have g : run0 p 1 (E 0 [] (O (2*k)++[])) = some ⟨0,[],O (2*k+1)⟩ := by rw [List.append_nil];rfl
  exact join0 h g

def costConvert (k : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => 4*k+10 + costConvert (k+2) n

theorem convertAll (k n : Nat) :
    run0 p (costConvert k n) (E k (O (2*n)) []) = some (E (k+2*n) [] []) := by
  induction n generalizing k with
  | zero => simp [costConvert, run0]
  | succ n ih =>
    have h := convert k (O (2*n))
    rw [show 2*(n+1)=2*n+1+1 by omega]
    change run0 p (costConvert k (n+1)) (E k (true::true::O (2*n)) []) = _
    have g := join0 h (ih (k+2))
    rw [show k+2+2*n=k+2*(n+1) by omega] at g
    exact g

theorem bSweep (k j : Nat) :
    run0 p (5*k) (B j (O (3*k))) = some (B (j+3*k) []) := by
  induction k generalizing j with
  | zero => simp [run0]
  | succ k ih =>
    have h : run0 p 5 (B j (O (3*(k+1)))) = some (B (j+3) (O (3*k))) := by
      unfold B
      rw [show 3*(k+1)=3*k+1+1+1 by omega,show 2+(j+3)=j+1+1+1+1+1 by omega,show 2+j=j+1+1 by omega]
      rfl
    have g := join0 h (ih (j+3))
    rw [show 5+5*k=5*(k+1) by omega,show j+3+3*k=j+3*(k+1) by omega] at g
    exact g

def cost (h : Nat) := 1+5*(2*h)+9+costConvert 1 (3*h+1)+(2*(6*h+3)+1)
theorem epoch (h : Nat) : run0 p (cost h) (A h) = some (A (2*h+1)) := by
  have h1 : run0 p 1 (A h) = some (B 0 (O (3*(2*h)))) := by
    unfold A B
    rw [show 6*h+1=3*(2*h)+1 by omega];rfl
  have h2 := bSweep (2*h) 0
  have h3 : run0 p 9 (B (0+3*(2*h)) []) = some (E 1 (O (2*(3*h+1))) []) := by
    unfold B
    rw [show 2*(3*h+1)=3*(2*h)+1+1 by omega,show 2+(0+3*(2*h))=3*(2*h)+1+1 by omega]
    rfl
  have h4 := convertAll 1 (3*h+1)
  rw [show 1+2*(3*h+1)=6*h+3 by omega] at h4
  have h5 := finish (6*h+3)
  have z := join0 (join0 (join0 (join0 h1 h2) h3) h4) h5
  unfold A cost
  rw [show 6*(2*h+1)+1=2*(6*h+3)+1 by omega]
  exact z

theorem entry : run0 p 29 ⟨0,[],[]⟩ = some (A 1) := by rfl
def param : Nat → Nat
  | 0 => 1
  | n+1 => 2*param n+1
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_growth p (fun n => A (param n)) 29 (fun n => cost (param n))
    entry (by intro n; unfold cost; omega) (fun n => epoch (param n)) m hm
#print axioms never
end BB6.Agent8Raw115Double
