import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Raw61Unary
open BB6Coverage Agent31Pump
abbrev W := List Bool
abbrev o (n : Nat) : W := List.replicate n true
abbrev z (n : Nat) : W := List.replicate n false
abbrev cfg (q : Fin 6) (l r : W) : Z0 := ⟨q,l,r⟩
theorem repTail (b : Bool) (n m : Nat) (L : W) :
    List.replicate n b ++ (List.replicate m b ++ L) = List.replicate (n+m) b ++ L := by
  rw [← List.append_assoc,List.replicate_append_replicate]

def table (variant : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => if variant then some (some ⟨true,false,5⟩) else some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none

theorem aStep (v : Bool) (L R : W) : run0 (table v) 6 (cfg 0 (false::L) (false::false::true::true::R)) = some (cfg 0 (false::true::true::L) (false::false::R)) := by cases v <;> rfl
theorem aStepBlank (v : Bool) (R : W) : run0 (table v) 6 (cfg 0 [] (false::false::true::true::R)) = some (cfg 0 [false,true,true] (false::false::R)) := by cases v <;> rfl

theorem aSweep (v : Bool) (k : Nat) (L : W) :
    run0 (table v) (6*k) (cfg 0 (false::L) (false::false::o (2*k))) = some (cfg 0 (false::(o (2*k) ++ L)) [false,false]) := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h := join0 (aStep v L (o (2*k))) (ih (true::true::L))
    rw [show 6*(k+1)=6+6*k by omega]
    have ho : o (2*(k+1)) = true::true::o (2*k) := by rw [show 2*(k+1)=2*k+2 by omega]; rfl
    have he : o (2*k) ++ true::true::L = o (2*(k+1)) ++ L := by
      rw [show 2*(k+1)=2*k+2 by omega]
      exact repTail true (2*k) 2 L
    rw [he] at h
    rw [ho] at ⊢
    rw [ho] at h
    exact h

theorem aEntry (v : Bool) (L : W) : run0 (table v) 3 (cfg 0 (false::L) [false,false]) = some (cfg 3 (false::false::true::true::L) []) := by cases v <;> rfl

theorem aToD (v : Bool) (k : Nat) : run0 (table v) (6+6*k+3) (cfg 0 [] (false::false::o (2*k+2))) = some (cfg 3 (false::false::o (2*k+4)) []) := by
  have h := join0 (join0 (aStepBlank v (o (2*k))) (aSweep v k [true,true])) (aEntry v (o (2*k) ++ [true,true]))
  have hh : o (2*k) ++ [true,true] = o (2*k+2) := by exact @List.replicate_append_replicate (2*k) Bool true 2
  rw [hh] at h
  simpa only [List.replicate_succ,show 2*k+4=(2*k+2)+1+1 by omega] using h

theorem dStep (v : Bool) (L R : W) : run0 (table v) 1 (cfg 3 (false::L) R) = some (cfg 3 L (true::R)) := by cases v <;> rfl

theorem dSweep (v : Bool) (k : Nat) (L R : W) : run0 (table v) k (cfg 3 (z k ++ L) R) = some (cfg 3 L (o k ++ R)) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have h := join0 (dStep v (z k ++ L) R) (ih (true::R))
    rw [show k+1=1+k by omega] at ⊢
    have hh : o k ++ true::R = o (k+1) ++ R := repTail true k 1 R
    rw [hh] at h
    simpa only [List.replicate_succ,show 1+k=k+1 by omega,List.cons_append] using h

theorem dEnd (v : Bool) (k : Nat) : run0 (table v) (k+2+3) (cfg 3 (z (k+2) ++ [true]) []) = some (cfg 0 [] (false::false::o (k+1))) := by
  have h := dSweep v (k+2) [true] []
  have h2 : run0 (table v) 3 (cfg 3 [true] (o (k+2))) = some (cfg 0 [] (false::false::o (k+1))) := by cases v <;> rfl
  simp only [List.append_nil] at h
  exact join0 h h2

theorem dTurn (v : Bool) (k : Nat) (L : W) : run0 (table v) 6 (cfg 3 (true::true::L) (o (k+2))) = some (cfg 5 (true::false::false::true::L) (o k)) := by cases v <;> rfl

def cCost (v : Bool) : Nat := if v then 3 else 1

theorem cStep (v : Bool) (L R : W) : run0 (table v) (cCost v) (cfg 2 (true::false::L) (true::R)) = some (cfg 2 (true::false::false::L) R) := by cases v <;> rfl

theorem cFinish (v : Bool) (L : W) : run0 (table v) (cCost v+1) (cfg 2 (true::false::L) []) = some (cfg 3 (false::false::false::false::L) []) := by cases v <;> rfl

theorem cDrain (v : Bool) (k : Nat) (L : W) : run0 (table v) (cCost v*k+cCost v+1) (cfg 2 (true::false::L) (o k)) = some (cfg 3 (z (k+4) ++ L) []) := by
  induction k generalizing L with
  | zero => simpa [List.replicate_succ] using cFinish v L
  | succ k ih =>
    have h := join0 (cStep v L (o k)) (ih (false::L))
    rw [Nat.mul_succ,show cCost v*k+cCost v+cCost v+1=cCost v+(cCost v*k+cCost v+1) by omega]
    have hh : z (k+4) ++ false::L = z (k+5) ++ L := repTail false (k+4) 1 L
    rw [hh] at h
    simpa only [List.replicate_succ,show k+1+4=k+5 by omega] using h

theorem fDrain (v : Bool) (k : Nat) (L : W) : run0 (table v) (cCost v*k+2) (cfg 5 (true::false::false::true::L) (o k)) = some (cfg 3 (z (k+5) ++ (true::L)) []) := by
  cases k with
  | zero => cases v <;> rfl
  | succ k =>
    have h : run0 (table v) 1 (cfg 5 (true::false::false::true::L) (o (k+1))) = some (cfg 2 (true::false::false::false::true::L) (o k)) := by cases v <;> rfl
    have H := join0 h (cDrain v k (false::false::true::L))
    rw [Nat.mul_succ,show cCost v*k+cCost v+2=1+(cCost v*k+cCost v+1) by omega]
    have hh : z (k+4) ++ false::false::true::L = z (k+6) ++ true::L := repTail false (k+4) 2 (true::L)
    rw [hh] at H
    simpa only [List.replicate_succ,show k+1+5=k+6 by omega] using H

theorem dConsume (v : Bool) (k : Nat) (L : W) : run0 (table v) (k+2+6+(cCost v*k+2)) (cfg 3 (z (k+2) ++ (true::true::L)) []) = some (cfg 3 (z (k+5) ++ (true::L)) []) := by
  have h := dSweep v (k+2) (true::true::L) []
  have h' : run0 (table v) (k+2) (cfg 3 (z (k+2) ++ (true::true::L)) []) = some (cfg 3 (true::true::L) (o (k+2))) := by simpa using h
  exact join0 (join0 h' (dTurn v k L)) (fDrain v k L)

def drainCost (v : Bool) : Nat → Nat → Nat
  | 0,k => k+5
  | n+1,k => k+2+6+(cCost v*k+2) + drainCost v n (k+3)

theorem drain (v : Bool) (n k : Nat) : run0 (table v) (drainCost v n k) (cfg 3 (z (k+2) ++ o (n+1)) []) = some (cfg 0 [] (false::false::o (k+3*n+1))) := by
  induction n generalizing k with
  | zero => simpa [drainCost] using dEnd v k
  | succ n ih =>
    have h := join0 (dConsume v k (o n)) (ih (k+3))
    rw [show k+3*(n+1)+1=k+3+3*n+1 by omega]
    simpa [drainCost,List.replicate_succ,show k+3+2=k+5 by omega] using h

def A (k : Nat) : Z0 := cfg 0 [] (false::false::o (2*k+2))
def epochCost (v : Bool) (k : Nat) := 6+6*k+3+drainCost v (2*k+3) 0

theorem epoch (v : Bool) (k : Nat) : run0 (table v) (epochCost v k) (A k) = some (A (3*k+4)) := by
  have h := join0 (aToD v k) (drain v (2*k+3) 0)
  change run0 (table v) (epochCost v k) (A k) = some (cfg 0 [] (false::false::o (2*(3*k+4)+2)))
  rw [show 2*(3*k+4)+2=0+3*(2*k+3)+1 by omega]
  exact h

theorem entry (v : Bool) : run0 (table v) 21 (cfg 0 [] []) = some (A 1) := by cases v <;> rfl

def index : Nat → Nat
  | 0 => 1
  | n+1 => 3*index n+4

theorem never (v : Bool) (m : Machine) (hm : compatible (table v) m) : NeverHalts m :=
  never_of_growth (table v) (fun n => A (index n)) 21 (fun n => epochCost v (index n))
    (entry v) (by intro n; unfold epochCost; omega) (fun n => epoch v (index n)) m hm

#print axioms epoch
#print axioms entry
#print axioms never
end BB6Coverage.Raw61Unary

namespace BB6.Agent10Recursive
namespace R61M1344
abbrev table := BB6Coverage.Raw61Unary.table false
theorem never (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible table m) : BB6Coverage.NeverHalts m :=
  BB6Coverage.Raw61Unary.never false m hm
end R61M1344
namespace R61M1346
abbrev table := BB6Coverage.Raw61Unary.table true
theorem never (m : BB6Coverage.Machine) (hm : BB6Coverage.compatible table m) : BB6Coverage.NeverHalts m :=
  BB6Coverage.Raw61Unary.never true m hm
end R61M1346
end BB6.Agent10Recursive
