import Late1341Repeat
namespace BB6.Agent13Raw120Late1341
open BB6Coverage BB6Coverage.Agent13PackedZipper
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def onesFast (base n x : Nat) : Nat := base^n*(x+1)-1

theorem ones_add_one (base n x : Nat) (hb : 0 < base) : ones base n x+1=base^n*(x+1) := by
  induction n with
  | zero => simp [ones]
  | succ n ih =>
    calc
      ones base (n+1) x+1 = base*(ones base n x+1) := by
        simp only [ones, Nat.mul_add, Nat.mul_one]
        omega
      _ = base*(base^n*(x+1)) := by rw [ih]
      _ = base^(n+1)*(x+1) := by rw [Nat.pow_succ, Nat.mul_comm (base^n) base, Nat.mul_assoc]

theorem ones_fast (base n x : Nat) (hb : 0 < base) : ones base n x = onesFast base n x := by
  unfold onesFast
  have h := ones_add_one base n x hb
  omega

theorem repeat18Fast (n L R : Nat) :
    runP table (18*n) ⟨0,8*L,4*onesFast 4 n R+1⟩ = some ⟨0,8*onesFast 4 n L,4*R+1⟩ := by
  rw [← ones_fast 4 n R (by decide),← ones_fast 4 n L (by decide)]
  exact repeat18 n L R

theorem repeatEFast (n L R : Nat) :
    runP table n ⟨4,onesFast 2 n L,R⟩ = some ⟨4,L,onesFast 2 n R⟩ := by
  rw [← ones_fast 2 n L (by decide),← ones_fast 2 n R (by decide)]
  exact repeatE n L R

inductive Action where
  | plain (n : Nat)
  | sweep18 (n : Nat)
  | sweepE (n : Nat)
  deriving Repr

def cost : Action → Nat
  | .plain n => n
  | .sweep18 n => 18*n
  | .sweepE n => n

def applyAction : Action → P → Option P
  | .plain n,z => runP table n z
  | .sweep18 n,z =>
    let L := z.l/8
    let R := z.r/4^(n+1)
    if z = ⟨0,8*L,4*onesFast 4 n R+1⟩ then some ⟨0,8*onesFast 4 n L,4*R+1⟩ else none
  | .sweepE n,z =>
    let L := z.l/2^n
    let R := z.r
    if z = ⟨4,onesFast 2 n L,R⟩ then some ⟨4,L,onesFast 2 n R⟩ else none

theorem applyAction_sound {a : Action} {z z' : P} (h : applyAction a z = some z') : runP table (cost a) z = some z' := by
  cases a with
  | plain n => exact h
  | sweep18 n =>
    let L := z.l/8
    let R := z.r/4^(n+1)
    change (if z = ⟨0,8*L,4*onesFast 4 n R+1⟩ then some ⟨0,8*onesFast 4 n L,4*R+1⟩ else none) = some z' at h
    split at h
    next hz =>
      exact (congrArg (runP table (18*n)) hz).trans ((repeat18Fast n L R).trans h)
    next => contradiction
  | sweepE n =>
    let L := z.l/2^n
    let R := z.r
    change (if z = ⟨4,onesFast 2 n L,R⟩ then some ⟨4,L,onesFast 2 n R⟩ else none) = some z' at h
    split at h
    next hz =>
      exact (congrArg (runP table n) hz).trans ((repeatEFast n L R).trans h)
    next => contradiction

def runActions : List Action → P → Option P
  | [],z => some z
  | a::as,z => (applyAction a z).bind (runActions as)

def costActions : List Action → Nat
  | [] => 0
  | a::as => cost a+costActions as

theorem runActions_sound {as : List Action} {z z' : P} (h : runActions as z = some z') : runP table (costActions as) z = some z' := by
  induction as generalizing z with
  | nil => exact h
  | cons a as ih =>
    cases ha : applyAction a z with
    | none => simp [runActions,ha] at h
    | some w =>
      have htail : runActions as w = some z' := by simpa [runActions,ha] using h
      exact joinP (applyAction_sound ha) (ih htail)

#print axioms runActions_sound
end BB6.Agent13Raw120Late1341
