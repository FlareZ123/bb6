import PackedZipper
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw108LEFast
open BB6Coverage BB6Coverage.Agent13PackedZipper

/-- v=false is 0LE open leaf 1276; v=true is leaf 1313. -/
def table (v : Bool) : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨v,true,5⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,false,4⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨true,true,1⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,4⟩)
  | (4,false) => some (some ⟨false,true,0⟩)
  | (4,true) => some (some ⟨true,false,1⟩)
  | (5,false) => if v then some (some ⟨false,true,3⟩) else some (some ⟨false,false,1⟩)
  | _ => none

def block (d : Nat) : Nat → Nat → Nat
  | 0,x => x
  | k+1,x => d+4*block d k x

theorem block_push (d k x : Nat) : block d k (d+4*x) = d+4*block d k x := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [block,ih]

theorem left2 (v : Bool) (x r : Nat) :
    runP (table v) 2 ⟨1,3+4*x,r⟩ = some ⟨1,x,1+4*r⟩ := by
  have h1 : stepP (table v) ⟨1,3+4*x,r⟩ = some ⟨4,1+2*x,2*r⟩ := by
    have hb : (3+4*x)%2 = 1 := by omega
    have hd : (3+4*x)/2 = 1+2*x := by omega
    simp [stepP,readP,hb,table,moveP,hd,Bool.toNat]
  have h2 : stepP (table v) ⟨4,1+2*x,2*r⟩ = some ⟨1,x,1+4*r⟩ := by
    have hb : (1+2*x)%2 = 1 := by omega
    have hd : (1+2*x)/2 = x := by omega
    simp [stepP,readP,hb,table,moveP,hd,Bool.toNat] <;> omega
  simp [runP,h1,h2]

theorem right2 (v : Bool) (x r : Nat) :
    runP (table v) 2 ⟨1,2*x,1+4*r⟩ = some ⟨1,2*(3+4*x),r⟩ := by
  have h1 : stepP (table v) ⟨1,2*x,1+4*r⟩ = some ⟨2,3+4*x,2*r⟩ := by
    have hb : (1+4*r)%2 = 1 := by omega
    have hd : (1+4*r)/2 = 2*r := by omega
    simp [stepP,readP,table,moveP,hb,hd,Bool.toNat] <;> omega
  have h2 : stepP (table v) ⟨2,3+4*x,2*r⟩ = some ⟨1,2*(3+4*x),r⟩ := by
    have hb : (3+4*x)%2 = 1 := by omega
    have hd : (3+4*x)/2 = 1+2*x := by omega
    simp [stepP,readP,table,moveP,hb,hd,Bool.toNat] <;> omega
  simp [runP,h1,h2]

theorem leftSweep (v : Bool) (k x r : Nat) :
    runP (table v) (2*k) ⟨1,block 3 k x,r⟩ = some ⟨1,x,block 1 k r⟩ := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih =>
    rw [show 2*(k+1)=2+2*k by omega,block]
    have h := joinP (left2 v (block 3 k x) r) (ih (1+4*r))
    rw [block_push] at h
    exact h

theorem rightSweep (v : Bool) (k x r : Nat) :
    runP (table v) (2*k) ⟨1,2*x,block 1 k r⟩ = some ⟨1,2*block 3 k x,r⟩ := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [show 2*(k+1)=2+2*k by omega,block]
    have h := joinP (right2 v x (block 1 k r)) (ih (3+4*x))
    rw [block_push] at h
    exact h

inductive Instr where
  | ordinary (n : Nat)
  | left (k : Nat)
  | right (k : Nat)

def Instr.cost : Instr → Nat
  | .ordinary n => n
  | .left k => 2*k
  | .right k => 2*k

def execute (v : Bool) : Instr → P → Option P
  | .ordinary n,z => runP (table v) n z
  | .left k,z =>
    let x := z.l / 4^k
    if z.q = 1 ∧ z.l = block 3 k x then some ⟨1,x,block 1 k z.r⟩ else none
  | .right k,z =>
    let x := z.l / 2
    let r := z.r / 4^k
    if z.q = 1 ∧ z.l = 2*x ∧ z.r = block 1 k r then some ⟨1,2*block 3 k x,r⟩ else none

theorem execute_sound (v : Bool) (i : Instr) (z t : P)
    (h : execute v i z = some t) : runP (table v) i.cost z = some t := by
  cases i with
  | ordinary n => exact h
  | left k =>
    rcases z with ⟨q,l,r⟩
    simp only [execute] at h
    split at h
    · rename_i he
      obtain ⟨hq,hl⟩ := he
      subst q
      have ht := Option.some.inj h
      subst t
      have hs := leftSweep v k (l/4^k) r
      rw [← hl] at hs
      exact hs
    · contradiction
  | right k =>
    rcases z with ⟨q,l,r⟩
    simp only [execute] at h
    split at h
    · rename_i he
      obtain ⟨hq,hl,hr⟩ := he
      subst q
      have ht := Option.some.inj h
      subst t
      have hs := rightSweep v k (l/2) (r/4^k)
      rw [← hl,← hr] at hs
      exact hs
    · contradiction

def execList (v : Bool) : List Instr → P → Option P
  | [],z => some z
  | i::is,z => (execute v i z).bind (execList v is)
def totalCost : List Instr → Nat
  | [] => 0
  | i::is => i.cost+totalCost is

theorem execList_sound (v : Bool) (is : List Instr) (z t : P)
    (h : execList v is z = some t) : runP (table v) (totalCost is) z = some t := by
  induction is generalizing z with
  | nil => simpa [execList,totalCost,runP] using h
  | cons i is ih =>
    simp only [execList] at h
    cases he : execute v i z with
    | none => simp [he] at h
    | some u =>
      have hh : execList v is u = some t := by simpa [he] using h
      exact joinP (execute_sound v i z u he) (ih u hh)

theorem joinN {p : PartialMachine} {n k t : Nat} {a b c : P}
    (ht : n+k=t) (h : runP p n a = some b) (g : runP p k b = some c) :
    runP p t a = some c := by
  subst t
  exact joinP h g

#print axioms execList_sound
#print axioms joinN
end BB6.Agent10Raw108LEFast
