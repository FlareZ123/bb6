import SweepPumping
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13UnaryRecursion
open BB6Coverage BB6Coverage.Agent31Pump

/-- 1RB1LD1RC0RB1LA1RE1LF0LA1LC1RA1LE--- -/
def p : PartialMachine := FAR.fromCodes [7,14,11,5,2,19,22,0,10,3,18,24]
abbrev Z : List Bool := [false,false,false,false,false]
abbrev U : List Bool := [true,true,true,true,true]
abbrev H : List Bool := [true,false,false,false,false]
abbrev S : List Bool := [false,true,false,true,false,true,true]
abbrev A (l r : List Bool) : Z0 := ⟨0,l,r⟩
def rcfg (q : Fin 6) (l w : List Bool) : Z0 := ⟨q,w.headD false::l,w.tail⟩

theorem bBlock (L W : List Bool) :
    run0 p 5 (rcfg 1 L (U++W)) = some (rcfg 1 (Z++L) W) := by rfl

theorem bScan (k : Nat) (L W : List Bool) :
    run0 p (5*k) (rcfg 1 L (rep U k++W)) = some (rcfg 1 (rep Z k++L) W) := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h := bBlock L (rep U k++W)
    have g := ih (Z++L)
    simpa only [rep,List.append_assoc,← List.append_assoc (rep Z k) Z L,rep_snoc Z k,show 5+5*k=5*(k+1) by omega] using join0 h g

theorem startB (L W : List Bool) :
    run0 p 1 (A (false::L) W) = some (rcfg 1 (true::L) W) := by rfl
theorem finishB (L : List Bool) :
    run0 p 9 (rcfg 1 L S) = some (A L S) := by rfl
theorem setup (k : Nat) (L : List Bool) :
    run0 p (5*k+10) (A (false::L) (rep U k++S)) =
      some (A (rep Z k++true::L) S) := by
  have h := startB L (rep U k++S)
  have g := bScan k (true::L) S
  have f := finishB (rep Z k++true::L)
  simpa only [show 1+5*k+9=5*k+10 by omega] using join0 (join0 h g) f

theorem pop (L R : List Bool) :
    run0 p 5 (A (H++L) R) = some (A L (U++R)) := by rfl
theorem popBlank (R : List Bool) :
    run0 p 5 (A [true] R) = some (A [] (U++R)) := by rfl

def cost : Nat → Nat
  | 0 => 0
  | k+1 => cost k + (5*k+10) + cost k + 5

/-- The five-cell unary recursion may be applied with an arbitrary left tail.
The induction is structural on k, not on the astronomical running time. -/
theorem fill (k : Nat) (L : List Bool) :
    run0 p (cost k) (A (rep Z k++L) S) = some (A L (rep U k++S)) := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    have h := ih (Z++L)
    have g := setup k ([false,false,false,false]++L)
    have f := ih (H++L)
    have e := pop L (rep U k++S)
    have hg : run0 p (5*k+10) (A (Z++L) (rep U k++S)) =
        some (A (rep Z k++(H++L)) S) := by exact g
    have hw : rep Z k++(Z++L) = rep Z (k+1)++L := by
      rw [← List.append_assoc,rep_snoc]
      rfl
    rw [hw] at h
    simpa only [cost,rep,List.append_assoc] using join0 (join0 (join0 h hg) f) e

theorem cost_closed (k : Nat) : cost k + 5*k + 20 = 20*2^k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [cost,Nat.pow_succ]; omega

def root (k : Nat) : Z0 := A [] (rep U k++S)

theorem setupBlank (k : Nat) :
    run0 p (5*k+10) (root k) = some (A (rep Z k++[true]) S) := by
  have h := setup k []
  have pad (n : Nat) (R : List Bool) (hn : 0<n) :
      run0 p n (A [] R) = run0 p n (A [false] R) := by
    cases n with
    | zero => omega
    | succ n => rfl
  unfold root
  rw [pad _ _ (by omega)]
  exact h

theorem rootGrowth (k : Nat) :
    run0 p (20*2^k-5) (root k) = some (root (k+1)) := by
  have h := setupBlank k
  have g := fill k [true]
  have f := popBlank (rep U k++S)
  have hc : 5*k+10+cost k+5=20*2^k-5 := by have := cost_closed k; omega
  simpa only [hc,root,rep,List.append_assoc] using join0 (join0 h g) f

theorem seed : run0 p 18 (A [] []) = some (root 0) := by rfl

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_growth p root 18 (fun k => 20*2^k-5) seed
    (fun k => by have := cost_closed k; omega) rootGrowth m hm

#print axioms rootGrowth
#print axioms never
end BB6.Agent46Raw13UnaryRecursion
