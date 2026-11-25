import Raw54Return
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent8Raw54.Growth71
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨false,false,4⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none

def one : List Bool := [true]
def zero : List Bool := [false]
def three : List Bool := [true,true,true]
def mark : List Bool := [false,true,true]
def zzz : List Bool := [false,false,false]
def block : List Bool := [false,false,true,true,true,false]
def aCfg (j r : Nat) (s : List Bool) : Z0 := ⟨0,three ++ rep zero j ++ three ++ s,rep one r⟩
def bCfg (j : Nat) (s r : List Bool) : Z0 := ⟨0,mark ++ rep zero j ++ three ++ s,r⟩

theorem drainOne (j r : Nat) (s : List Bool) : run0 table 9 (aCfg j (r+1) s) = some (aCfg (j+1) r s) := by rfl

theorem drainAll (j r : Nat) (s : List Bool) : run0 table (9*r) (aCfg j r s) = some (aCfg (j+r) 0 s) := by
  induction r generalizing j with
  | zero => rfl
  | succ r ih =>
    have h := join0 (drainOne j r s) (ih (j+1))
    rw [show 9*(r+1)=9+9*r by omega,show j+(r+1)=j+1+r by omega]
    exact h

theorem drainEnd (j : Nat) (s : List Bool) : run0 table 9 (aCfg j 0 s) = some (bCfg (j+1) s []) := by rfl

theorem raiseFirst (j : Nat) (s : List Bool) : run0 table 12 (bCfg (j+2) s []) = some (bCfg j s (zzz ++ rep one 2)) := by rfl

theorem raiseOne (j m : Nat) (s : List Bool) : run0 table 12 (bCfg (j+2) s (zzz ++ rep one (2*m))) = some (bCfg j s (zzz ++ rep one (2*(m+1)))) := by rfl

theorem raiseAll (j k m : Nat) (s : List Bool) : run0 table (12*k) (bCfg (2*k+j) s (zzz ++ rep one (2*m))) = some (bCfg j s (zzz ++ rep one (2*(m+k)))) := by
  induction k generalizing m with
  | zero => simp [run0]
  | succ k ih =>
    have h := join0 (raiseOne (2*k+j) m s) (ih (m+1))
    rw [show 12*(k+1)=12+12*k by omega,show 2*(k+1)+j=2*k+j+2 by omega,show m+(k+1)=m+1+k by omega]
    exact h

theorem raiseOdd (n : Nat) (s : List Bool) : run0 table (12*(n+1)) (bCfg (2*(n+1)+1) s []) = some (bCfg 1 s (zzz ++ rep one (2*(n+1)))) := by
  have h := join0 (raiseFirst (2*n+1) s) (raiseAll 1 n 1 s)
  rw [show 12*(n+1)=12+12*n by omega,show 2*(n+1)+1=2*n+1+2 by omega,show n+1=1+n by omega]
  exact h

theorem raiseEven (n : Nat) (s : List Bool) : run0 table (12*(n+1)) (bCfg (2*(n+1)) s []) = some (bCfg 0 s (zzz ++ rep one (2*(n+1)))) := by
  have h := join0 (raiseFirst (2*n) s) (raiseAll 0 n 1 s)
  rw [show 12*(n+1)=12+12*n by omega,show 2*(n+1)=2*n+2 by omega]
  rw [show 2*(1+n)=2*n+2 by omega] at h
  exact h

theorem middle (n : Nat) (s : List Bool) : run0 table 25 (bCfg 1 s (zzz ++ rep one (2*(n+1)))) = some (aCfg 1 (2*(n+1)) (mark ++ s)) := by rfl

theorem finish (n : Nat) (s : List Bool) : run0 table 55 (bCfg 0 (mark ++ s) (zzz ++ rep one (2*(n+1)))) = some (aCfg 0 (2*(n+1)) (block ++ s)) := by rfl

def family (n : Nat) : Z0 := aCfg 0 (2*(n+1)) (rep block (n+1))
theorem first : run0 table 123 ⟨0,[],[]⟩ = some (family 0) := by rfl

theorem next (n : Nat) : ∃ t,0<t ∧ run0 table t (family n) = some (family (n+1)) := by
  let s := rep block (n+1)
  have a := drainAll 0 (2*(n+1)) s
  have b := drainEnd (2*(n+1)) s
  have c := raiseOdd n s
  have d := middle n s
  have e := drainAll 1 (2*(n+1)) (mark ++ s)
  have f := drainEnd (1+2*(n+1)) (mark ++ s)
  have g := raiseEven (n+1) (mark ++ s)
  have h := finish (n+1) s
  simp only [Nat.zero_add] at a
  rw [show 1+2*(n+1)+1=2*(n+1+1) by omega] at f
  have H := join0 (join0 (join0 (join0 (join0 (join0 (join0 a b) c) d) e) f) g) h
  refine ⟨60*(n+1)+110,by omega,?_⟩
  rw [show 60*(n+1)+110 = 9*(2*(n+1))+9+12*(n+1)+25+9*(2*(n+1))+9+12*(n+1+1)+55 by omega]
  exact H

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent8Raw54.never_of_returns table family 123 first next m hm
#print axioms never
end BB6.Agent8Raw54.Growth71
