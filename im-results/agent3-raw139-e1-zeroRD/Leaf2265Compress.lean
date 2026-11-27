import Leaf2265Core
namespace BB6.Agent3Leaf2265
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem one0010 (k : Nat) (r : Ray) :
    Runs (8*k+20) (S k (pre [false,false,true,false] r)) (S (k+4) r) := by
  have h : Runs (4*k+10) (S k (pre [false,false,true,false] r))
      (S (k+1) (pre P (pre [true,true] r))) := by
    have h0 := ret1 k 0 r
    simp only [Nat.mul_zero,Nat.add_zero] at h0
    exact h0
  rw [S_push] at h
  have j := one (k+2) (cons true r)
  have g := chain h j
  have he : S (k+2+1) (cons false (cons true r)) = S (k+4) r := by
    change S (k+3) (pre P r) = _
    rw [S_push]
  rw [he] at g
  simpa only [show 4*k+10+(4*(k+2)+2)=8*k+20 by omega] using g

theorem pairStep (a b : Nat) (r : Ray) :
    Runs (12*a+38) (S a (cons false (rep P (b+2) r)))
      (S (a+5) (cons false (rep P b r))) := by
  have h : Runs (8*a+20) (S a (cons false (rep P (b+2) r)))
      (S (a+4) (cons true (rep P b r))) := one0010 a _
  have g := chain h (one (a+4) (rep P b r))
  simpa only [show 8*a+20+(4*(a+4)+2)=12*a+38 by omega] using g

theorem pairIter (t a b : Nat) (r : Ray) :
    Runs (12*a*t+30*t*t+8*t) (S a (cons false (rep P (2*t+b) r)))
      (S (a+5*t) (cons false (rep P b r))) := by
  induction t generalizing a with
  | zero => simp only [Nat.mul_zero,Nat.zero_add,Nat.add_zero]; rfl
  | succ t ih =>
    have h := pairStep a (2*t+b) r
    have g := chain h (ih (a+5))
    have hn : 2*(t+1)+b=2*t+b+2 := by omega
    have ha : a+5*(t+1)=a+5+5*t := by omega
    have hc : 12*a*(t+1)+30*(t+1)*(t+1)+8*(t+1) =
        12*a+38+(12*(a+5)*t+30*t*t+8*t) := by
      simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_one,Nat.one_mul]
      omega
    rw [hn,ha,hc]
    exact g

theorem drain (t b : Nat) (r : Ray) :
    Runs (6+30*t*t+32*t) (S 0 (pre [false,true,true] (rep P (2*t+b) r)))
      (S (2+5*t) (cons false (rep P b r))) := by
  have h := one 1 (rep P (2*t+b) r)
  have j := pairIter t 2 b r
  have g := chain h j
  have hc : 6+(12*2*t+30*t*t+8*t)=6+30*t*t+32*t := by omega
  rw [← hc]
  exact g

theorem drainOdd (t : Nat) (r : Ray) :
    Runs (6+30*t*t+32*t+(8*(2+5*t)+20))
      (S 0 (pre [false,true,true] (rep P (2*t+1) (cons false r))))
      (S (2+5*t+4) r) := by
  have h := drain t 1 (cons false r)
  have j := one0010 (2+5*t) r
  exact chain h j

#print axioms one0010
#print axioms pairIter
#print axioms drainOdd
end BB6.Agent3Leaf2265
