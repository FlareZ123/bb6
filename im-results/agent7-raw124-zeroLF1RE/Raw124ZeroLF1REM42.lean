import BlockPump

set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw124ZeroLF1REM42
open BB6Coverage BB6Coverage.Agent50Pump BB6Coverage.Agent50Zipper

def table : PartialMachine := fun s =>
  match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨false,false,4⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,true,0⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => none
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,4⟩)
  | (4,false) => some (some ⟨true,false,0⟩)
  | (4,true) => some (some ⟨true,false,5⟩)
  | (5,false) => some (some ⟨true,true,4⟩)
  | (5,true) => some (some ⟨false,false,5⟩)
  | _ => none

def A (l r : List Bool) : HZ := ⟨0,l,r⟩
def lp : Nat → List Bool
  | 0 => []
  | n+1 => false::true::lp n
def rp : Nat → List Bool
  | 0 => []
  | n+1 => true::false::rp n

def sec (n : Nat) : HZ := A (false::lp (2*n+2)) []
def mid (n j : Nat) : HZ := A (true::true::lp (2*n+1)) (rp (2*j+1) ++ [true,true])

theorem enter (n : Nat) : hrun table 11 (sec n) = some (mid n 0) := by rfl

theorem pass (n j : Nat) : hrun table 8 (mid (n+1) j) = some (mid n (j+1)) := by
  unfold mid
  rw [show 2*(n+1)+1=2*n+1+2 by omega,show 2*(j+1)+1=2*j+1+2 by omega]
  rfl

theorem drain (n j : Nat) : hrun table (8*n) (mid n j) = some (mid 0 (j+n)) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    have h := hjoin (pass n j) (ih (j+1))
    rw [show 8+8*n=8*(n+1) by omega, show j+1+n=j+(n+1) by omega] at h
    exact h

theorem turn (n : Nat) : hrun table 10 (mid 0 n) = some (A [] (rp (2*n+4) ++ [true,true])) := by rfl

theorem stepR (j k : Nat) (R : List Bool) :
    hrun table 2 (A (false::lp j) (rp (k+1) ++ R)) = some (A (false::lp (j+1)) (rp k ++ R)) := by rfl

theorem scanR (j k : Nat) (R : List Bool) :
    hrun table (2*k) (A (false::lp j) (rp k ++ R)) = some (A (false::lp (j+k)) R) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    have h := hjoin (stepR j k R) (ih (j+1))
    rw [show 2+2*k=2*(k+1) by omega,show j+1+k=j+(k+1) by omega] at h
    exact h

theorem scanR0 (k : Nat) (R : List Bool) :
    hrun table (2*(k+1)) (A [] (rp (k+1) ++ R)) = some (A (false::lp (k+1)) R) := by
  have h0 : hrun table 2 (A [] (rp (k+1) ++ R)) = some (A (false::lp 1) (rp k ++ R)) := by rfl
  have h := hjoin h0 (scanR 1 k R)
  rw [show 2+2*k=2*(k+1) by omega,show 1+k=k+1 by omega] at h
  exact h

theorem rightEnd (k : Nat) : hrun table 2 (A (false::lp k) [true,true]) = some (A (true::lp (k+1)) []) := by rfl

theorem stepL (k j : Nat) : hrun table 2 (A (true::lp (k+1)) (rp j)) = some (A (true::lp k) (rp (j+1))) := by rfl

theorem scanL (k j : Nat) : hrun table (2*k) (A (true::lp k) (rp j)) = some (A [true] (rp (j+k))) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    have h := hjoin (stepL k j) (ih (j+1))
    rw [show 2+2*k=2*(k+1) by omega,show j+1+k=j+(k+1) by omega] at h
    exact h

theorem leftEnd (k : Nat) : hrun table 2 (A [true] (rp k)) = some (A [] (rp (k+1))) := by rfl

theorem growth (n : Nat) : hrun table (20*n+55) (sec n) = some (sec (n+2)) := by
  have h := hjoin (enter n) (drain n 0)
  rw [Nat.zero_add] at h
  have h := hjoin h (turn n)
  have h := hjoin h (scanR0 (2*n+3) [true,true])
  have h := hjoin h (rightEnd (2*n+4))
  have h := hjoin h (scanL (2*n+5) 0)
  rw [Nat.zero_add] at h
  have h := hjoin h (leftEnd (2*n+5))
  have h := hjoin h (by simpa only [List.append_nil] using scanR0 (2*n+5) [])
  have ht : 11 + 8*n + 10 + 2*(2*n+3+1) + 2 + 2*(2*n+5) + 2 + 2*(2*n+5+1) = 20*n+55 := by omega
  rw [ht] at h
  unfold sec
  rw [show 2*(n+2)+2=2*n+5+1 by omega]
  exact h

theorem root : hrun table 35 (A [] []) = some (sec 1) := by rfl

theorem arbitraryLive (n : Nat) : ∃ t k, n≤t ∧ hrun table t (A [] []) = some (sec k) := by
  induction n with
  | zero => exact ⟨35,1,by decide,root⟩
  | succ n ih =>
    obtain ⟨t,k,ht,h⟩ := ih
    exact ⟨t+(20*k+55),k+2,by omega,hjoin h (growth k)⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  intro n
  obtain ⟨k,x,hk,Hk⟩ := arbitraryLive n
  obtain ⟨h',H'⟩ := hrun_sound table k _ _ 0 Hk
  have H := zrun_sound table m hm k _ _ H'
  rw [show embed (HZ.at (A [] []) 0) = blank from blank_embed] at H
  rw [show k=n+(k-n) by omega,run_append] at H
  cases he : run m n blank with
  | none => simp [he] at H
  | some z => rfl
#print axioms never
#print axioms growth
#print axioms arbitraryLive
end BB6.Agent7Raw124ZeroLF1REM42
