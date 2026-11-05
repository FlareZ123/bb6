import FirstForkFatalThree
set_option maxHeartbeats 0

namespace CascadeFirstFork
open CascadeResetInverse CascadeUniformFatal CascadeManyShield

/-- The exact valuation-six odd reset predecessor. -/
def oddPre6 (n u : Nat) : Nat :=
  128*((2*u+5)/2187)-8*2^(n-5)-(n-5)-5

theorem sixth_linear (n:Nat) (hn:10≤n) :
    n+3 ≤ 4*2^(n-5) := by
  have h : ∀ k:Nat, k+13 ≤ 4*2^(k+5) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+5=k+5+1 by omega,Nat.pow_succ]
      omega
  have he:n=(n-10)+10 := by omega
  have hh:=h (n-10)
  rw [he]
  have hk : (n-10+10)-5=(n-10)+5 := by omega
  rw [hk]
  omega

/-- Under the near-top dyadic bound, a divisor 3^7 of 2*u+5
    supplies a genuine odd valuation-six first-reset predecessor.
    It is a source-level predecessor, not a reached blank-root state. -/
theorem near_top_has_tsix (n u A:Nat) (hn:10≤n)
    (hclose:u+A=4*2^n) (htight:64*A+164≤13*2^n)
    (hdiv:(2*u+5)%2187=0) :
    ResetParent (oddPre6 n u) u := by
  let d : Nat := (2*u+5)/2187
  have hd:2187*d=2*u+5 := by
    have hm:=Nat.mod_add_div (2*u+5) 2187
    dsimp [d]
    omega
  have hodd:d%2=1:=by omega
  have hp:2^n=32*2^(n-5):=by
    have he:2^n=2^((n-5)+5):=congrArg (fun m:Nat=>2^m) (by omega)
    rw [Nat.pow_add] at he
    omega
  have hlarge:1024≤2^n:=by
    have he:2^10≤2^n:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) hn
    exact he
  have hb0 : 2187*(64*d)+128*A=512*2^n+320 := by omega
  have hlo:6*2^(n-5)+1≤64*d := by omega
  have hhi:64*d≤8*2^(n-5)-1 := by omega
  have hlinear := sixth_linear n hn
  have heq:2*(64*d)=8*2^(n-5)+oddPre6 n u+(n-5)+5 := by
    dsimp [oddPre6, d]
    omega
  have hout:2*u+5=3^(6+1)*d := by
    have he:3^(6+1)=2187:=by decide
    rw [he]
    omega
  have hpow:2^6=64:=by decide
  exact Or.inr ⟨n-5,6,d,hodd,
    (by simpa [hpow] using (show 6*2^(n-5)+1 ≤ 64*d ∧
      64*d ≤ 8*2^(n-5)-1 from ⟨hlo,hhi⟩)),hout,
    (by simpa [hpow] using heq)⟩

#print axioms near_top_has_tsix
end CascadeFirstFork
