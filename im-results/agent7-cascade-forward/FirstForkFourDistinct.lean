import FirstForkExactFour
set_option maxHeartbeats 0

namespace CascadeFirstFork
open CascadeResetInverse CascadeUniformFatal

/-- The four explicit near-top inverse parents are strictly ordered.
    The proof itself is arithmetic and uses only previously proved
    dyadic growth lemmas; the inverse grammar is not needed here. -/
theorem four_parents_strict_order (n u A:Nat) (hn:10≤n)
    (hA:3≤A) (hclose:u+A=4*2^n)
    (htight:64*A+164≤13*2^n)
    (hdiv:(2*u+5)%2187=0) :
    oddPre6 n u < oddPre3 n u ∧ oddPre3 n u < oddPre n u ∧
    oddPre n u < evenPre n A := by
  let d1:Nat:=(2*u+5)/9
  let d3:Nat:=(2*u+5)/81
  let d6:Nat:=(2*u+5)/2187
  have hd1:9*d1=2*u+5:=by
    have hm:=Nat.mod_add_div (2*u+5) 9
    dsimp [d1]
    omega
  have hd3:81*d3=2*u+5:=by
    have hm:=Nat.mod_add_div (2*u+5) 81
    dsimp [d3]
    omega
  have hd6:2187*d6=2*u+5:=by
    have hm:=Nat.mod_add_div (2*u+5) 2187
    dsimp [d6]
    omega
  have hp32:2^n=32*2^(n-5) := by
    have hh:2^n=2^((n-5)+5):=congrArg (fun m:Nat=>2^m) (by omega)
    rw [Nat.pow_add] at hh
    omega
  have hp8:2^n=8*2^(n-3) := by
    have hh:2^n=2^((n-3)+3):=congrArg (fun m:Nat=>2^m) (by omega)
    rw [Nat.pow_add] at hh
    omega
  have hp4:2^n=4*2^(n-2) := by
    have hh:2^n=2^((n-2)+2):=congrArg (fun m:Nat=>2^m) (by omega)
    rw [Nat.pow_add] at hh
    omega
  have hlin:=sixth_linear n hn
  have hlarge:1024≤2^n := by
    have hh:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) hn
    exact hh
  have hsize:8*A≤5*2^n:=by omega
  have hdiv81:(2*u+5)%81=0:=by omega
  have hdiv9:(2*u+5)%9=0:=by omega
  have hscale6 : 6*2^(n-5)+1≤64*d6 ∧ 64*d6≤8*2^(n-5)-1 := by
    constructor <;> omega
  have hscale3 : 6*2^(n-3)+1≤8*d3 ∧ 8*d3≤8*2^(n-3)-1 := by
    constructor <;> omega
  have hscale1 : 6*2^(n-2)+1≤2*d1 ∧ 2*d1≤8*2^(n-2)-1 := by
    constructor <;> omega
  have h6low:oddPre6 n u<8*2^(n-5) := by
    dsimp [oddPre6,d6]
    omega
  have h3high:8*2^(n-5)<oddPre3 n u := by
    dsimp [oddPre3,d3]
    omega
  have h3low:oddPre3 n u<2^n := by
    dsimp [oddPre3,d3]
    omega
  have h1high:2^n<oddPre n u := by
    dsimp [oddPre,d1]
    omega
  have h1low:oddPre n u<2*2^n := by
    dsimp [oddPre,d1]
    omega
  have hehigh:2*2^n<evenPre n A := by
    have h2:=two_n_le_pow n (by omega)
    dsimp [evenPre]
    omega
  omega

#print axioms four_parents_strict_order
end CascadeFirstFork
