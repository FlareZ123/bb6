import FirstFork162

namespace CascadeFirstFork
open CascadeResetInverse CascadeUniformFatal CascadeManyShield

def oddPre3 (n u:Nat) : Nat :=
  2*(8*((2*u+5)/81))-8*2^(n-3)-(n-3)-5

theorem near_top_has_tthree (n u A:Nat) (hn:4≤n)
    (hclose:u+A=4*2^n) (htight:64*A+164≤13*2^n)
    (hdiv:(2*u+5)%81=0) :
    ResetParent (oddPre3 n u) u := by
  let d := (2*u+5)/81
  have hd:81*d=2*u+5:=by
    have hm:=Nat.mod_add_div (2*u+5) 81
    dsimp [d]
    omega
  have hodd:d%2=1:=by omega
  have hp:2^n=8*2^(n-3):=by
    have he:2^n=2^((n-3)+3):=congrArg (fun m:Nat=>2^m) (by omega)
    rw [Nat.pow_add] at he
    omega
  have hlarge:16≤2^n:=by
    have he:2^4≤2^n:=Nat.pow_le_pow_right (by decide) hn
    exact he
  have hlow : 6*2^(n-3)+1≤8*d := by omega
  have hhigh:8*d≤8*2^(n-3)-1 := by omega
  have hlinear:n≤4*2^(n-3) := by
    have h2n:=two_n_le_pow n hn
    omega
  have heq:2*(8*d)=8*2^(n-3)+oddPre3 n u+(n-3)+5 := by
    dsimp [oddPre3,d]
    omega
  have hout:2*u+5=3^(3+1)*d := by
    have he:3^(3+1)=81:=by decide
    rw [he]
    omega
  exact Or.inr ⟨n-3,3,d,hodd,⟨hlow,hhigh⟩,hout,heq⟩

#print axioms near_top_has_tthree
end CascadeFirstFork
