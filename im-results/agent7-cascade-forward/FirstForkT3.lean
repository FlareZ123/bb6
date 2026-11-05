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

theorem tight_fatal (n:Nat) (hn:10≤n) :
    64*(n+4)+164≤13*2^n := by
  have h:∀ k:Nat,64*(k+10+4)+164≤13*2^(k+10):=by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+10=k+10+1 by omega,Nat.pow_succ]
      omega
  have he:n=(n-10)+10:=by omega
  rw [he]
  exact h (n-10)

theorem tight_second (n:Nat) (hn:10≤n) :
    64*(7*n+13)+164≤13*2^n := by
  have h:∀ k:Nat,64*(7*(k+10)+13)+164≤13*2^(k+10):=by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+10=k+10+1 by omega,Nat.pow_succ]
      omega
  have he:n=(n-10)+10:=by omega
  rw [he]
  exact h (n-10)

theorem fatal_div81_bad (n:Nat) (hn:10≤n)
    (hres:n%162=5 ∨ n%162=130) :
    (2*fatal n+5)%81=0 := by
  have hf:=fatal_close n (by omega)
  have hp:=pow_mod_fiftyfour n
  rcases hres with h|h
  · have hm:n%54=5:=by omega
    have hm81:2^n%81=2^5%81:=by rw [hp,hm]
    omega
  · have hm:n%54=22:=by omega
    have hm81:2^n%81=2^22%81:=by rw [hp,hm]
    omega

theorem second_div81_bad (n:Nat) (hn:10≤n)
    (hres:n%162=83 ∨ n%162=124) :
    (2*secondPred n+5)%81=0 := by
  have hf:=second_close n hn
  have hp:=pow_mod_fiftyfour n
  rcases hres with h|h
  · have hm:n%54=29:=by omega
    have hm81:2^n%81=2^29%81:=by rw [hp,hm]
    omega
  · have hm:n%54=16:=by omega
    have hm81:2^n%81=2^16%81:=by rw [hp,hm]
    omega

theorem fatal_bad_has_tthree (n:Nat) (hn:10≤n)
    (hres:n%162=5 ∨ n%162=130) :
    ResetParent (oddPre3 n (fatal n)) (fatal n) :=
  near_top_has_tthree n (fatal n) (n+4) (by omega)
    (fatal_close n (by omega)) (tight_fatal n hn)
    (fatal_div81_bad n hn hres)

theorem second_bad_has_tthree (n:Nat) (hn:10≤n)
    (hres:n%162=83 ∨ n%162=124) :
    ResetParent (oddPre3 n (secondPred n)) (secondPred n) :=
  near_top_has_tthree n (secondPred n) (7*n+13) (by omega)
    (second_close n hn) (tight_second n hn)
    (second_div81_bad n hn hres)

#print axioms fatal_bad_has_tthree
#print axioms second_bad_has_tthree

#print axioms near_top_has_tthree
end CascadeFirstFork
