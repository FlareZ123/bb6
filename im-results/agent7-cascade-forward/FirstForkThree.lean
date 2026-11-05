import FirstForkT3

namespace CascadeFirstFork
open CascadeResetInverse CascadeUniformFatal CascadeManyShield

private theorem four_n_le_pow (n:Nat) (hn:4≤n) : 4*n≤2^n := by
  have h:∀ k:Nat,4*(k+4)≤2^(k+4):=by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+4=k+4+1 by omega,Nat.pow_succ]
      omega
  have he:n=(n-4)+4:=by omega
  rw [he]
  exact h (n-4)

theorem near_top_has_three_parents (n u A:Nat) (hn:4≤n)
    (hA:3≤A) (hclose:u+A=4*2^n) (htight:64*A+164≤13*2^n)
    (hdiv:(2*u+5)%81=0) :
    ∃ a b c, a≠b ∧ a≠c ∧ b≠c ∧
      ResetParent a u ∧ ResetParent b u ∧ ResetParent c u := by
  have hsize:8*A≤5*2^n:=by omega
  have hdiv9:(2*u+5)%9=0:=by omega
  have h3:=near_top_has_tthree n u A hn hclose htight hdiv
  have h1:=odd_parent_near_top n u A hn hclose hsize hdiv9
  have he:=even_parent_near_top n u A hn hA hclose hsize
  have h4n:=four_n_le_pow n hn
  let d3:Nat:=(2*u+5)/81
  let d1:Nat:=(2*u+5)/9
  have hd3:81*d3=2*u+5:=by
    have hm:=Nat.mod_add_div (2*u+5) 81
    dsimp [d3]
    omega
  have hd1:9*d1=2*u+5:=by
    have hm:=Nat.mod_add_div (2*u+5) 9
    dsimp [d1]
    omega
  have hp3:2^n=8*2^(n-3):=by
    have hh:2^n=2^((n-3)+3):=congrArg (fun m:Nat=>2^m) (by omega)
    rw [Nat.pow_add] at hh
    omega
  have hp2:2^n=4*2^(n-2):=by
    have hh:2^n=2^((n-2)+2):=congrArg (fun m:Nat=>2^m) (by omega)
    rw [Nat.pow_add] at hh
    omega
  have hlin:n+3≤4*2^(n-2):=by
    have h:=n_plus_three_le_pow n hn
    omega
  have h3low:oddPre3 n u<2^n:=by
    dsimp [oddPre3,d3]
    omega
  have h1high:2^n<oddPre n u:=by
    dsimp [oddPre,d1]
    omega
  have hehigh:2^n<evenPre n A:=by
    dsimp [evenPre]
    omega
  have hdiff:oddPre n u≠evenPre n A:=by
    have hOddLow:oddPre n u<2*2^n:=by
      dsimp [oddPre,d1]
      omega
    have hEvenHigh:2*2^n<evenPre n A:=by
      dsimp [evenPre]
      omega
    omega
  refine ⟨oddPre3 n u,oddPre n u,evenPre n A,?_,?_,hdiff,h3,h1,he⟩
  · omega
  · omega

theorem fatal_bad_has_three_parents (n:Nat) (hn:10≤n)
    (hres:n%162=5 ∨ n%162=130) :
    ∃ a b c, a≠b ∧ a≠c ∧ b≠c ∧
      ResetParent a (fatal n) ∧ ResetParent b (fatal n) ∧
      ResetParent c (fatal n) :=
  near_top_has_three_parents n (fatal n) (n+4) (by omega)
    (by omega) (fatal_close n (by omega)) (tight_fatal n hn)
    (fatal_div81_bad n hn hres)

theorem second_bad_has_three_parents (n:Nat) (hn:10≤n)
    (hres:n%162=83 ∨ n%162=124) :
    ∃ a b c, a≠b ∧ a≠c ∧ b≠c ∧
      ResetParent a (secondPred n) ∧ ResetParent b (secondPred n) ∧
      ResetParent c (secondPred n) :=
  near_top_has_three_parents n (secondPred n) (7*n+13) (by omega)
    (by omega) (second_close n hn) (tight_second n hn)
    (second_div81_bad n hn hres)

#print axioms fatal_bad_has_three_parents
#print axioms second_bad_has_three_parents

#print axioms near_top_has_three_parents
end CascadeFirstFork
