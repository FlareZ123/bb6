import RayNoSeam
set_option maxHeartbeats 0
namespace CascadeSeam

private theorem mod_period (k:Nat): 2^(k+2)%3=2^k%3 := by
  rw [Nat.pow_add]
  simp [Nat.mul_mod]

private theorem pow_mod_three (k:Nat) :
  (k%2=0 → 2^k%3=1) ∧ (k%2=1 → 2^k%3=2) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hk:k<2
    · rcases (show k=0∨k=1 by omega) with h|h
      · subst k; decide
      · subst k; decide
    · have hprior:k-2<k:=by omega
      have h := ih (k-2) hprior
      have hper:k%2=(k-2)%2:=by omega
      have he:k=(k-2)+2:=by omega
      have hp:2^k%3=2^(k-2)%3:=by
        calc
          2^k%3=2^((k-2)+2)%3 := congrArg (fun x:Nat=>2^x%3) he
          _=2^(k-2)%3 := mod_period (k-2)
      rw [hp,hper]
      exact h

theorem source_even_residue (n:Nat) (hn:20≤n)
 (hsector:n%6=4 ∨ n%6=5) :
 (8*2^(n-4)+(n-4))%3=2 := by
  rcases hsector with hsec|hsec
  · have hpmod:2^(n-4)%3=1 :=
      (pow_mod_three (n-4)).1 (by omega)
    omega
  · have hpmod:2^(n-4)%3=2 :=
      (pow_mod_three (n-4)).2 (by omega)
    omega

theorem source_second_safe (n q d:Nat) (hn:20≤n)
  (hsector:n%6=4 ∨ n%6=5)
  (hd:d%3≠0)
  (hq:4*d=8*2^(n-4)+q+(n-4)+5) :
  q%3≠2 ∧ (8*2^(n-4)+(n-4))%3=2 := by
  have he:=source_even_residue n hn hsector
  exact ⟨by omega,he⟩

theorem valuation_not_three (w d:Nat)
 (hw:2*w+5=9*d) (hmod:(2*w+5)%27≠0) :d%3≠0 :=by
 omega

#print axioms source_even_residue
#print axioms source_second_safe
#print axioms valuation_not_three
end CascadeSeam
