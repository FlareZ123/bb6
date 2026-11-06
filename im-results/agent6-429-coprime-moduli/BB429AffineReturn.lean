import Lean.Elab.Tactic.Omega
import BB429Rank
import BB429Burst
import BB429DyadicStarts

namespace Agent6AffineReturn

open BB429

/-- A complete source return after an even-length first burst. If n=2 mod 4,
the first n steps are taken and the next even/d-odd branch returns to the
zero row with an affine increment 3n+10. -/
theorem even_burst_affine_return (n W : Nat)
    (hn : n%4=2) (hW : W%4=0)
    (hlo : 6*2^n ≤ W+3*n+6)
    (hhi : W+3*n+18 ≤ 12*2^n) :
    BB429.run (n+1) (0,W)=some (0,W+3*n+10) := by
  have hn1 : 1≤n := by omega
  have hn2 : 2≤n := by omega
  have hpow : 2^n=2^(n-1)*2 := by
    calc
      2^n=2^((n-1)+1) := by congr 1 <;> omega
      _=2^(n-1)*2 := by rw [Nat.pow_succ]
  have hnsub : n-1+1=n := by omega
  have hpow' : 12*2^(n-1)=6*2^n := by
    calc
      12*2^(n-1)=6*(2^(n-1)*2) := by omega
      _=6*2^n := by rw [←hpow]
  have hcond :
      4*((0+3)*2^(n-1)) ≤ 2*0+W+3*(n-1)+9 := by
    omega
  have hnon : BB429Burst.firstRun n (0,W) ≠ none := by
    rw [BB429Burst.prefix_exists_iff]
    exact ⟨hn1,hcond⟩
  rcases Option.ne_none_iff_exists'.mp hnon with ⟨p,hp⟩
  rcases p with ⟨a,b⟩
  have hprefix : BB429.run n (0,W)=some (a,b) :=
    BB429DyadicStarts.first_prefix_is_source n 0 W a b hp
  have hformula := BB429Burst.prefix_formula n 0 W a b hp
  have ha : a+3=3*2^n := by simpa using hformula.1
  have hab : 2*a+b=W+3*n := by simpa using hformula.2
  have hpow4 : 2^n%4=0 := by
    have hn' : n=(n-2)+2 := by omega
    rw [hn', Nat.pow_add]
    simp
  have ha4 : a%4=1 := by omega
  have hb4 : b%4=0 := by omega
  have hb2 : b%2=0 := by omega
  have hbound : b+6≤2*a := by omega
  have hdge : 3≤a-b/2 := by omega
  have hdne : a-b/2≠1 := by omega
  have hdodd : (a-b/2)%2≠0 := by omega
  have hnotfirst : ¬ b≥2*a+3 := by omega
  have hne2 : b≠2*a+2 := by omega
  have hne1 : b≠2*a+1 := by omega
  have hne0 : b≠2*a := by omega
  have hnext : BB429.next (a,b)=some (0,W+3*n+10) := by
    simp [BB429.next,hnotfirst,hne2,hne1,hne0,hb2,hdne,hdodd,hab]
  rw [BB429.run_add]
  simp [hprefix,BB429.run,hnext]

end Agent6AffineReturn
