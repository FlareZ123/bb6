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
  have hn_eq : n=(n-1)+1 := by omega
  have hexists : ∃ a b, BB429Burst.firstRun n (0,W)=some (a,b) := by
    rw [hn_eq, BB429Burst.prefix_exists_iff 0 W (n-1)]
    exact hcond
  rcases hexists with ⟨a,b,hp⟩
  have hprefix : BB429.run n (0,W)=some (a,b) :=
    BB429DyadicStarts.first_prefix_is_source (0,W) (a,b) n hp
  have hformula := BB429Burst.prefix_formula 0 W n a b hp
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


/-- Iteration of the affine return map gives a long exact zero-row block. -/
theorem even_burst_affine_iter (n W k : Nat)
    (hn : n%4=2) (hW : W%4=0)
    (hlo : 6*2^n ≤ W+3*n+6)
    (hhi : W+k*(3*n+10)+3*n+18 ≤ 12*2^n) :
    BB429.run (k*(n+1)) (0,W)=some (0,W+k*(3*n+10)) := by
  induction k with
  | zero =>
    simp [BB429.run]
  | succ k ih =>
    have hc : (3*n+10)%4=0 := by omega
    have hWk : (W+k*(3*n+10))%4=0 := by
      rw [Nat.add_mod, Nat.mul_mod, hW, hc]
      simp
    have hlo_k : 6*2^n ≤ (W+k*(3*n+10))+3*n+6 := by omega
    have hhi_k : (W+k*(3*n+10))+3*n+18 ≤ 12*2^n := by
      have hhi' : W+(k*(3*n+10)+(3*n+10))+3*n+18 ≤ 12*2^n := by
        simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hhi
      omega
    have hstep := even_burst_affine_return n (W+k*(3*n+10)) hn hWk hlo_k hhi_k
    have hprev := ih hhi_k
    rw [Nat.succ_mul, BB429.run_add]
    simp [hprev,hstep]
    have hmul : (k+1)*(3*n+10)=k*(3*n+10)+(3*n+10) := by
      simpa [Nat.succ_eq_add_one] using (Nat.succ_mul k (3*n+10))
    rw [hmul]
    omega

/-- The n=22 affine block is an exact 7,615,921-step source segment,
conditional only on its displayed entry state. -/
theorem n22_zero_row_segment (k : Nat) (hk : k≤331127) :
    BB429.run (k*23) (0,25165912)=some (0,25165912+76*k) := by
  have hn : 22%4=2 := by decide
  have hW : 25165912%4=0 := by decide
  have hpow : 2^22=4194304 := by decide
  have hlo : 6*2^22≤25165912+3*22+6 := by rw [hpow]; omega
  have hmul : 331127*76=25165652 := by decide
  have hbound : k*76≤25165652 := by
    calc
      k*76≤331127*76 := Nat.mul_le_mul_right 76 hk
      _=25165652 := hmul
  have hhi : 25165912+k*(3*22+10)+3*22+18≤12*2^22 := by
    rw [show 3*22+10=76 by decide, show 3*22+18=84 by decide, hpow]
    omega
  simpa [show 22+1=23 by decide,
    show 3*22+10=76 by decide, Nat.mul_comm] using
      even_burst_affine_iter 22 25165912 k hn hW hlo hhi

theorem n22_zero_row_block_end :
    BB429.run (331127*23) (0,25165912)=some (0,50331564) := by
  have h := n22_zero_row_segment 331127 (by omega)
  have hval : 25165912+76*331127=50331564 := by decide
  simpa [hval] using h

#print axioms even_burst_affine_return
#print axioms even_burst_affine_iter
#print axioms n22_zero_row_segment
#print axioms n22_zero_row_block_end

end Agent6AffineReturn
