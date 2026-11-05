import FatalValuationPower
set_option maxHeartbeats 0

namespace CascadeFatalValuation
open CascadeFirstFork CascadeManyShield

private theorem three_mod_zero (z q j w:Nat) (h:z+q*j=q*w) : z%q=0 := by
  have hm:(z+q*j)%q=0:=by
    rw [h,Nat.mul_mod]
    simp
  simpa [Nat.add_mod,Nat.mul_mod] using hm

private theorem generic_lift (P w j m x z':Nat)
   (h:z'+4*P*j=P*(3*w+j)+3*P*m*x):
   z'+3*P*j=3*P*(w+m*x) :=by
  have hpw : P*(3*w)=3*(P*w):=by simp only [Nat.mul_assoc,Nat.mul_comm]
  simp only [Nat.mul_add,Nat.mul_assoc] at h ⊢
  rw [hpw] at h
  omega

private theorem mul_cong (a P m:Nat):
    a*(1+3*P*m)=a+3*P*m*a:=by
  simp only [Nat.mul_add,Nat.mul_comm,Nat.mul_left_comm]
  ac_rfl

/-- If 3^k divides a fatal-index odd inverse numerator, one of the three
    lifts n + 2·3^k·j, j=0,1,2, has numerator divisible by 3^(k+1).
    For k>=1 the candidate index's residue modulo six is preserved. -/
theorem fatal_valuation_lift (k n:Nat) (hk:1≤k) (hn:4≤n)
  (hdiv:(2*fatal n+5)%3^k=0):
  ∃n',n≤n' ∧ n'%6=n%6 ∧ (2*fatal n'+5)%3^(k+1)=0:=by
  let P:Nat:=3^k
  let z:Nat:=2*fatal n+5
  let v:Nat:=z/P
  let j:Nat:=v%3
  let w:Nat:=v/3
  let nn:Nat:=n+2*P*j
  obtain ⟨m,hm⟩:=pow_offset k j
  have hdiv0:P*v=z:=by
    have hmod:=Nat.mod_add_div z P
    dsimp [P,z,v] at *
    omega
  have hquot:v=3*w+j:=by
    have hmod:=Nat.mod_add_div v 3
    dsimp [w,j]
    omega
  have hclose0:z+2*n+3=8*2^n:=by
    have hc:=fatal_close n hn
    dsimp [z]
    omega
  have hnnew:4≤nn:=by dsimp [nn];omega
  have hclose1:2*fatal nn+5+2*nn+3=8*2^nn:=by
    have hc:=fatal_close nn hnnew
    omega
  have hpow:2^nn=2^n*(1+3*P*m):=by
    dsimp [nn]
    rw [Nat.pow_add]
    have he:2*P*j=2*3^k*j:=by rfl
    rw [he,hm]
  have hmult:8*2^nn=8*2^n+3*P*m*(8*2^n):=by
    calc
      8*2^nn=(8*2^n)*(1+3*P*m):=by rw [hpow,←Nat.mul_assoc]
      _ = 8*2^n+3*P*m*(8*2^n) := mul_cong (8*2^n) P m
  have hstep:(2*fatal nn+5)+4*P*j=z+3*P*m*(8*2^n):=by
    have hscaled:4*P*j=2*(2*P*j):=by
      simp only [Nat.mul_assoc]
      omega
    have hnnlin:2*nn=2*n+4*P*j:=by
      dsimp [nn]
      rw [Nat.mul_add,←hscaled]
    omega
  have hstep0:(2*fatal nn+5)+4*P*j=P*(3*w+j)+3*P*m*(8*2^n):=by
    rw [←hdiv0,hquot] at hstep
    exact hstep
  have hfinal:(2*fatal nn+5)+3*P*j=3*P*(w+m*(8*2^n)):=
    generic_lift P w j m (8*2^n) (2*fatal nn+5) hstep0
  have hzero:(2*fatal nn+5)%(3*P)=0:=three_mod_zero _ _ j _ hfinal
  have hP:3^(k+1)=3*P:=by
    dsimp [P]
    rw [Nat.pow_succ]
    omega
  have hperiod:n%6=nn%6:=by
    have he:k=(k-1)+1:=by omega
    have heP:P=3*3^(k-1):=by
      have hpowstep:3^k=3^((k-1)+1):=
        congrArg (fun t:Nat=>3^t) (by omega)
      dsimp [P]
      rw [hpowstep,Nat.pow_succ]
      omega
    have hnn:nn=n+6*(3^(k-1)*j):=by
      dsimp [nn]
      rw [heP]
      have hf:2*(3*3^(k-1))*j=6*(3^(k-1)*j):=by
        simp only [Nat.mul_assoc]
        omega
      rw [hf]
    rw [hnn]
    omega
  exact ⟨nn,(by dsimp[nn];omega),hperiod.symm,(by rw [hP];exact hzero)⟩

/-- Arbitrarily high 3-adic valuations occur among fatal candidate
    indices n=4 (mod 6), without a finite valuation cutoff. -/
theorem fatal_unbounded_3adic_four (k:Nat):
  ∃n:Nat,4≤n ∧ n%6=4 ∧ (2*fatal n+5)%3^(k+1)=0 :=by
  induction k with
  | zero=>exact ⟨4,by decide,by decide,by decide⟩
  | succ k ih=>
    obtain ⟨n,hn,hres,hdiv⟩:=ih
    obtain ⟨n',hnmon,hres2,hdiv2⟩:=
      fatal_valuation_lift (k+1) n (by omega) hn hdiv
    exact ⟨n',(by omega),(by rw [hres2,hres]),hdiv2⟩

/-- The other true fatal candidate index class n=5 (mod 6) likewise
    contains numerators divisible by arbitrarily high powers of three. -/
theorem fatal_unbounded_3adic_five (k:Nat):
  ∃n:Nat,5≤n ∧ n%6=5 ∧ (2*fatal n+5)%3^(k+1)=0 :=by
  induction k with
  | zero=>exact ⟨5,by decide,by decide,by decide⟩
  | succ k ih=>
    obtain ⟨n,hn,hres,hdiv⟩:=ih
    obtain ⟨n',hnmon,hres2,hdiv2⟩:=
      fatal_valuation_lift (k+1) n (by omega) (by omega) hdiv
    exact ⟨n',(by omega),(by rw [hres2,hres]),hdiv2⟩

#print axioms fatal_valuation_lift
#print axioms fatal_unbounded_3adic_four
#print axioms fatal_unbounded_3adic_five
end CascadeFatalValuation
