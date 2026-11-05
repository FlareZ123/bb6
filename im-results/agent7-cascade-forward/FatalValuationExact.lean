import FatalValuationBeyond
set_option maxHeartbeats 0
namespace CascadeFatalValuation
open CascadeManyShield CascadeFirstFork

/-- Exact additive displacement of fatal-index odd inverse numerators under one 3-adic lifting stride. -/
theorem fatal_shift_balance (k n j:Nat) (hn:4≤n):
  ∃m:Nat, (2*fatal (n+2*3^k*j)+5)+4*3^k*j =
    (2*fatal n+5)+3*3^k*m*(8*2^n) := by
  let P:Nat:=3^k
  let nn:Nat:=n+2*P*j
  let z:Nat:=2*fatal n+5
  obtain ⟨m,hm⟩:=pow_offset k j
  have hnnew:4≤nn:=by dsimp [nn]; omega
  have hclose0:z+2*n+3=8*2^n:=by
    have hc:=fatal_close n hn
    dsimp [z]
    omega
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
      _ = 8*2^n+3*P*m*(8*2^n):=by
        simp only [Nat.mul_add, Nat.mul_one]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hstep:(2*fatal nn+5)+4*P*j=z+3*P*m*(8*2^n):=by
    have hscaled:4*P*j=2*(2*P*j):=by
      simp only [Nat.mul_assoc]
      omega
    have hnnlin:2*nn=2*n+4*P*j:=by
      dsimp [nn]
      rw [Nat.mul_add,←hscaled]
    omega
  exact ⟨m,by simpa [P,nn,z] using hstep⟩

/-- Exactly one of the three 3-adic lifts succeeds. The successful lift is determined by the current quotient modulo three. -/
theorem fatal_shift_exact (k n j:Nat) (hn:4≤n)
  (hdiv:(2*fatal n+5)%3^k=0) (hj:j<3):
  ((2*fatal (n+2*3^k*j)+5)%3^(k+1)=0 ↔
    j=((2*fatal n+5)/3^k)%3) := by
  let P:Nat:=3^k
  let z:Nat:=2*fatal n+5
  let z':Nat:=2*fatal (n+2*P*j)+5
  let x:Nat:=8*2^n
  have hp:0<P:=by dsimp [P]; exact Nat.pow_pos (by decide)
  have hzmod:z%P=0:=hdiv
  obtain ⟨m,hstep⟩:=fatal_shift_balance k n j hn
  have hstep':z'+P*(4*j)=z+P*(3*(m*x)):=by
    dsimp [P,z,z',x]
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hstep
  have hz'mod:z'%P=0:=by
    have hh:=congrArg (fun t:Nat=>t%P) hstep'
    simpa [Nat.add_mod,Nat.mul_mod,hzmod] using hh
  have hzfac:P*(z/P)=z:=Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hzmod)
  have hz'fac:P*(z'/P)=z':=Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hz'mod)
  have hrel:z'/P+4*j=z/P+3*(m*x):=by
    apply Nat.mul_left_cancel hp
    calc
      P*(z'/P+4*j)=z'+P*(4*j):=by rw [Nat.mul_add,hz'fac]
      _ = z+P*(3*(m*x)):=hstep'
      _ = P*(z/P+3*(m*x)):=by rw [Nat.mul_add,hzfac]
  have hfac_big:(3*P∣z') ↔ (3∣z'/P):=by
    have hh := (Nat.mul_dvd_mul_iff_right hp (a:=3) (b:=z'/P))
    simpa only [Nat.mul_comm, hz'fac] using hh
  have hbig:(z' % (3*P)=0) ↔ (z'/P)%3=0:=by
    constructor
    · intro hb
      exact Nat.mod_eq_zero_of_dvd (hfac_big.mp (Nat.dvd_of_mod_eq_zero hb))
    · intro hb
      exact Nat.mod_eq_zero_of_dvd (hfac_big.mpr (Nat.dvd_of_mod_eq_zero hb))
  have hmod3:((z'/P)%3=0 ↔ j=(z/P)%3):=by omega
  have hpow:3^(k+1)=3*P:=by dsimp [P];rw [Nat.pow_succ];omega
  rw [hpow]
  exact hbig.trans hmod3

/-- Every index in a lift triple retains divisibility by the original power 3^k. -/
theorem fatal_shift_keeps_divisibility (k n j:Nat) (hn:4≤n)
  (hdiv:(2*fatal n+5)%3^k=0):
  (2*fatal (n+2*3^k*j)+5)%3^k=0:=by
  let P:Nat:=3^k
  let z:Nat:=2*fatal n+5
  let z':Nat:=2*fatal (n+2*P*j)+5
  let x:Nat:=8*2^n
  obtain ⟨m,hstep⟩:=fatal_shift_balance k n j hn
  have hstep':z'+P*(4*j)=z+P*(3*(m*x)):=by
    dsimp [P,z,z',x]
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hstep
  have hmod:=congrArg (fun t:Nat=>t%P) hstep'
  have hzmod:z%P=0:=hdiv
  have hzero:z'%P=0:=by simpa [Nat.add_mod,Nat.mul_mod,hzmod] using hmod
  exact hzero

/-- Exactly one of three adjacent 2*3^k index lifts is divisible by 3^(k+1). -/
theorem fatal_unique_3adic_digit (k n:Nat) (hn:4≤n)
  (hdiv:(2*fatal n+5)%3^k=0):
  ∃j:Nat,j<3 ∧
    (2*fatal (n+2*3^k*j)+5)%3^(k+1)=0 ∧
    ∀l:Nat,l<3 →
      (2*fatal (n+2*3^k*l)+5)%3^(k+1)=0 → l=j:=by
  let j:Nat:=((2*fatal n+5)/3^k)%3
  have hj:j<3:=by dsimp [j]; exact Nat.mod_lt _ (by decide)
  have hh:(2*fatal (n+2*3^k*j)+5)%3^(k+1)=0:=
    (fatal_shift_exact k n j hn hdiv hj).mpr rfl
  refine ⟨j,hj,hh,?_⟩
  intro l hl hsuccess
  have hlift: l=j :=(fatal_shift_exact k n l hn hdiv hl).mp hsuccess
  exact hlift

theorem fatal_nonmatching_digit (k n j:Nat) (hn:4≤n)
  (hdiv:(2*fatal n+5)%3^k=0) (hj:j<3)
  (hne:j≠((2*fatal n+5)/3^k)%3):
  (2*fatal (n+2*3^k*j)+5)%3^(k+1)≠0:=by
  intro hzero
  exact hne ((fatal_shift_exact k n j hn hdiv hj).mp hzero)

/-- A base index with one extra factor of three has a nearby index of exact valuation k, in the same residue class modulo six. -/
theorem fatal_exact_digit_near (k n:Nat) (hk:1≤k) (hn:4≤n)
  (hdiv:(2*fatal n+5)%3^(k+1)=0):
  (n+2*3^k)%6=n%6 ∧
  (2*fatal (n+2*3^k)+5)%3^k=0 ∧
  (2*fatal (n+2*3^k)+5)%3^(k+1)≠0:=by
  have hpow:3^(k+1)=3*3^k:=by rw [Nat.pow_succ];omega
  have hsmall:(2*fatal n+5)%3^k=0:=by
    have hd:3^(k+1)∣2*fatal n+5:=Nat.dvd_of_mod_eq_zero hdiv
    have hpart:3^k∣3^(k+1):=by
      refine ⟨3,?_⟩
      rw [hpow]
      omega
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hpart hd)
  have hquot:((2*fatal n+5)/3^k)%3=0:=by
    have hh:=(fatal_shift_exact k n 0 hn hsmall (by decide)).mp
      (by simpa using hdiv)
    simpa using hh.symm
  have hm: (2*fatal (n+2*3^k)+5)%3^k=0:=by
    simpa using fatal_shift_keeps_divisibility k n 1 hn hsmall
  have hnot:(2*fatal (n+2*3^k)+5)%3^(k+1)≠0:=by
    have hne:(1:Nat)≠((2*fatal n+5)/3^k)%3:=by omega
    simpa using fatal_nonmatching_digit k n 1 hn hsmall (by decide) hne
  have hkexp:3^k=3*3^(k-1):=by
    have he:k=(k-1)+1:=by omega
    calc
      3^k = 3^((k-1)+1) := congrArg (fun t:Nat=>3^t) he
      _ = 3^(k-1)*3 := Nat.pow_succ 3 (k-1)
      _ = 3*3^(k-1) := by omega
  have hres:(n+2*3^k)%6=n%6:=by
    rw [hkexp]
    omega
  exact ⟨hres,hm,hnot⟩

/-- Arbitrarily high indices in both surviving classes have any specified exact positive 3-adic valuation. -/
theorem fatal_exact_valuation_four (N k:Nat) (hk:1≤k):
  ∃n:Nat,N<n ∧ n%6=4 ∧
    (2*fatal n+5)%3^k=0 ∧
    (2*fatal n+5)%3^(k+1)≠0:=by
  obtain ⟨n,hn,hres,hdiv⟩:=fatal_high_val_above_four N k
  obtain ⟨hperiod,hsmall,hnot⟩:=fatal_exact_digit_near k n hk (by omega) hdiv
  exact ⟨n+2*3^k,(by omega),(by rw [hperiod,hres]),hsmall,hnot⟩

theorem fatal_exact_valuation_five (N k:Nat) (hk:1≤k):
  ∃n:Nat,N<n ∧ n%6=5 ∧
    (2*fatal n+5)%3^k=0 ∧
    (2*fatal n+5)%3^(k+1)≠0:=by
  obtain ⟨n,hn,hres,hdiv⟩:=fatal_high_val_above_five N k
  obtain ⟨hperiod,hsmall,hnot⟩:=fatal_exact_digit_near k n hk (by omega) hdiv
  exact ⟨n+2*3^k,(by omega),(by rw [hperiod,hres]),hsmall,hnot⟩

#print axioms fatal_exact_digit_near
#print axioms fatal_exact_valuation_four
#print axioms fatal_exact_valuation_five
#print axioms fatal_shift_keeps_divisibility
#print axioms fatal_unique_3adic_digit
#print axioms fatal_nonmatching_digit
#print axioms fatal_shift_balance
#print axioms fatal_shift_exact
end CascadeFatalValuation
