import Lean
namespace BB6.Agent43ForwardBlock

/-- Ordinary moving-modulus step, before any exceptional source reset. -/
def unit (q v : Nat) : Nat := (2*v) % (q+1)
def run (q v : Nat) : Nat → Nat
  | 0 => v
  | k+1 => unit (q+k) (run q v k)
def word (q v : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => 2*word q v k + (2*run q v k)/(q+k+1)

/-- Clock correction to the fixed-modulus quotient word. -/
def corr : Nat → Nat → Nat
  | 0, _ => 0
  | k+1, B => 2*corr k (B/2)+(k+1)*(B%2)

theorem run_lt (q v k : Nat) (_hq : 0<q) (hv : v<q) : run q v k < q+k := by
  cases k with
  | zero => simpa [run] using hv
  | succ k =>
    unfold run unit
    exact Nat.mod_lt _ (by omega)

theorem digit_le (q v k : Nat) (hq : 0<q) (hv : v<q) :
    2*run q v k/(q+k+1) ≤ 1 := by
  have ht := run_lt q v k hq hv
  have hd : 2*run q v k/(q+k+1)<2 := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
  omega

theorem word_lt (q v k : Nat) (hq : 0<q) (hv : v<q) : word q v k<2^k := by
  induction k with
  | zero => simp [word]
  | succ k ih =>
    have hd := digit_le q v k hq hv
    simp only [word,Nat.pow_succ]
    omega

theorem corr_bound (k B : Nat) : corr k B+k+2≤2^(k+1) := by
  induction k generalizing B with
  | zero => simp [corr]
  | succ k ih =>
    have h := ih (B/2)
    have hb : B%2=0 ∨ B%2=1 := by omega
    simp only [corr,Nat.pow_succ] at *
    rcases hb with hb|hb <;> simp [hb] <;> omega

private theorem div_digit (a d : Nat) (h : d≤1) :
    (2*a+d)/2=a ∧ (2*a+d)%2=d := by omega

theorem word_eq (q v k : Nat) (hq : 0<q) (hv : v<q) :
    2^k*v = q*word q v k+corr k (word q v k)+run q v k := by
  induction k with
  | zero => simp [word,corr,run]
  | succ k ih =>
    let d := 2*run q v k/(q+k+1)
    have hd : d≤1 := digit_le q v k hq hv
    have he : word q v (k+1)=2*word q v k+d := rfl
    obtain ⟨hdv,hdm⟩ := div_digit (word q v k) d hd
    have hr : run q v (k+1)+(q+k+1)*d=2*run q v k := by
      change (2*run q v k)%(q+k+1)+(q+k+1)*(2*run q v k/(q+k+1))=2*run q v k
      exact Nat.mod_add_div _ _
    rw [he,corr,hdv,hdm,Nat.pow_succ]
    have hi := congrArg (fun x : Nat => 2*x) ih
    simp only [Nat.mul_add] at hi ⊢
    simp only [Nat.add_mul,Nat.one_mul] at hr ⊢
    have hL : 2^k*2*v=2*(2^k*v) := by ac_rfl
    have hA : q*(2*word q v k)=2*(q*word q v k) := by ac_rfl
    rw [hL,hA]
    omega

theorem word_near (q v k : Nat) (hq : 0<q) (hv : v<q) (hfit : 2^(k+1)≤q) :
    word q v k≤2^k*v/q ∧ 2^k*v/q≤word q v k+1 := by
  have he := word_eq q v k hq hv
  have hc := corr_bound k (word q v k)
  have hr := run_lt q v k hq hv
  have hlow : q*word q v k≤2^k*v := by omega
  have hhigh : 2^k*v<q*(word q v k+2) := by rw [Nat.mul_add]; omega
  exact ⟨(Nat.le_div_iff_mul_le hq).2 (by simpa [Nat.mul_comm] using hlow),by
    have h : 2^k*v/q<word q v k+2 := (Nat.div_lt_iff_lt_mul hq).2 (by simpa only [Nat.mul_comm q (word q v k+2)] using hhigh)
    omega⟩

/-- The static word is exact whenever its corrected final remainder is
nonnegative. This checks every prefix implicitly, not only the final state. -/
theorem static_word_of_nonnegative (q v k : Nat) (hq : 0<q) (hv : v<q)
    (h : q*(2^k*v/q)+corr k (2^k*v/q)≤2^k*v) :
    word q v k=2^k*v/q := by
  induction k with
  | zero => simp [word,Nat.div_eq_of_lt hv]
  | succ k ih =>
    let B := 2^(k+1)*v/q
    let C := 2^k*v/q
    let X := 2^k*v
    have hX : 2^(k+1)*v=2*X := by simp only [X,Nat.pow_succ]; ac_rfl
    have hBC : B/2=C := by
      dsimp [B,C]
      rw [hX, Nat.div_div_eq_div_mul]
      rw [Nat.mul_comm q 2, Nat.mul_div_mul_left _ _ (by decide)]
    have hB : B=2*C+B%2 := by have hh := Nat.mod_add_div B 2; omega
    have h' : q*B+corr (k+1) B≤2*X := by simpa [B,hX] using h
    have hprod : q*B=2*(q*C)+q*(B%2) := by
      calc
        q*B=q*(2*C+B%2) := congrArg (q*·) hB
        _=_ := by rw [Nat.mul_add]; congr 1; ac_rfl
    rw [corr,hBC,hprod] at h'
    have hp : q*C+corr k C≤X := by omega
    have hw : word q v k=C := ih hp
    have hrun := word_eq q v k hq hv
    rw [hw] at hrun
    change X=q*C+corr k C+run q v k at hrun
    have hlo : (q+k+1)*(B%2)≤2*run q v k := by
      have hp' : 2*(q*C)+q*(B%2)+(2*corr k C+(k+1)*(B%2))≤2*X := h'
      simp only [Nat.add_mul,Nat.one_mul] at hp' ⊢
      omega
    have hmod := Nat.div_add_mod (2*X) q
    have hrem := Nat.mod_lt (2*X) hq
    have hB' : 2*X/q=B := by rw [← hX]
    rw [hB',hprod] at hmod
    have hhi : 2*run q v k<(q+k+1)*(B%2)+(q+k+1) := by
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    have hd : 2*run q v k/(q+k+1)=B%2 := by
      apply (Nat.div_eq_iff (by omega : 0<q+k+1)).2
      rw [Nat.mul_comm (B%2) (q+k+1)]
      omega
    change word q v (k+1)=B
    rw [word,hw,hd]
    exact hB.symm

/-- Only two candidates are needed. No intermediate test is required to
    select the ordinary wrap word. -/
def fastWord (q v k : Nat) : Nat :=
  let X := 2^k*v
  let B := X/q
  if q*B+corr k B≤X then B else B-1

def fastRun (q v k : Nat) : Nat :=
  let B := fastWord q v k
  2^k*v-(q*B+corr k B)

theorem fastWord_eq (q v k : Nat) (hq : 0<q) (hv : v<q) (hfit : 2^(k+1)≤q) :
    fastWord q v k=word q v k := by
  unfold fastWord
  dsimp only
  split
  · rename_i h
    exact (static_word_of_nonnegative q v k hq hv h).symm
  · rename_i h
    have hnear := word_near q v k hq hv hfit
    have he := word_eq q v k hq hv
    have hn : word q v k≠2^k*v/q := by
      intro hw
      rw [hw] at he
      omega
    omega

theorem fastRun_eq (q v k : Nat) (hq : 0<q) (hv : v<q) (hfit : 2^(k+1)≤q) :
    fastRun q v k=run q v k := by
  unfold fastRun
  rw [fastWord_eq q v k hq hv hfit]
  have he := word_eq q v k hq hv
  dsimp only
  omega

theorem run_growth (q v i j : Nat) (hij : i≤j) : run q v j≤2^(j-i)*run q v i := by
  induction j with
  | zero =>
    have hi : i=0 := by omega
    subst i
    simp
  | succ j ih =>
    by_cases h : i≤j
    · have hprev := ih h
      have ht : run q v (j+1)≤2*run q v j := Nat.mod_le _ _
      rw [show j+1-i=(j-i)+1 by omega,Nat.pow_succ]
      have hm := Nat.mul_le_mul_left 2 hprev
      rw [show 2*(2^(j-i)*run q v i)=2^(j-i)*2*run q v i by ac_rfl] at hm
      omega
    · have hi : i=j+1 := by omega
      subst i
      simp

/-- Cheap sufficient test for a reset-free block. If the ordinary endpoint
    is larger than 2^k, no positive intermediate time has value <=2. -/
theorem no_small_of_endpoint (q v k : Nat) (h : 2^k<run q v k) :
    ∀ i, 0<i → i≤k → 2<run q v i := by
  intro i hi hik
  have hg := run_growth q v i k hik
  by_cases hv : run q v i≤2
  · have hm := Nat.mul_le_mul_left (2^(k-i)) hv
    have hp := Nat.pow_le_pow_right (show 0<2 by decide) (show k-i+1≤k by omega)
    rw [Nat.pow_succ] at hp
    omega
  · omega

/-- After any small ordinary residue, a fitted block has no further wrap.
    The remaining word and residue are both shifted by the same amount. -/
theorem small_tail (q v i k : Nat) (hi : 0<i) (hik : i≤k)
    (hs : run q v i≤2) (hf : 2^(k+1)≤q) :
    run q v k=2^(k-i)*run q v i ∧
    word q v k=2^(k-i)*word q v i := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : i≤k
    · have hf' : 2^(k+1)≤q := Nat.le_trans (Nat.pow_le_pow_right (by decide : 0<2) (by omega)) hf
      obtain ⟨hr,hw⟩ := ih h hf'
      have hpow : 2^(k-i+2)≤2^(k+1) := Nat.pow_le_pow_right (by decide : 0<2) (by omega)
      rw [show k-i+2=(k-i)+1+1 by omega,Nat.pow_succ,Nat.pow_succ,Nat.pow_succ] at hpow
      have hb := Nat.mul_le_mul_left (2^(k-i)) hs
      have hx : 2*run q v k<q+k+1 := by
        rw [hr]
        omega
      have hu : run q v (k+1)=2*run q v k := Nat.mod_eq_of_lt hx
      have hd : 2*run q v k/(q+k+1)=0 := Nat.div_eq_of_lt hx
      rw [hu,word,hd,hr,hw,show k+1-i=k-i+1 by omega,Nat.pow_succ]
      constructor <;> ac_rfl
    · have he : i=k+1 := by omega
      subst i
      simp

private theorem pow_le_of_odd_mul_dvd (d r a : Nat)
    (h : 2^d∣2^r*(2*a+1)) : d≤r := by
  by_cases hd : d≤r
  · exact hd
  · have hp : 2^(r+1)∣2^d := Nat.pow_dvd_pow 2 (by omega)
    have hdiv := Nat.dvd_trans hp h
    rw [Nat.pow_succ] at hdiv
    obtain ⟨t,ht⟩ := hdiv
    have hEq : 2^r*(2*a+1)=2^r*(2*t) := by rw [ht,Nat.mul_assoc]
    have hh := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos r) hEq
    omega

/-- Exact low-bit detector: the last wrap is at distance r from the end.
    An ordinary small residue anywhere would force the final residue to be
    at most twice the low set bit of the wrap word. -/
theorem no_small_of_lowbit (q v k r a : Nat) (hf : 2^(k+1)≤q)
    (hw : word q v k=2^r*(2*a+1)) (hR : 2*2^r<run q v k) :
    ∀ i, 0<i → i≤k → 2<run q v i := by
  intro i hi hik
  by_cases hs : run q v i≤2
  · obtain ⟨hr,hw'⟩ := small_tail q v i k hi hik hs hf
    have hd : 2^(k-i)∣word q v k := ⟨word q v i,hw'⟩
    rw [hw] at hd
    have hle := pow_le_of_odd_mul_dvd _ _ _ hd
    have hp := Nat.pow_le_pow_right (show 0<2 by decide) hle
    have hmul := Nat.mul_le_mul_left (2^(k-i)) hs
    omega
  · omega

private theorem corr_zero (k : Nat) : corr k 0=0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [corr,ih]

theorem word_zero_run (q v k : Nat) (hq : 0<q) (hv : v<q)
    (hw : word q v k=0) : run q v k=2^k*v := by
  have h := word_eq q v k hq hv
  rw [hw] at h
  simp [corr_zero] at h
  exact h.symm

theorem no_small_of_zero_word (q v k : Nat) (hq : 0<q) (hv : v<q)
    (hv3 : 3≤v) (hw : word q v k=0) : ∀ i, 0<i → i≤k → 2<run q v i := by
  apply no_small_of_endpoint
  rw [word_zero_run q v k hq hv hw]
  have h := Nat.mul_le_mul_left (2^k) hv3
  have hp := Nat.two_pow_pos k
  omega

#print axioms small_tail
#print axioms no_small_of_lowbit
#print axioms no_small_of_zero_word
#print axioms word_eq
#print axioms word_near
#print axioms static_word_of_nonnegative
#print axioms fastWord_eq
#print axioms fastRun_eq
#print axioms no_small_of_endpoint
end BB6.Agent43ForwardBlock
