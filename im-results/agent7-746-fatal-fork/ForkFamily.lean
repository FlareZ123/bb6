import ForkArithmetic
set_option maxHeartbeats 0
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048
namespace BB746Fork

private theorem power_period (s t c : Nat) (hc : 2^s%729=c) :
    2^(s+1458*t)%729=c := by
  induction t with
  | zero => simpa using hc
  | succ t ih =>
    have he : s+1458*(t+1)=(s+1458*t)+1458 := by omega
    rw [he,Nat.pow_add,Nat.mul_mod,ih]
    have hp : 2^1458%729=1 := by decide
    rw [hp]
    omega

private theorem div_fatal_mod9 (n p u : Nat)
    (hnum : 2*u+5+2*n+3=32*p)
    (hres : (p%729=544 ∧ n%729=40) ∨
      (p%729=224 ∧ n%729=401) ∨
      (p%729=544 ∧ n%729=283) ∨
      (p%729=224 ∧ n%729=644)) :
    (2*u+5)%9=0 := by
  rcases hres with hr | hr | hr | hr
  all_goals omega

private theorem div_fork_mod27 (n p x : Nat)
    (hx : 9*x+17*n+39=56*p)
    (hres : (p%729=544 ∧ n%729=40) ∨
      (p%729=224 ∧ n%729=401) ∨
      (p%729=544 ∧ n%729=283) ∨
      (p%729=224 ∧ n%729=644)) :
    (2*x+5)%27=0 := by
  rcases hres with hr | hr | hr | hr
  all_goals omega

private theorem pow_growth (k : Nat) (hk : 38≤k) :
    100*(k+2)+200<2^k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : 38≤k
    · have hb := ih h
      rw [Nat.pow_succ]
      omega
    · have he : k=37 := by omega
      subst k
      decide

private theorem family_residue (r t : Nat)
    (hr : r=40 ∨ r=401 ∨ r=1012 ∨ r=1373) :
    let n := r+1458*t
    let p := 2^(n-2)
    ((p%729=544 ∧ n%729=40) ∨
     (p%729=224 ∧ n%729=401) ∨
     (p%729=544 ∧ n%729=283) ∨
     (p%729=224 ∧ n%729=644)) ∧ 40≤n := by
  rcases hr with rfl | rfl | rfl | rfl
  all_goals simp only
  · have hp : 2^(38+1458*t)%729=544 := power_period 38 t 544 (by decide)
    have he : (40+1458*t)-2=38+1458*t := by omega
    rw [he]
    exact ⟨Or.inl ⟨hp,by omega⟩,by omega⟩
  · have hp : 2^(399+1458*t)%729=224 := power_period 399 t 224 (by decide)
    have he : (401+1458*t)-2=399+1458*t := by omega
    rw [he]
    exact ⟨Or.inr (Or.inl ⟨hp,by omega⟩),by omega⟩
  · have hp : 2^(1010+1458*t)%729=544 := power_period 1010 t 544 (by decide)
    have he : (1012+1458*t)-2=1010+1458*t := by omega
    rw [he]
    exact ⟨Or.inr (Or.inr (Or.inl ⟨hp,by omega⟩)),by omega⟩
  · have hp : 2^(1371+1458*t)%729=224 := power_period 1371 t 224 (by decide)
    have he : (1373+1458*t)-2=1371+1458*t := by omega
    rw [he]
    exact ⟨Or.inr (Or.inr (Or.inr ⟨hp,by omega⟩)),by omega⟩

/-- Four explicit unbounded arithmetic families all exhibit a genuine
source reset predecessor x of a fatal height, where x itself has a
completely excluded two-layer inverse cone. -/
theorem infinite_fatal_feeder_gap (r t : Nat)
    (hr : r=40 ∨ r=401 ∨ r=1012 ∨ r=1373) :
    let n := r+1458*t
    let k := n-2
    let p := 2^k
    let u := 4*2^n-n-4
    let d := (2*u+5)/9
    let x := 4*d-8*p-n-3
    ¬ResetChain 2 x := by
  let n := r+1458*t
  let k := n-2
  let p := 2^k
  let u := 4*2^n-n-4
  let d := (2*u+5)/9
  let x := 4*d-8*p-n-3
  let h := 2*x-8*p-k
  let d2 := (2*x+5)/27
  let y := 8*d2-2*p-n-1
  let z := 2*y-2*p-n+4
  obtain ⟨hres,hn⟩ := family_residue r t hr
  have hn2 : k+2=n := by dsimp [k]; omega
  have hk : 4≤k := by omega
  have hgrowth : 100*n+200<p := by
    have hkb : 38≤k := by omega
    have hp := pow_growth k hkb
    dsimp [p]
    omega
  have hpow : 2^n=4*p := by
    rw [←hn2,Nat.pow_add]
    simp only [show 2^2=4 by decide]
    dsimp [p]
    omega
  have hu : u+n+4=16*p := by dsimp [u]; omega
  have hnum : 2*u+5=32*p-2*n-3 := by omega
  have hnum_add : 2*u+5+2*n+3=32*p := by omega
  have hdiv9 : (2*u+5)%9=0 := div_fatal_mod9 n p u hnum_add hres
  have hd : 9*d=2*u+5 := by dsimp [d]; omega
  have hxd : x+8*p+n+3=4*d := by dsimp [x]; omega
  have hx : 9*x+17*n+39=56*p := by omega
  have hh0 : h+8*p+k=2*x := by dsimp [h]; omega
  have hh : 9*h+43*n+60=40*p := by omega
  have hdiv27 : (2*x+5)%27=0 := div_fork_mod27 n p x hx hres
  have hd2 : 27*d2=2*x+5 := by dsimp [d2]; omega
  have hyd : y+2*p+n+1=8*d2 := by dsimp [y]; omega
  have hy : 243*y+515*n+507=410*p := by omega
  have hz0 : z+2*p+n=2*y+4 := by dsimp [z]; omega
  have hz : 243*z+1273*n+42=334*p := by omega
  exact index_fork_root_exclusion n k p x h y z hk hn2 rfl hgrowth hx hh hy hz hres

#print axioms infinite_fatal_feeder_gap
end BB746Fork
