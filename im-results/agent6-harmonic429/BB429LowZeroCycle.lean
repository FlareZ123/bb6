import BB429Rank
import Lean.Elab.Tactic.Omega

namespace BB429.LowZeroCycle

set_option maxHeartbeats 2000000

private theorem pow2 (n : Nat) : 0 < 2^n := Nat.pow_pos (by decide)

private theorem period (k : Nat) : 2^(2*k) % (2^k+1) = 1 := by
  let A := 2^k
  have hA : 0<A := pow2 k
  have he : 2^(2*k) = A*A := by
    rw [Nat.mul_comm 2 k, Nat.mul_two, Nat.pow_add]
  have hq : A*A = 1+(A+1)*(A-1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.add_mul, Nat.one_mul]
    have hpos : A+1 ≤ A*A+A := by
      have h := Nat.le_mul_of_pos_right A hA
      omega
    omega
  rw [he,hq,Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

private theorem period_mod (k e : Nat) (hk : 0<k) :
    2^e % (2^k+1) = 2^(e%(2*k)) % (2^k+1) := by
  let r := e%(2*k)
  let q := e/(2*k)
  have he : e=r+(2*k)*q := (Nat.mod_add_div e (2*k)).symm
  have hp : 2^e=2^r*(2^(2*k))^q := by
    conv => lhs; rw [he,Nat.pow_add,Nat.pow_mul]
  rw [hp,Nat.mul_mod, Nat.pow_mod (2^(2*k)) q (2^k+1),period]
  have h1 : 1 < 2^k+1 := by have h:=pow2 k; omega
  simp [Nat.mod_eq_of_lt h1]
  rfl

private theorem linear_bound (k : Nat) (hk : 6≤k) : k+10≤2^(k-1) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : 6≤k
    · have hp := ih h
      have he : k+1-1=(k-1)+1 := by omega
      rw [he,Nat.pow_succ]
      omega
    · have h5 : k=5 := by omega
      subst k
      decide

/-- Exact divisibility for the zero-cycle Fermat-type modulus. -/
theorem fermat_divisibility (k e : Nat) (hk : 6≤k) :
    (2^k+1) ∣ (2^e+k+10) ↔
      ∃ s, s<k ∧ 2^s=k+10 ∧ e%(2*k)=k+s := by
  let M := 2^k+1
  let r := e%(2*k)
  have hr : r<2*k := Nat.mod_lt _ (by omega)
  have hM : 0<M := by dsimp [M]; exact Nat.zero_lt_succ _
  have hper : 2^e%M=2^r%M := period_mod k e (by omega)
  have hsum : (2^e+k+10)%M=(2^r+k+10)%M := by
    rw [show 2^e+k+10=2^e+(k+10) by omega,
      show 2^r+k+10=2^r+(k+10) by omega,
      Nat.add_mod (2^e),Nat.add_mod (2^r),hper]
  have hlin := linear_bound k hk
  have hpow : 2^k=2^(k-1)*2 := by
    conv => lhs; rw [show k=(k-1)+1 by omega,Nat.pow_succ]
  constructor
  · intro hd
    have h0 : (2^r+k+10)%M=0 := hsum ▸ Nat.mod_eq_zero_of_dvd hd
    by_cases hlo : r<k
    · have hle := Nat.pow_le_pow_right (n:=2) (by decide) (show r≤k-1 by omega)
      have hp := pow2 r
      have hsmall : 2^r+k+10<M := by dsimp [M]; omega
      rw [Nat.mod_eq_of_lt hsmall] at h0
      omega
    · let s := r-k
      have hs : s<k := by dsimp [s]; omega
      have hrs : r=k+s := by dsimp [s]; omega
      have h2s := pow2 s
      have hle := Nat.pow_le_pow_right (n:=2) (by decide) (show s≤k-1 by omega)
      have hmul : 2^r+2^s=M*2^s := by rw [hrs,Nat.pow_add]; dsimp [M]; rw [Nat.add_mul,Nat.one_mul]
      have hsmall1 : 2^s<M := by dsimp [M]; omega
      have hsmall2 : k+10<M := by dsimp [M]; omega
      have hrem : (2^r+2^s)%M=0 := by rw [hmul,Nat.mul_mod_right]
      rw [Nat.add_mod, Nat.mod_eq_of_lt hsmall1] at hrem
      rw [show 2^r+k+10=2^r+(k+10) by omega,Nat.add_mod,Nat.mod_eq_of_lt hsmall2] at h0
      have hA := Nat.mod_lt (2^r) hM
      have hmod1 := Nat.mod_add_div ((2^r)%M+2^s) M
      have hmod2 := Nat.mod_add_div ((2^r)%M+(k+10)) M
      have hD1 : ((2^r)%M+2^s)/M=1 := by
        apply Nat.div_eq_of_lt_le
        · simp only [Nat.one_mul]
          by_cases h : (2^r)%M+2^s<M
          · rw [Nat.mod_eq_of_lt h] at hrem
            omega
          · omega
        · omega
      have hD2 : ((2^r)%M+(k+10))/M=1 := by
        apply Nat.div_eq_of_lt_le
        · simp only [Nat.one_mul]
          by_cases h : (2^r)%M+(k+10)<M
          · rw [Nat.mod_eq_of_lt h] at h0
            omega
          · omega
        · omega
      rw [hrem,hD1,Nat.mul_one,Nat.zero_add] at hmod1
      rw [h0,hD2,Nat.mul_one,Nat.zero_add] at hmod2
      exact ⟨s,hs,by omega,hrs⟩
  · rintro ⟨s,hs,he,hr'⟩
    change r=k+s at hr'
    have hmul : 2^r+k+10=M*2^s := by
      rw [hr',Nat.pow_add,Nat.add_assoc,← he]
      dsimp [M]
      rw [Nat.add_mul,Nat.one_mul]
    apply Nat.dvd_of_mod_eq_zero
    rw [hsum,hmul,Nat.mul_mod_right]

private theorem pow3_mod (t : Nat) (ht : t%4=0) :
    (2^(t+2)+1)%3=2 := by
  let q := t/4
  have h : t=4*q := by dsimp [q]; omega
  rw [h,Nat.pow_add,Nat.pow_mul,Nat.add_mod,Nat.mul_mod,Nat.pow_mod 16 q 3]
  simp

private theorem mod5_pow (m : Nat) : 2^(4*m+5)%5=2 := by
  rw [Nat.pow_add,Nat.pow_mul,Nat.mul_mod,Nat.pow_mod 16 m 5]
  simp

private theorem mul_three_cancel (M v Z : Nat) (hM : M%3=2)
    (h : M*v=3*Z) : M ∣ Z := by
  have hm := congrArg (fun n : Nat => n%3) h
  rw [Nat.mul_mod M v 3,hM] at hm
  have hv : v%3=0 := by
    have hvlt := Nat.mod_lt v (by decide : 0<3)
    omega
  let q := v/3
  have hvq : v=3*q := by dsimp [q]; omega
  refine ⟨q,?_⟩
  rw [hvq,Nat.mul_left_comm M 3] at h
  omega

/-- Necessary and sufficient arithmetic parameters for the first low-side
    terminal F burst: the burst length is t=2^s-12 with s=3 mod 4, s>=7. -/
theorem parameter_divisibility (m t : Nat) (ht : t%4=0) :
    (2^(t+2)+1) ∣ (2^(4*m+5)+t+12) ↔
    ∃ s, 7≤s ∧ s%4=3 ∧ t+12=2^s ∧ (4*m+5)%(2*(t+2))=t+2+s := by
  constructor
  · intro hd
    by_cases hz : t=0
    · subst t
      have h := Nat.mod_eq_zero_of_dvd hd
      change (2^(4*m+5)+0+12)%5=0 at h
      simp only [Nat.add_zero] at h
      rw [Nat.add_mod,mod5_pow] at h
      contradiction
    · have hk : 6≤t+2 := by omega
      have hd' : (2^(t+2)+1) ∣ (2^(4*m+5)+(t+2)+10) := by
        simpa only [Nat.add_assoc,show (2+10:Nat)=12 by decide] using hd
      obtain ⟨s,hs,hpow,hr⟩ := (fermat_divisibility (t+2) (4*m+5) hk).mp hd'
      have hmod : (2*(t+2))%4=0 := by omega
      have hrem := Nat.mod_add_div (4*m+5) (2*(t+2))
      rw [hr] at hrem
      have hcong := congrArg (fun n : Nat => n%4) hrem
      rw [Nat.add_mod,Nat.mul_mod,hmod] at hcong
      have hsmod : s%4=3 := by omega
      have hs7 : 7≤s := by
        by_cases hlt : s<7
        · have he : s=3 := by omega
          subst s
          omega
        · omega
      exact ⟨s,hs7,hsmod,by omega,hr⟩
  · rintro ⟨s,hs,hmod,hpow,hr⟩
    have hp : 2^7≤2^s := Nat.pow_le_pow_right (by decide) hs
    have hk : 6≤t+2 := by omega
    have hslt : s<t+2 := by
      have h := Nat.mod_lt (4*m+5) (show 0<2*(t+2) by omega)
      omega
    have hd := (fermat_divisibility (t+2) (4*m+5) hk).mpr ⟨s,hslt,by omega,hr⟩
    simpa only [Nat.add_assoc,show (2+10:Nat)=12 by decide] using hd

private theorem pow_scale (m : Nat) : 2^(4*m+5)=32*16^m := by
  rw [Nat.pow_add,Nat.pow_mul]
  change 16^m*32=32*16^m
  omega

private theorem scale_ge (m : Nat) : 16*m≤16^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.pow_succ]
    have hp : 0<16^m := Nat.pow_pos (by decide)
    omega

/-- Exact endpoint arithmetic for a successful F-only trace. -/
theorem first_coordinates (n u w a b : Nat)
    (h : firstRun n (u,w)=some (a,b)) :
    a+3=(u+3)*2^n ∧ 2*a+b=2*u+w+3*n := by
  induction n generalizing a b with
  | zero =>
    simp only [firstRun,Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    simp
  | succ n ih =>
    simp only [firstRun] at h
    cases ht : firstRun n (u,w) with
    | none => simp [ht] at h
    | some p =>
      obtain ⟨x,y⟩ := p
      obtain ⟨hx,hy⟩ := ih x y ht
      simp only [ht,Option.bind_some,firstStep] at h
      split at h
      · simp only [Option.some.injEq,Prod.mk.injEq] at h
        rw [Nat.pow_succ,← Nat.mul_assoc,← hx]
        omega
      · contradiction

/-- Conversely, the endpoint equations with natural counters imply that
    every intermediate F guard holds. -/
theorem first_of_coordinates (n u w a b : Nat)
    (ha : a+3=(u+3)*2^n) (hb : 2*a+b=2*u+w+3*n) :
    firstRun n (u,w)=some (a,b) := by
  induction n generalizing a b with
  | zero =>
    simp at ha hb
    have h1 : a=u := by omega
    have h2 : b=w := by omega
    subst a; subst b; rfl
  | succ n ih =>
    let x := (u+3)*2^n-3
    have hp : 3≤(u+3)*2^n := by
      have h := Nat.le_mul_of_pos_right (u+3) (pow2 n)
      omega
    have hx : x+3=(u+3)*2^n := by dsimp [x]; omega
    have hax : a=2*x+3 := by
      rw [Nat.pow_succ,← Nat.mul_assoc,← hx] at ha
      omega
    have hy : 2*x+(b+a)=2*u+w+3*n := by omega
    have h := ih x (b+a) hx hy
    simp only [firstRun,h,Option.bind_some,firstStep]
    simp only [Prod.fst,Prod.snd,if_pos (show 2*x+3≤b+a by omega),Option.some.injEq,Prod.mk.injEq]
    omega

theorem first_is_run (n u w a b : Nat)
    (h : firstRun n (u,w)=some (a,b)) : run n (u,w)=some (a,b) := by
  induction n generalizing a b with
  | zero => exact h
  | succ n ih =>
    simp only [firstRun] at h
    cases ht : firstRun n (u,w) with
    | none => simp [ht] at h
    | some p =>
      obtain ⟨x,y⟩ := p
      have hrun := ih x y ht
      simp only [ht,Option.bind_some,firstStep] at h
      split at h
      · simp only [run,hrun,Option.bind_some]
        rw [show next (x,y)=some (2*x+3,y-2*x-3) by simp [next, *]]
        exact h
      · contradiction

/-- Prepared terminal state after the initial low-side Oe,F pair (j=0). -/
def TerminalHalt (m t : Nat) : Prop :=
  ∃ d, 6≤d ∧ d%4=2 ∧ d+19≤24*16^m-3 ∧
    ∃ a b, firstRun t (24*16^m+3-d,24*16^m+11+3*d)=some (a,b) ∧
      next (a,b)=none

/-- A successful zero-cycle terminal F burst necessarily has these exact
    exponent parameters, not just a congruence at a finite modulus. -/
theorem terminal_necessary (m t : Nat) (h : TerminalHalt m t) :
    ∃ s, 7≤s ∧ s%4=3 ∧ t+12=2^s ∧ (4*m+5)%(2*(t+2))=t+2+s := by
  obtain ⟨d,hd,hd4,hguard,a,b,hfirst,hhalt⟩ := h
  let X := 16^m
  let v := 24*X+6-d
  have hv : v+d=24*X+6 := by dsimp [v]; change d+19≤24*X-3 at hguard; omega
  obtain ⟨ha,hb⟩ := first_coordinates t (24*X+3-d) (24*X+11+3*d) a b hfirst
  have hv' : 24*X+3-d+3=v := by dsimp [v]; omega
  rw [hv'] at ha
  have hl := (next_none_iff_halt_line a b).mp hhalt
  have hclock : 4*(v*2^t)=72*X+d+30+3*t := by omega
  have ht : t%4=0 := by omega
  have hM : (2^(t+2)+1)*v=3*(2^(4*m+5)+t+12) := by
    rw [Nat.pow_add (2:Nat) t 2,pow_scale]
    change (2^t*4+1)*v=3*(32*X+t+12)
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_assoc,Nat.mul_left_comm (2^t) 4 v,Nat.mul_comm (2^t) v]
    omega
  exact (parameter_divisibility m t ht).mp (mul_three_cancel _ _ _ (pow3_mod t ht) hM)

private theorem pow4_dvd (s : Nat) (hs : 2≤s) : 4∣2^s := by
  refine ⟨2^(s-2),?_⟩
  conv => lhs; rw [show s=2+(s-2) by omega,Nat.pow_add]

private theorem parameter_v (m t s : Nat) (hs : 7≤s)
    (ht : t+12=2^s) (hr : (4*m+5)%(2*(t+2))=t+2+s) :
    ∃ v, 384≤v ∧ v%4=0 ∧ v≤24*16^m ∧
      (2^(t+2)+1)*v=3*(2^(4*m+5)+t+12) := by
  let k := t+2
  let e := 4*m+5
  let M := 2^k+1
  have hk : 6≤k := by
    have hp : 2^7≤2^s := Nat.pow_le_pow_right (by decide) hs
    dsimp [k]; omega
  change e%(2*k)=k+s at hr
  have he : e=k+s+(2*k)*(e/(2*k)) := by
    have h := Nat.mod_add_div e (2*k)
    rw [hr] at h
    exact h.symm
  have hle : s≤e := by omega
  have he' : e-s=k+(2*k)*(e/(2*k)) := by omega
  have hmod : (e-s)%(2*k)=k := by
    rw [he',Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (show k<2*k by omega)]
  have hdiv : M ∣ (2^(e-s)+1) := by
    apply Nat.dvd_of_mod_eq_zero
    have hper := period_mod k (e-s) (by omega)
    rw [hmod] at hper
    change 2^(e-s)%M=2^k%M at hper
    rw [Nat.add_mod,hper,← Nat.add_mod]
    exact Nat.mod_self _
  obtain ⟨z,hz⟩ := hdiv
  have hzpos : 0<z := by
    by_cases h : z=0
    · simp [h] at hz
    · omega
  let v := 3*2^s*z
  have h128 : 128≤2^s := Nat.pow_le_pow_right (n:=2) (by decide) hs
  have hvlo : 384≤v := by
    have h := Nat.le_mul_of_pos_right (3*2^s) hzpos
    dsimp [v]; omega
  have hv4 : v%4=0 := by
    obtain ⟨q,hq⟩ := pow4_dvd s (by omega)
    dsimp [v]; rw [hq,Nat.mul_left_comm 3 4 q, Nat.mul_assoc]
    simp
  have hpow : 2^e=2^s*2^(e-s) := by
    conv => lhs; rw [show e=s+(e-s) by omega,Nat.pow_add]
  have hZ : 2^e+t+12=2^s*(2^(e-s)+1) := by
    rw [hpow,Nat.mul_add,Nat.mul_one]
    omega
  have hMv : M*v=3*(2^e+t+12) := by
    rw [hZ,hz]
    dsimp [v]; ac_rfl
  have hM : 5≤M := by
    have hp : 2^2≤2^k := Nat.pow_le_pow_right (by decide) (by omega)
    dsimp [M]; omega
  have hbound := Nat.mul_le_mul_right v hM
  rw [hMv] at hbound
  have hX := scale_ge m
  have hm : 1≤m := by dsimp [e,k] at he; omega
  have ht' : t≤4*m+3 := by dsimp [e,k] at he; omega
  have hvhi : v≤24*16^m := by
    change 5*v≤3*(2^(4*m+5)+t+12) at hbound
    rw [pow_scale] at hbound
    omega
  exact ⟨v,hvlo,hv4,hvhi,hMv⟩

/-- Conversely every admissible exponent pair gives an actual guarded F
    terminal halt, with a uniquely determined deviation d. -/
theorem terminal_sufficient (m t : Nat)
    (h : ∃ s, 7≤s ∧ s%4=3 ∧ t+12=2^s ∧ (4*m+5)%(2*(t+2))=t+2+s) :
    TerminalHalt m t := by
  obtain ⟨s,hs,_,ht,hr⟩ := h
  obtain ⟨v,hvlo,hv4,hvhi,hMv⟩ := parameter_v m t s hs ht hr
  let X := 16^m
  let d := 24*X+6-v
  have hd : d+v=24*X+6 := by dsimp [d]; omega
  have hguard : d+19≤24*X-3 := by omega
  let a := v*2^t-3
  let b := 2*a-1
  have hlarge : 384≤v*2^t := by
    have h := Nat.le_mul_of_pos_right v (pow2 t)
    omega
  have ha : a+3=v*2^t := by dsimp [a]; omega
  have hb : b+1=2*a := by dsimp [b]; omega
  have hclock : 4*(v*2^t)=72*X+d+30+3*t := by
    rw [Nat.pow_add (2:Nat) t 2,pow_scale] at hMv
    change (2^t*4+1)*v=3*(32*X+t+12) at hMv
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_assoc,Nat.mul_left_comm (2^t) 4 v,Nat.mul_comm (2^t) v] at hMv
    omega
  refine ⟨d,by omega,by omega,hguard,a,b,?_,(next_none_iff_halt_line a b).mpr hb⟩
  apply first_of_coordinates
  · have h : 24*X+3-d+3=v := by omega
    rw [h]; exact ha
  · omega

theorem terminal_classification (m t : Nat) : TerminalHalt m t ↔
    ∃ s, 7≤s ∧ s%4=3 ∧ t+12=2^s ∧ (4*m+5)%(2*(t+2))=t+2+s :=
  ⟨terminal_necessary m t,terminal_sufficient m t⟩

private theorem low_pair (u d : Nat) (hd : 6≤d) (hd4 : d%4=2)
    (hu4 : u%4=1) (hguard : d+19≤u) :
    run 2 (u,u+12+d)=some (u+6-d,u+14+3*d) := by
  let w := u+12+d
  let v := (u+3-d)/2
  have hw : w+1<2*u := by dsimp [w]; omega
  have hw0 : ¬w≥2*u+3 := by omega
  have hw1 : w≠2*u+2 := by omega
  have hw2 : w≠2*u+1 := by omega
  have hw3 : w≠2*u := by omega
  have hodd : w%2≠0 := by dsimp [w]; omega
  have hgap : 4≤u-w/2 := by dsimp [w]; omega
  have hgap1 : u-w/2≠1 := by omega
  have hgap2 : u-w/2≠2 := by omega
  have heven : (u-w/2)%2=0 := by dsimp [w]; omega
  have hw4 : w≠1 := by dsimp [w]; omega
  have h1 : next (u,w)=some (v,2*u+20+2*d) := by
    simp only [next,hw0,hw1,hw2,hw3,hodd,hgap1,hgap2,heven,hw4,ite_false,ite_true,
      Option.some.injEq,Prod.mk.injEq]
    dsimp [w,v]; omega
  have h2 : next (v,2*u+20+2*d)=some (u+6-d,u+14+3*d) := by
    rw [show next (v,2*u+20+2*d)=some (2*v+3,(2*u+20+2*d)-2*v-3) by
      apply ite_eq_left (show 2*u+20+2*d≥2*v+3 by dsimp [v]; omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    dsimp [v]; omega
  change run 2 (u,w)=some (u+6-d,u+14+3*d)
  simp [run,h1,h2]

/-- Lift the complete exponent classification to the original accelerator.
    Every witness is a successful zero-section trajectory with exact word
    F^(4m+3), Oe,F, F^t, followed by a halt. -/
theorem terminal_source (m t : Nat) (h : TerminalHalt m t) :
    ∃ d a b, 6≤d ∧ d%4=2 ∧ d+19≤24*16^m-3 ∧
      firstRun t (24*16^m+3-d,24*16^m+11+3*d)=some (a,b) ∧
      run (4*m+5+t) (0,72*16^m+d-(12*m+6))=some (a,b) ∧ next (a,b)=none := by
  obtain ⟨d,hd,hd4,hguard,a,b,hfirst,hhalt⟩ := h
  let X := 16^m
  let u := 24*X-3
  let W := 72*X+d-(12*m+6)
  have hX := scale_ge m
  have hpos : 0<X := Nat.pow_pos (by decide)
  have hu : u+3=3*2^(4*m+3) := by
    rw [Nat.pow_add,Nat.pow_mul]
    change u+3=3*(X*8)
    dsimp [u]; omega
  have hB : firstRun (4*m+3) (0,W)=some (u,u+12+d) := by
    apply first_of_coordinates
    · simpa using hu
    · dsimp [u,W]; omega
  have hrun := first_is_run _ _ _ _ _ hB
  have hpair := low_pair u d hd hd4 (by dsimp [u]; omega) hguard
  have hpair' : run 2 (u,u+12+d)=some (24*X+3-d,24*X+11+3*d) := by
    have h1 : u+6-d=24*X+3-d := by dsimp [u]; omega
    have h2 : u+14+3*d=24*X+11+3*d := by dsimp [u]; omega
    rwa [h1,h2] at hpair
  refine ⟨d,a,b,hd,hd4,hguard,hfirst,?_,hhalt⟩
  change run (4*m+5+t) (0,W)=some (a,b)
  rw [show 4*m+5+t=(4*m+3)+2+t by omega,run_add,run_add,hrun]
  simp only [Option.bind_some,hpair']
  exact first_is_run _ _ _ _ _ hfirst

/-- All admissible exponent pairs produce a real source-level prepared halt. -/
theorem classified_source_halt (m t s : Nat) (hs : 7≤s) (hs4 : s%4=3)
    (ht : t+12=2^s) (hr : (4*m+5)%(2*(t+2))=t+2+s) :
    ∃ d a b, 6≤d ∧ d%4=2 ∧ d+19≤24*16^m-3 ∧
      firstRun t (24*16^m+3-d,24*16^m+11+3*d)=some (a,b) ∧
      run (4*m+5+t) (0,72*16^m+d-(12*m+6))=some (a,b) ∧ next (a,b)=none :=
  terminal_source m t (terminal_sufficient m t ⟨s,hs,hs4,ht,hr⟩)

#print axioms fermat_divisibility
#print axioms parameter_divisibility
#print axioms terminal_classification
#print axioms classified_source_halt

end BB429.LowZeroCycle
