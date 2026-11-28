import BB429Resonance234
import BB429ResonanceEven

namespace BB429.CoarseExit

/-- Re-index the exact d=234 post-resonance state by the total scale m. -/
theorem d234_post_m (m : Nat) (hm : 2≤m) :
    run (8*m+7) (prepared m 234) =
      some (416*m+3965,72*16^m-808*m-7677) := by
  obtain ⟨j,rfl⟩ : ∃ j : Nat, m=j+2 := ⟨m-2,by omega⟩
  have h := d234_post j
  have hp : 72*16^(j+2)=18432*16^j := by
    rw [Nat.pow_add,show 16^2=256 by decide]
    omega
  rw [show 8*(j+2)+7=8*j+23 by omega]
  convert h using 1 <;> simp only [Prod.mk.injEq,Option.some.injEq]
  · omega
  · rw [hp]
    have hpow : 1≤16^j := Nat.pow_pos (by decide)
    omega

/-- Large-scale second-burst reduction for d=234 in the even-burst parity.
    Writing m=j+s and taking K=4j first-branch steps leaves an odd second
    counter and leading V coefficient 54*4^(2s+1).  Unless m=8 (mod 9),
    the doubled-scale Cantor resonance is arithmetically impossible. -/
theorem d234_even_second_return (m s j : Nat) (hm : m=j+s) (hm2 : 2≤m)
    (hmod : m%9≠8)
    (hbudget :
      2*((416*m+3968)*2^(4*j)-3) ≤
        72*16^m+24*m+253+12*j)
    (hsep :
      3*cap
        (budget 0 (72*(m:Int)+759+36*(j:Int)) (2*s+5))
        (2*s+5)+39 < (16:Int)^j) :
    ∃ k t, 0<k ∧ k≤12*m+17 ∧
      run k (prepared m 234)=some t ∧ isSection t := by
  let K := 4*j
  let I := 2*s+1
  let P := 2^K
  let u := (416*m+3968)*P-3
  let R := 72*16^m+24*m+253+3*K
  let w := R-2*u
  let a : Int := 2496*(m:Int)+23808
  let y : Int := 72*(m:Int)+759+9*(K:Int)
  have hP : 1≤P := Nat.pow_pos (by decide)
  have hu : u+3=(416*m+3968)*P := by
    have hp : 3≤(416*m+3968)*P :=
      Nat.le_mul_of_pos_right _ (Nat.pow_pos (a:=2) (n:=K) (by decide))
    dsimp [u]
    omega
  have hR : 2*u+w=R := by
    dsimp [w]
    dsimp [R,K,P] at hbudget ⊢
    omega
  have hfirst := d234_post_m m hm2
  have hburst :
      run K (416*m+3965,72*16^m-808*m-7677)=some (u,w) := by
    apply LowReturnBand.section_burst
    · simpa [P] using hu
    · rw [hR]
      dsimp [R]
      omega
  have hp : w%2=1 := by
    rw [show R=2*u+w by omega]
    dsimp [R,K]
    omega
  have hUc : Uc (u,w)=a*(P:Int) := by
    have h := congrArg (fun z : Nat => (z:Int)) hu
    simp only [Int.natCast_add,Int.natCast_mul,Int.cast_ofNat_Int] at h
    simp [Uc,a]
    grind +ring
  have hV : Vc (u,w)=(54*4^I)*(P:Int)+y := by
    have hr := congrArg (fun z : Nat => (z:Int)) hR
    simp only [Int.natCast_add,Int.natCast_mul,Int.natCast_pow,Int.cast_ofNat_Int] at hr
    have hpow : (54:Int)*4^I*(P:Int)=216*16^m := by
      dsimp [I,P,K]
      push_cast
      rw [Int.pow_add (4:Int) (2*s) 1,Int.pow_mul,Int.pow_mul]
      rw [hm,Int.pow_add]
      change 54*((16:Int)^s*4)*(16:Int)^j =
        216*((16:Int)^j*(16:Int)^s)
      grind +ring
    rw [hpow]
    simp [Vc,y]
    dsimp [R] at hr
    omega
  have hsep' : 3*cap (budget 0 y (I+4)) (I+4)+39<(P:Int) := by
    dsimp [I,P,K,y]
    push_cast
    simpa using hsep
  have hres := d234_even_nonresonant_mod9 m I hmod
  obtain ⟨k,t,hk,hkn,ht,hs⟩ :=
    return_from_exact_burst_even (u,w) I a P y hp
      (by simp [y,K]; omega) hUc hV hsep'
      (by simp [a]; omega) (by simpa [a] using hres)
  refine ⟨8*m+7+K+k,t,by omega,?_,?_,hs⟩
  · dsimp [K,I] at hkn
    omega
  · rw [run_add,run_add,hfirst,Option.bind_some,hburst,Option.bind_some,ht]

theorem d234_burst_growth (s : Nat) (hs : 3≤s) :
    832*(4*s+3)+7936 ≤ 72*16^s := by
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases h : 3≤s
    · have hh := ih h
      rw [Nat.pow_succ]
      omega
    · have he : s=2 := by omega
      subst s
      decide

theorem d234_sep_growth (s : Nat) (hs : 4≤s) :
    (9375:Int)*(1000*s+4000)+40≤128^s := by
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases h : 4≤s
    · have hh := ih h
      rw [Int.pow_succ,Int.natCast_succ]
      omega
    · have he : s=3 := by omega
      subst s
      decide

/-- All sufficiently large d=234 scales outside one residue class modulo 9
    return to a section.  The only large scales not covered are m=8 (mod 9). -/
theorem d234_large_non8 (s t : Nat) (hs : 4≤s) (ht : t<4)
    (hmod : (4*s+t)%9≠8) :
    ∃ k p, 0<k ∧ k≤12*(4*s+t)+17 ∧
      run k (prepared (4*s+t) 234)=some p ∧ isSection p := by
  let j := 3*s+t
  let m := j+s
  have hm : m=4*s+t := by dsimp [m,j]; omega
  have hX : 16^m=16^j*16^s := by
    dsimp [m]
    rw [Nat.pow_add]
  have hP : 2^(4*j)=16^j := by rw [Nat.pow_mul]
  have hg := d234_burst_growth s (by omega)
  have hcoef : 2*(416*m+3968)≤72*16^s := by
    rw [hm]
    omega
  have hb :
      2*((416*m+3968)*2^(4*j)-3) ≤
        72*16^m+24*m+253+12*j := by
    have hh := Nat.mul_le_mul_right (16^j) hcoef
    rw [hP,hX]
    calc
      2*((416*m+3968)*16^j-3) ≤ 2*(416*m+3968)*16^j := by omega
      _ ≤ 72*(16^j*16^s) := by
        simpa [Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using hh
      _ ≤ 72*(16^j*16^s)+24*m+253+12*j := by omega
  let L := 2*s+5
  let y : Int := 72*(m:Int)+759+36*(j:Int)
  have hB : budget 0 y L≤1000*(s:Int)+4000 := by
    simp [budget,y,L,m,j]
    omega
  have h25 : 1≤(25:Int)^s := by
    have hh := Int.pow_pos (m:=s) (show (0:Int)<25 by decide)
    omega
  have h5 : (5:Int)^L=3125*25^s := by
    dsimp [L]
    rw [Int.pow_add,Int.pow_mul]
    change (25:Int)^s*3125=3125*25^s
    exact Int.mul_comm ..
  have hcap : 3*cap (budget 0 y L) L+39≤128^s*25^s := by
    rw [cap_eq,h5]
    have hh := Int.mul_le_mul_of_nonneg_right hB (show 0≤(25:Int)^s by omega)
    have hh' := Int.mul_le_mul_of_nonneg_right (d234_sep_growth s hs)
      (show 0≤(25:Int)^s by omega)
    have hmul : (25:Int)^s*budget 0 y L=budget 0 y L*25^s := Int.mul_comm ..
    have hdist :
        ((9375:Int)*(1000*s+4000)+40)*25^s =
          9375*((1000*s+4000)*25^s)+40*25^s := by
      grind +ring
    have hgoal :
        3*(3125*25^s*budget 0 y L)=
          9375*((25:Int)^s*budget 0 y L) := by
      grind +ring
    rw [hdist] at hh'
    rw [hgoal,hmul]
    have haux : (40:Int)≤40*25^s := by omega
    omega
  have hbig : (128:Int)^s*25^s≤16^j := by
    rw [←Int.mul_pow]
    change (3200:Int)^s≤16^j
    have h1 : (3200:Int)^s≤4096^s := by
      induction s with
      | zero => decide
      | succ s ih =>
        rw [Int.pow_succ,Int.pow_succ]
        have hp : 0≤(4096:Int)^s := Int.pow_nonneg (by decide)
        omega
    have h2 : (4096:Int)^s≤16^j := by
      dsimp [j]
      rw [Int.pow_add,Int.pow_mul]
      change (4096:Int)^s≤4096^s*16^t
      have hp : 1≤(16:Int)^t := by
        have hh := Int.pow_pos (m:=t) (show (0:Int)<16 by decide)
        omega
      have hh := Int.mul_le_mul_of_nonneg_left hp
        (show 0≤(4096:Int)^s from Int.pow_nonneg (by decide))
      rw [Int.mul_one] at hh
      exact hh
    omega
  have hsep :
      3*cap (budget 0 y L) L+39<(16:Int)^j := by
    have hp : 0<(16:Int)^j := Int.pow_pos (by decide)
    omega
  obtain ⟨k,p,hk,hkn,hr,hs'⟩ :=
    d234_even_second_return m s j rfl (by dsimp [m,j]; omega)
      (by rw [hm]; exact hmod) hb
      (by simpa [L,y] using hsep)
  rw [hm] at hkn hr
  exact ⟨k,p,hk,hkn,hr,hs'⟩

#print axioms d234_post_m
#print axioms d234_even_second_return
#print axioms d234_large_non8

end BB429.CoarseExit
