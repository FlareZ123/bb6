import BB429Rank
import Lean.Elab.Tactic.Omega

namespace BB429.LowReturnBand

def phase (u d : Nat) : State := (u,u+12+d)

private theorem stepF (u w : Nat) (h : 2*u+3 ≤ w) :
    next (u,w) = some (2*u+3,w-2*u-3) := by simp [next,h]

private theorem stepOe (u w : Nat) (h : w+1 < 2*u)
    (hw : w%2=1) (hd : 4 ≤ u-w/2) (he : (u-w/2)%2=0)
    (hw1 : 1 < w) :
    next (u,w) = some (u-w/2+7,2*w-4) := by
  have h0 : ¬ w ≥ 2*u+3 := by omega
  have h1 : w ≠ 2*u+2 := by omega
  have h2 : w ≠ 2*u+1 := by omega
  have h3 : w ≠ 2*u := by omega
  have h4 : w%2 ≠ 0 := by omega
  have h5 : u-w/2 ≠ 1 := by omega
  have h6 : u-w/2 ≠ 2 := by omega
  have h7 : w ≠ 1 := by omega
  simp [next,h0,h1,h2,h3,h4,h5,h6,he,h7]

private theorem stepOo (u w : Nat) (h : w+1 < 2*u)
    (hw : w%2=1) (hd : 3 ≤ u-w/2) (he : (u-w/2)%2=1) :
    next (u,w) = some (u-w/2+3,2*w) := by
  have h0 : ¬ w ≥ 2*u+3 := by omega
  have h1 : w ≠ 2*u+2 := by omega
  have h2 : w ≠ 2*u+1 := by omega
  have h3 : w ≠ 2*u := by omega
  have h4 : w%2 ≠ 0 := by omega
  have h5 : u-w/2 ≠ 1 := by omega
  have h6 : u-w/2 ≠ 2 := by omega
  have h7 : (u-w/2)%2 ≠ 0 := by omega
  simp [next,h0,h1,h2,h3,h4,h5,h6,h7]

private theorem stepEe (u w : Nat) (h : w < 2*u)
    (hw : w%2=0) (hd : 2 ≤ u-w/2) (he : (u-w/2)%2=0) :
    next (u,w) = some (11,2*u+w-2) := by
  have h0 : ¬ w ≥ 2*u+3 := by omega
  have h1 : w ≠ 2*u+2 := by omega
  have h2 : w ≠ 2*u+1 := by omega
  have h3 : w ≠ 2*u := by omega
  have h5 : u-w/2 ≠ 1 := by omega
  simp [next,h0,h1,h2,h3,hw,h5,he]

-- The four-step low-side cycle Oe F Oo F.
theorem cycle (u d : Nat) (hd : 6 ≤ d) (he : d % 2 = 0)
    (hp : (u+1)%4 = d%4) (hu : 5*d+7 ≤ u) :
    run 4 (phase u d) = some (phase (u+8-5*d) (16*d)) := by
  have h1 : next (phase u d) = some ((u+3-d)/2, 2*u+20+2*d) := by
    unfold phase
    rw [stepOe _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h2 : next ((u+3-d)/2, 2*u+20+2*d) = some (u+6-d,u+14+3*d) := by
    rw [stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h3 : next (u+6-d,u+14+3*d) = some ((u+5-5*d)/2, 2*u+28+6*d) := by
    rw [stepOo _ _ (by omega) (by omega) (by omega) (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h4 : next ((u+5-5*d)/2, 2*u+28+6*d) = some (phase (u+8-5*d) (16*d)) := by
    unfold phase
    rw [stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  simp [run,h1,h2,h3,h4]

theorem cycle_phase (u d : Nat) (hp : (u+1)%4=d%4)
    (hu : 5*d+7 ≤ u) : ((u+8-5*d)+1)%4=(16*d)%4 := by omega

-- Terminal low-side band: the preceding cycle is followed by F,Eeven.
theorem terminal (u d : Nat) (hd : 6 ≤ d) (he : d%2=0)
    (hp : (u+1)%4=d%4) (hu : 5*d+7 ≤ u)
    (hlo : u ≤ 21*d+1) (hhi : 41*d ≤ 5*u+33) :
    run 6 (phase u d) = some (11, 3*u+37+d) := by
  have h5 : next (phase (u+8-5*d) (16*d)) = some (2*u+19-10*d, 21*d+1-u) := by
    unfold phase
    rw [stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega
  have h6 : next (2*u+19-10*d,21*d+1-u) = some (11,3*u+37+d) := by
    rw [stepEe _ _ (by omega) (by omega) (by omega) (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    clear h5
    constructor
    · trivial
    · omega
  rw [show 6=4+2 by decide,run_add,cycle u d hd he hp hu]
  simp [run,h5,h6]

/-- Arbitrarily many low-side four-step cycles, checked from the final guard.
    No individual intermediate-cycle test is required. -/
theorem cycles (j u0 d0 u : Nat) (hd : 6 ≤ d0) (he : d0%2=0)
    (hp : (u0+1)%4=d0%4)
    (hcoord : 3*u0+d0+24*j = 3*u+d0*16^j)
    (hu : 5*(d0*16^j)+7 ≤ u) :
    run (4*j) (phase u0 d0) = some (phase u (d0*16^j)) ∧
    (u+1)%4=(d0*16^j)%4 ∧ (d0*16^j)%2=0 := by
  induction j generalizing u with
  | zero =>
    simp only [Nat.pow_zero,Nat.mul_one,Nat.mul_zero,Nat.add_zero] at hcoord hu ⊢
    have h : u=u0 := by omega
    subst u
    exact ⟨rfl,hp,he⟩
  | succ j ih =>
    let D := d0*16^j
    have hD : 6 ≤ D := by
      have h := Nat.le_mul_of_pos_right d0 (Nat.pow_pos (a:=16) (n:=j) (by decide))
      omega
    have hpow : d0*16^(j+1)=16*D := by
      simp only [Nat.pow_succ, D]
      rw [← Nat.mul_assoc, Nat.mul_comm (d0 * 16^j) 16]
    rw [hpow] at hcoord hu ⊢
    let v := u+5*D-8
    have hv : 5*D+7 ≤ v := by dsimp [v]; omega
    have hcv : 3*u0+d0+24*j=3*v+D := by dsimp [v]; omega
    obtain ⟨hr,hp',he'⟩ := ih v hcv hv
    have hcy := cycle v D hD he' hp' hv
    have hve : v+8-5*D=u := by dsimp [v]; omega
    rw [hve] at hcy
    refine ⟨?_,?_,by omega⟩
    · rw [show 4*(j+1)=4*j+4 by omega,run_add,hr]
      exact hcy
    · have h := cycle_phase v D hp' hv
      simpa [hve] using h

/-- A whole family of low-side returns, with exact macro count and endpoint. -/
theorem return_band (j u0 d0 u : Nat) (hd : 6 ≤ d0) (he : d0%2=0)
    (hp : (u0+1)%4=d0%4)
    (hcoord : 3*u0+d0+24*j=3*u+d0*16^j)
    (hu : 5*(d0*16^j)+7 ≤ u)
    (hlo : u ≤ 21*(d0*16^j)+1)
    (hhi : 41*(d0*16^j) ≤ 5*u+33) :
    run (4*j+6) (phase u0 d0) = some (11,3*u0+d0+24*j+37) := by
  obtain ⟨hr,hp',he'⟩ := cycles j u0 d0 u hd he hp hcoord hu
  have hD : 6 ≤ d0*16^j := by
    have h := Nat.le_mul_of_pos_right d0 (Nat.pow_pos (a:=16) (n:=j) (by decide))
    omega
  rw [run_add,hr]
  simp only [Option.bind_some]
  rw [terminal u (d0*16^j) hD he' hp' hu hlo hhi]
  rw [hcoord]
  rw [Nat.add_right_comm (3*u) 37 (d0*16^j)]

/-- A return test involving only the initial parameters and one exponent. -/
theorem return_test (j u0 d0 : Nat) (hd : 6 ≤ d0) (he : d0%2=0)
    (hp : (u0+1)%4=d0%4)
    (h1 : 16*(d0*16^j)+21 ≤ 3*u0+d0+24*j)
    (h2 : 3*u0+d0+24*j ≤ 64*(d0*16^j)+3)
    (h3 : 128*(d0*16^j) ≤ 5*(3*u0+d0+24*j)+99) :
    run (4*j+6) (phase u0 d0) = some (11,3*u0+d0+24*j+37) := by
  let C := 3*u0+d0+24*j
  let D := d0*16^j
  have hmod : D%3=d0%3 := by
    dsimp [D]
    rw [Nat.mul_mod, Nat.pow_mod]
    simp
  have hCD : C%3=D%3 := by dsimp [C]; omega
  let u := (C-D)/3
  have hc : 3*u+D=C := by dsimp [u]; omega
  exact return_band j u0 d0 u hd he hp hc.symm (by omega) (by omega) (by omega)

/-- A first-branch burst from an arbitrary section, checked at the endpoint. -/
theorem section_burst (a k W u w : Nat) (hu : u+3=(a+3)*2^k)
    (hr : 2*u+w=2*a+W+3*k) : run k (a,W) = some (u,w) := by
  induction k generalizing u w with
  | zero =>
    simp at hu hr
    have h : u=a := by omega
    subst u
    have hw : w=W := by omega
    subst w
    rfl
  | succ k ih =>
    let v := (a+3)*2^k-3
    have hp : 3 ≤ (a+3)*2^k := by
      have h := Nat.le_mul_of_pos_right (a+3) (Nat.pow_pos (a:=2) (n:=k) (by decide))
      omega
    have hv : v+3=(a+3)*2^k := by dsimp [v]; omega
    have he : u=2*v+3 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc] at hu
      omega
    have hp' : 2*v+(w+u)=2*a+W+3*k := by omega
    have hrun := ih v (w+u) hv hp'
    simp only [run,hrun,Option.bind_some]
    rw [stepF _ _ (by omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    omega

theorem zero_burst (k W u w : Nat) (hu : u+3=3*2^k)
    (hr : 2*u+w=W+3*k) : run k (0,W) = some (u,w) := by
  exact section_burst 0 k W u w hu (by simpa using hr)

/-- Direct zero-section test: a certified F burst followed by a low-side return. -/
theorem zero_return (k j W u d : Nat) (hu : u+3=3*2^k)
    (hr : 3*u+12+d=W+3*k)
    (hd : 6 ≤ d) (he : d%2=0) (hp : (u+1)%4=d%4)
    (h1 : 16*(d*16^j)+21 ≤ 3*u+d+24*j)
    (h2 : 3*u+d+24*j ≤ 64*(d*16^j)+3)
    (h3 : 128*(d*16^j) ≤ 5*(3*u+d+24*j)+99) :
    run (k+4*j+6) (0,W) = some (11,W+3*k+24*j+25) := by
  have hb : run k (0,W)=some (phase u d) := by
    apply zero_burst k W u (u+12+d) hu
    omega
  rw [show k+4*j+6=k+(4*j+6) by omega,run_add,hb]
  simp only [Option.bind_some]
  rw [return_test j u d hd he hp h1 h2 h3]
  simp only [Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · omega

private theorem scale_ge (m : Nat) : 16*m ≤ 16^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.pow_succ]
    have h : 0 < 16^m := Nat.pow_pos (by decide)
    omega

/-- Uniform geometric subbands of the low side. For X=16^m, the
    scaled deviation D=d*16^j lies between 1.5X and 2.5X. -/
theorem zero_scale_band (m j d : Nat) (hm : 1 ≤ m) (hj : j < m)
    (hd : 6 ≤ d) (hp : d%4=2)
    (hlo : 3*16^m ≤ 2*(d*16^j))
    (hhi : 2*(d*16^j) ≤ 5*16^m) :
    run (4*m+4*j+9) (0,72*16^m+d-(12*m+6)) =
      some (11,72*16^m+d+24*j+28) := by
  let X := 16^m
  let D := d*16^j
  let W := 72*X+d-(12*m+6)
  let u := 24*X-3
  have hX : 16*m ≤ X := scale_ge m
  have hD : d ≤ D := Nat.le_mul_of_pos_right d (Nat.pow_pos (a:=16) (n:=j) (by decide))
  have hpow : 2^(4*m+3)=8*X := by
    rw [Nat.pow_add,Nat.pow_mul]
    change 16^m*8=8*X
    exact Nat.mul_comm _ _
  have hpu : (u+1)%4=d%4 := by
    dsimp [u]
    omega
  have hbur : u+3=3*2^(4*m+3) := by rw [hpow]; dsimp [u]; omega
  have hr : 3*u+12+d=W+3*(4*m+3) := by dsimp [u,W]; omega
  have hret := zero_return (4*m+3) j W u d hbur hr hd (by omega) hpu
    (by dsimp [u]; omega) (by dsimp [u]; omega) (by dsimp [u]; omega)
  have htime : 4*m+3+4*j+6=4*m+4*j+9 := by omega
  rw [htime] at hret
  change run (4*m+4*j+9) (0,W)=some (11,72*X+d+24*j+28)
  rw [hret]
  simp only [Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · dsimp [W]; omega

private theorem stepEo (u w : Nat) (h : w < 2*u)
    (hw : w%2=0) (hd : 3 ≤ u-w/2) (he : (u-w/2)%2=1) :
    next (u,w) = some (0,2*u+w+10) := by
  have h0 : ¬ w ≥ 2*u+3 := by omega
  have h1 : w ≠ 2*u+2 := by omega
  have h2 : w ≠ 2*u+1 := by omega
  have h3 : w ≠ 2*u := by omega
  have h5 : u-w/2 ≠ 1 := by omega
  have h6 : (u-w/2)%2 ≠ 0 := by omega
  simp [next,h0,h1,h2,h3,hw,h5,h6]

private theorem scale_ge3 (m : Nat) (hm : 3 ≤ m) : 1024*m ≤ 16^m := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h : 3 ≤ m
    · rw [Nat.pow_succ]
      have h' := ih h
      omega
    · have h' : m=2 := by omega
      subst m
      decide

/-- The eleven endpoint of the geometric band returns to zero. -/
theorem eleven_scale_return (m j d : Nat) (hm : 3 ≤ m) (hj : j<m)
    (hd : 6 ≤ d) (hp : d%4=2) (hhi : 2*d ≤ 5*16^m) :
    run (4*m+3) (11,72*16^m+d+24*j+28) =
      some (0,72*16^m+d+24*j+12*m+70) := by
  let X := 16^m
  let V := 72*X+d+24*j+28
  let u := 28*X-3
  let w := 16*X+d+24*j+12*m+59
  have hX : 1024*m ≤ X := scale_ge3 m hm
  have hpow : 2^(4*m+1)=2*X := by
    rw [Nat.pow_add,Nat.pow_mul]
    change 16^m*2=2*X
    exact Nat.mul_comm _ _
  have hbur : u+3=(11+3)*2^(4*m+1) := by rw [hpow]; dsimp [u]; omega
  have hr : 2*u+w=2*11+V+3*(4*m+1) := by dsimp [u,w,V]; omega
  have hb := section_burst 11 (4*m+1) V u w hbur hr
  have h1 : next (u,w)=some (u-w/2+3,2*w) := by
    apply stepOo <;> dsimp [u,w] <;> omega
  have h2 : next (u-w/2+3,2*w)=some (0,72*X+d+24*j+12*m+70) := by
    rw [stepEo _ _ (by dsimp [u,w]; omega) (by omega)
      (by dsimp [u,w]; omega) (by dsimp [u,w]; omega)]
    simp only [Option.some.injEq,Prod.mk.injEq]
    constructor
    · trivial
    · dsimp [u,w]; omega
  change run (4*m+3) (11,V)=some (0,72*X+d+24*j+12*m+70)
  rw [show 4*m+3=(4*m+1)+2 by omega,run_add,hb]
  simp [run,h1,h2]

/-- Two-section return translates the zero parameter by a constant. -/
theorem zero_two_section_pump (m j d : Nat) (hm : 3 ≤ m) (hj : j<m)
    (hd : 6 ≤ d) (hp : d%4=2)
    (hlo : 3*16^m ≤ 2*(d*16^j))
    (hhi : 2*(d*16^j) ≤ 5*16^m) :
    run (8*m+4*j+12) (0,72*16^m+d-(12*m+6)) =
      some (0,72*16^m+(d+(24*m+24*j+76))-(12*m+6)) := by
  have hD : d ≤ d*16^j := Nat.le_mul_of_pos_right d (Nat.pow_pos (a:=16) (n:=j) (by decide))
  have hX := scale_ge m
  have h1 := zero_scale_band m j d (by omega) hj hd hp hlo hhi
  have h2 := eleven_scale_return m j d hm hj hd hp (by omega)
  rw [show 8*m+4*j+12=(4*m+4*j+9)+(4*m+3) by omega,run_add,h1]
  simp only [Option.bind_some]
  rw [h2]
  simp only [Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · omega

/-- Repeat the translation arbitrarily many times. Only the first and last
    starting deviations need to be tested. -/
theorem repeat_pump (m j d r : Nat) (hm : 3 ≤ m) (hj : j<m)
    (hd : 6 ≤ d) (hp : d%4=2)
    (hlo : 3*16^m ≤ 2*(d*16^j))
    (hhi : 2*((d+(24*m+24*j+76)*(r-1))*16^j) ≤ 5*16^m) :
    run ((8*m+4*j+12)*r) (0,72*16^m+d-(12*m+6)) =
      some (0,72*16^m+(d+(24*m+24*j+76)*r)-(12*m+6)) := by
  let L := 8*m+4*j+12
  let D := 24*m+24*j+76
  let X := 16^m
  induction r with
  | zero => simp [run]
  | succ r ih =>
    have h' : 2*((d+D*(r-1))*16^j) ≤ 5*X := by
      have h1 : D*(r-1) ≤ D*r := Nat.mul_le_mul_left _ (by omega)
      have h2 := Nat.mul_le_mul_right (16^j) (show d+D*(r-1) ≤ d+D*r by omega)
      change 2*((d+D*((r+1)-1))*16^j) ≤ 5*X at hhi
      simp only [Nat.add_sub_cancel] at hhi
      omega
    have hr := ih h'
    have hd' : 6 ≤ d+D*r := by omega
    have hp' : (d+D*r)%4=2 := by
      rw [Nat.add_mod, Nat.mul_mod]
      have hD : D%4=0 := by dsimp [D]; omega
      simp [hp,hD]
    have hlow : 3*X ≤ 2*((d+D*r)*16^j) := by
      have h := Nat.mul_le_mul_right (16^j) (show d≤d+D*r by omega)
      omega
    have hhigh : 2*((d+D*r)*16^j) ≤ 5*X := by simpa using hhi
    have hstep := zero_two_section_pump m j (d+D*r) hm hj hd' hp' hlow hhigh
    change run (L*(r+1)) (0,72*X+d-(12*m+6)) =
      some (0,72*X+(d+D*(r+1))-(12*m+6))
    rw [Nat.mul_succ,run_add,hr]
    simp only [Option.bind_some]
    change run L (0,72*X+(d+D*r)-(12*m+6)) = _
    rw [hstep,Nat.mul_succ]
    rw [Nat.add_assoc d (D*r) D]

#print axioms cycle
#print axioms terminal
#print axioms cycles
#print axioms return_band
#print axioms return_test
#print axioms zero_burst
#print axioms zero_return
#print axioms zero_scale_band
#print axioms eleven_scale_return
#print axioms zero_two_section_pump
#print axioms repeat_pump

end BB429.LowReturnBand
