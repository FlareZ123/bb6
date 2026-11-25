import Q0MacroCore

/-! The entire long odd-reset branch of #429 shares the q0 radix-16 graph.
    This module uses exactly the already-established Source interface. -/
namespace BB429Q0Macro
set_option maxHeartbeats 4000000

private theorem pow_succ_le_two (n : Nat) : n+1 ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

private theorem pow_succ_le_sixteen (n : Nat) : n+1 ≤ 16^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

private theorem pow_mod16 (n : Nat) (hn : 4 ≤ n) : 2^n % 16 = 0 := by
  rw [show n = 4+(n-4) by omega, Nat.pow_add]
  change (16*2^(n-4))%16=0
  omega

private theorem large_a (n a : Nat) (hn : 18 ≤ n)
    (h : a+3*(n/4)+6=3*2^n) : 300 ≤ a := by
  have hs := pow_succ_le_two (n-8)
  have hp : 2^n=256*2^(n-8) := by
    calc
      2^n = 2^(8+(n-8)) := by congr 1; omega
      _ = 256*2^(n-8) := by rw [Nat.pow_add]
  omega

variable {Reach : Nat → Nat → Prop}

private theorem phase3_shift (src : Source Reach) (a b : Nat)
    (ha : 29 ≤ a) (hp : (2*a+b)%4=3) (hr : Reach a b) :
    (a+3)%4=0 := by
  have hodd : a%2=1 := by
    by_cases he : a%2=0
    · have h := src.even8 a b (by omega) he hr
      omega
    · omega
  rcases src.odd_back a b (by omega) hodd hr with
    ⟨x,y,hxy,hx,hy⟩ | ⟨x,y,hxy,hx,hy,hm⟩
  · have ho : x%2=1 := by
      by_cases he : x%2=0
      · have h := src.even8 x y (by omega) he hxy
        omega
      · omega
    omega
  · omega

/-- After the compulsory first F inverse, parity selects FF or FE.
    The next phase-3 lookahead gives exactly the two modulo-16 possibilities. -/
theorem odd_reset_two_back (src : Source Reach) (a b : Nat)
    (ha : 300≤a) (ho : a%2=1) (hb : b+3=2*a) (hr : Reach a b) :
    (∃ x y, Reach x y ∧ 4*x+9=a ∧ 2*x+y+1=4*(a-2) ∧ (x+3)%4=0) ∨
    (∃ x y, Reach x y ∧ 4*x+23=5*a ∧ 2*x+y+1=4*(a-3) ∧ (x+3)%4=0) := by
  rcases src.odd_back a b (by omega) ho hr with
    ⟨u,v,huv,hu,hv⟩ | ⟨u,v,huv,hu,hv,hm⟩
  · by_cases hodd : u%2=1
    · rcases src.odd_back u v (by omega) hodd huv with
        ⟨x,y,hxy,hx,hy⟩ | ⟨x,y,hxy,hx,hy,hm⟩
      · have hphase : (2*x+y)%4=3 := by omega
        have hdiv := phase3_shift src x y (by omega) hphase hxy
        exact Or.inl ⟨x,y,hxy,by omega,by omega,hdiv⟩
      · omega
    · obtain ⟨x,y,hxy,hx,hy,hm⟩ := src.even_back u v (by omega) (by omega) huv
      have hphase : (2*x+y)%4=3 := by omega
      have hdiv := phase3_shift src x y (by omega) hphase hxy
      exact Or.inr ⟨x,y,hxy,by omega,by omega,hdiv⟩
  · omega

/-- A single theorem covers every large odd reset satisfying the exact
    terminal-burst equation. The two rays include residues 13/29 and 15/31.
    No fixed-depth or finite-parameter assumption is made. -/
theorem odd_reset_forces_path (src : Source Reach) (n a b : Nat)
    (hn : 18≤n) (ho : a%2=1) (hb : b+3=2*a)
    (heq : 4*a+3*n+15=3*2^(n+2)) (hr : Reach a b) :
    (∃ t, n=63+64*t ∧ Path (13+16*t) (53+48*t) (3+3*t)) ∨
    (∃ t, n=39+64*t ∧ Path (8+16*t) (36+48*t) (11+15*t)) := by
  have heq' : 4*a+3*n+15=12*2^n := by
    rw [Nat.pow_add] at heq
    omega
  have hnmod : n%4=3 := by omega
  let j := n/4
  have hn' : n=4*j+3 := by dsimp [j]; omega
  have hpow : a+3*j+6=3*2^n := by omega
  have ha : 300≤a := large_a n a hn (by simpa [j] using hpow)
  have hm16 := pow_mod16 n (by omega)
  rcases odd_reset_two_back src a b ha ho hb hr with
    ⟨A,B,hAB,hA,hB,hdiv⟩ | ⟨A,B,hAB,hA,hB,hdiv⟩
  · have hj : j%16=15 := by omega
    let t := j/16
    have ht : j=16*t+15 := by dsimp [t]; omega
    have hnt : n=63+64*t := by omega
    let m := 13+16*t
    let p := 53+48*t
    let y := 3+3*t
    have hnp : n=4*m+11 := by dsimp [m]; omega
    have hpw : 2^n=2048*16^m := by
      rw [hnp,Nat.pow_add,Nat.pow_mul]
      change 16^m*2048=2048*16^m
      omega
    have hlarge := pow_succ_le_sixteen m
    have hylo : y≤16^m := by dsimp [m,y] at *; omega
    have hplo : p≤6144*16^m := by dsimp [p,m] at *; omega
    let r := 6144*16^m-p
    let x := 384*16^m-y
    have h1 : r+p=16^m*6144 := by dsimp [r]; omega
    have h2 : x+y=16^m*384 := by dsimp [x]; omega
    have h3 : A+3=4*x := by rw [hpw] at hpow; dsimp [x,y]; omega
    have h4 : 2*A+B+1=4*r := by rw [hpw] at hpow; dsimp [r,p]; omega
    have h5 : 25*16^m≤x := by dsimp [x]; omega
    exact Or.inl ⟨t,hnt,lift_path src m A B r x p y 6144 384 hAB h3 h4 h5 h1 h2⟩
  · have hj : j%16=9 := by omega
    let t := j/16
    have ht : j=16*t+9 := by dsimp [t]; omega
    have hnt : n=39+64*t := by omega
    let m := 8+16*t
    let p := 36+48*t
    let y := 11+15*t
    have hnp : n=4*m+7 := by dsimp [m]; omega
    have hpw : 2^n=128*16^m := by
      rw [hnp,Nat.pow_add,Nat.pow_mul]
      change 16^m*128=128*16^m
      omega
    have hlarge := pow_succ_le_sixteen m
    have hylo : y≤2*16^m := by dsimp [m,y] at *; omega
    have hplo : p≤384*16^m := by dsimp [p,m] at *; omega
    let r := 384*16^m-p
    let x := 120*16^m-y
    have h1 : r+p=16^m*384 := by dsimp [r]; omega
    have h2 : x+y=16^m*120 := by dsimp [x]; omega
    have h3 : A+3=4*x := by rw [hpw] at hpow; dsimp [x,y]; omega
    have h4 : 2*A+B+1=4*r := by rw [hpw] at hpow; dsimp [r,p]; omega
    have h5 : 25*16^m≤x := by dsimp [x]; omega
    exact Or.inr ⟨t,hnt,lift_path src m A B r x p y 384 120 hAB h3 h4 h5 h1 h2⟩

/-- Both rays lie strictly inside the signed graph's cone. -/
theorem odd_reset_rays_interior (t : Nat) :
    0 < 3+3*t ∧ 3*(3+3*t)<53+48*t ∧
    0 < 11+15*t ∧ 3*(11+15*t)<36+48*t := by omega

#print axioms odd_reset_two_back
#print axioms odd_reset_forces_path
#print axioms odd_reset_rays_interior
end BB429Q0Macro
