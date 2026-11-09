import FeederSixStep
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
set_option maxRecDepth 8192
namespace CascadeFeederSix
open CascadeSweep

theorem pow_period486 (m : Nat) :
  2^(m+486)%243 = 2^m%243 := by
  rw [Nat.pow_add,Nat.mul_mod]
  have hp : (2:Nat)^486%243=1 := by decide
  rw [hp]
  simp

theorem pow_486_base (r t : Nat) :
  2^(r+486*t)%243 = 2^r%243 := by
  induction t with
  | zero => simp
  | succ t ih =>
    have he : r+486*(t+1) = (r+486*t)+486 := by omega
    rw [he,pow_period486,ih]

theorem pow_n_residue (n r : Nat) (hn : 2≤r)
  (hr : n%486=r) :
    2^(n-2)%243 = 2^(r-2)%243 := by
  let t := n/486
  have hrdiv : n=r+486*t := by
    have h := Nat.mod_add_div n 486
    dsimp [t]
    omega
  have he : n-2=(r-2)+486*t := by omega
  rw [he,pow_486_base]

/-- Arithmetic of the four conjecturally newly dead feeder classes. -/
theorem four_residue_numeric (n : Nat)
  (hr : n%486=76 ∨ n%486=238 ∨ n%486=275 ∨ n%486=437) :
  let p := 2^(n-2)
  (n%243=76 ∧ p%243=112) ∨
  (n%243=238 ∧ p%243=112) ∨
  (n%243=32 ∧ p%243=89) ∨
  (n%243=194 ∧ p%243=89) := by
  change (n%243=76 ∧ (2^(n-2))%243=112) ∨
    (n%243=238 ∧ (2^(n-2))%243=112) ∨
    (n%243=32 ∧ (2^(n-2))%243=89) ∨
    (n%243=194 ∧ (2^(n-2))%243=89)
  rcases hr with h|h|h|h
  · have hp := pow_n_residue n 76 (by decide) h
    have hn : n%243=76 := by omega
    have hpv : (2^(n-2))%243=112 := by rw [hp]
    exact Or.inl ⟨hn,hpv⟩
  · have hp := pow_n_residue n 238 (by decide) h
    have hn : n%243=238 := by omega
    have hpv : (2^(n-2))%243=112 := by rw [hp]
    exact Or.inr (Or.inl ⟨hn,hpv⟩)
  · have hp := pow_n_residue n 275 (by decide) h
    have hn : n%243=32 := by omega
    have hpv : (2^(n-2))%243=89 := by rw [hp]
    exact Or.inr (Or.inr (Or.inl ⟨hn,hpv⟩))
  · have hp := pow_n_residue n 437 (by decide) h
    have hn : n%243=194 := by omega
    have hpv : (2^(n-2))%243=89 := by rw [hp]
    exact Or.inr (Or.inr (Or.inr ⟨hn,hpv⟩))

theorem growth (n : Nat) (hn : 76≤n) :
  10000*n+10000 ≤ 2^(n-2) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : 76≤n
    · have hp := ih h
      have he : (n+1)-2=(n-2)+1 := by omega
      rw [he,Nat.pow_succ]
      omega
    · have he : n=75 := by omega
      subst n
      decide

theorem h_divnine (n p h : Nat)
 (hl : 9*h+43*n+60=40*p)
 (hm : (n%243=76 ∧ p%243=112) ∨
  (n%243=238 ∧ p%243=112) ∨
  (n%243=32 ∧ p%243=89) ∨
  (n%243=194 ∧ p%243=89)) : (2*h+5)%9=0 := by
 rcases hm with hh|hh|hh|hh
 all_goals omega

theorem mod_x (n p x : Nat)
 (hm : (n%243=76 ∧ p%243=112) ∨
  (n%243=238 ∧ p%243=112) ∨
  (n%243=32 ∧ p%243=89) ∨
  (n%243=194 ∧ p%243=89))
 (hl : 9*x+17*n+39=56*p) : x%3≠2 := by
 rcases hm with hh|hh|hh|hh
 all_goals omega

theorem mod_h (n p h : Nat)
 (hm : (n%243=76 ∧ p%243=112) ∨
  (n%243=238 ∧ p%243=112) ∨
  (n%243=32 ∧ p%243=89) ∨
  (n%243=194 ∧ p%243=89))
 (hl : 9*h+43*n+60=40*p) : (2*h+5)%27≠0 := by
 rcases hm with hh|hh|hh|hh
 all_goals omega

theorem mod_a (n p a : Nat)
 (hm : (n%243=76 ∧ p%243=112) ∨
  (n%243=238 ∧ p%243=112) ∨
  (n%243=32 ∧ p%243=89) ∨
  (n%243=194 ∧ p%243=89))
 (hl : 81*a+425*n+381=158*p) : a%3≠2 := by
 rcases hm with hh|hh|hh|hh
 all_goals omega

theorem mod_b (n p b : Nat)
 (hm : (n%243=76 ∧ p%243=112) ∨
  (n%243=238 ∧ p%243=112) ∨
  (n%243=32 ∧ p%243=89) ∨
  (n%243=194 ∧ p%243=89))
 (hl : 81*b+931*n+438=154*p) : b%3≠2 := by
 rcases hm with hh|hh|hh|hh
 all_goals omega

theorem mod_c (n p c : Nat)
 (hm : (n%243=76 ∧ p%243=112) ∨
  (n%243=238 ∧ p%243=112) ∨
  (n%243=32 ∧ p%243=89) ∨
  (n%243=194 ∧ p%243=89))
 (hl : 81*c+1943*n+552=146*p) : c%3≠2 := by
 rcases hm with hh|hh|hh|hh
 all_goals omega

theorem mod_d (n p d : Nat)
 (hm : (n%243=76 ∧ p%243=112) ∨
  (n%243=238 ∧ p%243=112) ∨
  (n%243=32 ∧ p%243=89) ∨
  (n%243=194 ∧ p%243=89))
 (hl : 81*d+3967*n+780=130*p) : d%3≠2 := by
 rcases hm with hh|hh|hh|hh
 all_goals omega

theorem mod_e (n p e : Nat)
 (hm : (n%243=76 ∧ p%243=112) ∨
  (n%243=238 ∧ p%243=112) ∨
  (n%243=32 ∧ p%243=89) ∨
  (n%243=194 ∧ p%243=89))
 (hl : 81*e+8015*n+1236=98*p) : e%3≠2 := by
 rcases hm with hh|hh|hh|hh
 all_goals omega

theorem geom_x (n p x : Nat)
 (hbig : 10000*n+10000≤p)
 (hl : 9*x+17*n+39=56*p) : (6*p≤x+1 ∧ x+3≤8*p) := by
 omega

theorem geom_h (n p h : Nat)
 (hbig : 10000*n+10000≤p)
 (hl : 9*h+43*n+60=40*p) : (4*p≤h ∧ 2*h+5<9*p) := by
 omega

theorem geom_a (n p a : Nat)
 (hbig : 10000*n+10000≤p)
 (hl : 81*a+425*n+381=158*p) : (6*p≤4*a+4 ∧ 4*a+12≤8*p) := by
 omega

theorem geom_b (n p b : Nat)
 (hbig : 10000*n+10000≤p)
 (hl : 81*b+931*n+438=154*p) : (6*p≤4*b+4 ∧ 4*b+12≤8*p) := by
 omega

theorem geom_c (n p c : Nat)
 (hbig : 10000*n+10000≤p)
 (hl : 81*c+1943*n+552=146*p) : (6*p≤4*c+4 ∧ 4*c+12≤8*p) := by
 omega

theorem geom_d (n p d : Nat)
 (hbig : 10000*n+10000≤p)
 (hl : 81*d+3967*n+780=130*p) : (6*p≤4*d+4 ∧ 4*d+12≤8*p) := by
 omega

theorem geom_e (n p e : Nat)
 (hbig : 10000*n+10000≤p)
 (hl : 81*e+8015*n+1236=98*p) : (4*p≤4*e ∧ 4*e+4<6*p) := by
 omega

theorem affine_a (n p j h z a : Nat) (hj : j+4=n)
 (hpj : p=4*2^j)
 (hlin : 9*h+43*n+60=40*p)
 (hz : 9*z=2*h+5)
 (haEq : 4*z=8*2^j+a+j+5) :
  81*a+425*n+381=158*p := by omega

theorem affine_b (n p j a b : Nat) (hj : j+4=n)
 (hpj : p=4*2^j)
 (hl : 81*a+425*n+381=158*p)
 (he : 2*a=8*2^j+b+j) :
  81*b+931*n+438=154*p := by omega

theorem affine_c (n p j b c : Nat) (hj : j+4=n)
 (hpj : p=4*2^j)
 (hl : 81*b+931*n+438=154*p)
 (he : 2*b=8*2^j+c+j) :
  81*c+1943*n+552=146*p := by omega

theorem affine_d (n p j c d : Nat) (hj : j+4=n)
 (hpj : p=4*2^j)
 (hl : 81*c+1943*n+552=146*p)
 (he : 2*c=8*2^j+d+j) :
  81*d+3967*n+780=130*p := by omega

theorem affine_e (n p j d e : Nat) (hj : j+4=n)
 (hpj : p=4*2^j)
 (hl : 81*d+3967*n+780=130*p)
 (he : 2*d=8*2^j+e+j) :
  81*e+8015*n+1236=98*p := by omega

theorem positive_even (n p j v : Nat)
 (hbig : 10000*n+10000≤p)
 (hpj : p=4*2^j)
 (hj : j+4=n)
 (hlo : 6*p≤4*v+4) : 8*2^j+j≤2*v := by
 omega

end CascadeFeederSix
