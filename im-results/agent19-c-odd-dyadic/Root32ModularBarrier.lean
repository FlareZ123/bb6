import MixedStripSource
import ShadowWords

namespace BB6.Agent19RootModularBarrier
open BB6.Agent19DirectBarrier BB6.Agent19MixedStrip
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option exponentiation.threshold 512

/-- These are actual CLine section returns, not shadow edges. -/
inductive Edge : Nat → Nat → Nat → Nat → Prop
  | direct (a k : Nat) (hk : 8≤k) (ha : 2*k+8≤a) : Edge a k (a-2*k) (2*k+2)
  | high2 (a k : Nat) (ha : 8≤a) (hk : 8≤k) (h1 : a+8≤2*k) (h2 : 2*k+8≤3*a) :
      Edge a k (3*a-2*k+1+2*(a%2)) (2*k-a+3-a%2)
  | high3 (a k : Nat) (ha : 8≤a) (hp : a%2=0) (h1 : 3*a+6≤2*k) (h2 : 2*k+8≤7*a) :
      Edge a k (7*a-2*k+6) (2*k-3*a+2)

theorem edge_closed (J : State → Prop) (hc : Closed J) {a k x y : Nat} (he : Edge a k x y) (hj : J (a,k,0)) : J (x,y,0) := by
  cases he with
  | direct hk ha => exact source_direct_closed J hc _ _ hk ha hj
  | high2 ha hk h1 h2 => exact source_high2_closed J hc _ _ ha hk h1 h2 hj
  | high3 ha hp h1 h2 => exact source_high3_even_closed J hc _ _ ha hp h1 h2 hj

/-- A backwards path every point of which is accepted by J. -/
inductive AcceptedPath (J : State → Prop) : Nat → Nat → Nat → Prop
  | zero (a k : Nat) (ha : 8≤a) (hk : 8≤k) (hj : J (a,k,0)) : AcceptedPath J 0 a k
  | step {n a k x y : Nat} (hx : 8≤x) (hy : 8≤y) (hj : J (x,y,0))
      (he : Edge a k x y) (tail : AcceptedPath J n a k) : AcceptedPath J (n+1) x y

theorem path_accepted {J : State → Prop} {n a k : Nat} (h : AcceptedPath J n a k) : J (a,k,0) := by
  cases h with
  | zero _ _ _ _ hj => exact hj
  | step _ _ hj _ _ => exact hj

theorem prepend (J : State → Prop) (hc : Closed J) {n a k x y : Nat} (hx : 8≤x) (hy : 8≤y)
    (he : Edge a k x y) (tail : AcceptedPath J n a k) : AcceptedPath J (n+1) x y :=
  .step hx hy (edge_closed J hc he (path_accepted tail)) he tail

/-- Long dyadic tails are accepted by every mixed finite quotient. -/
theorem direct_tail (p L : Nat) (hp : 2≤p) (ho : L%2=1) (J : State → Prop)
    (hj : J (5,0,1)) (hc : Closed J) (hcon : Congruent (2^p*L) (secPred J))
    (n a k : Nat) (ha : 8≤a) (hk : 10*2^n≤k+2) (hd : 2^(p+n)∣k+2) : AcceptedPath J n a k := by
  induction n generalizing a k with
  | zero =>
    have hk' : 8≤k := by simp at hk; omega
    exact .zero a k ha hk' (source_mixed_strip_forced p L hp ho J hj hc hcon a k ha hk' (by simpa using hd))
  | succ n ih =>
    obtain ⟨h,he⟩ := hd
    have hpow : 2^(p+(n+1))=2^(p+n)*2 := by rw [show p+(n+1)=p+n+1 by omega,Nat.pow_succ]
    rw [hpow,Nat.mul_right_comm] at he
    let l := (k+2)/2-2
    let b := a+k-2
    have h2 : 2≤2^n*2 := by have := Nat.two_pow_pos n; omega
    have hK : 8≤k := by rw [Nat.pow_succ] at hk; omega
    have hL : l+2=2^(p+n)*h := by dsimp [l]; rw [he]; omega
    have hdiv : 2^(p+n)∣l+2 := ⟨h,hL⟩
    have hkEq : k=2*l+2 := by dsimp [l] at *; omega
    have hll : 10*2^n≤l+2 := by rw [Nat.pow_succ] at hk; omega
    have hb : 2*l+8≤b := by dsimp [b]; omega
    have hle : 8≤l := by have := Nat.two_pow_pos n; omega
    have he' : Edge b l a k := by
      have hE := Edge.direct b l hle hb
      have hbb : b-2*l=a := by dsimp [b]; omega
      rw [hbb,←hkEq] at hE
      exact hE
    exact prepend J hc ha hK he' (ih b l (by omega) hll hdiv)

/-- Exact common ten-return D-prefix, in true section coordinates. -/
theorem d_prefix (J : State → Prop) (hc : Closed J) (t n : Nat)
    (tail : AcceptedPath J n (2861931660*t+767469219) (2092249530*t+561067594)) :
    AcceptedPath J (n+10) (1469153280*t+393975148) (2788638720*t+747814654) := by
  have h9 := Edge.high2 (2861931660*t+767469219) (2092249530*t+561067594) (by omega) (by omega) (by omega) (by omega)
  have h9x : 3*(2861931660*t+767469219)-2*(2092249530*t+561067594)+1+2*((2861931660*t+767469219)%2)=4401295920*t+1180272472 := by omega
  have h9y : 2*(2092249530*t+561067594)-(2861931660*t+767469219)+3-(2861931660*t+767469219)%2=1322567400*t+354665971 := by omega
  rw [h9x,h9y] at h9
  have p9 := prepend J hc (by omega) (by omega) h9 tail
  clear h9 h9x h9y tail
  have h8 := Edge.direct (4401295920*t+1180272472) (1322567400*t+354665971) (by omega) (by omega)
  have h8x : (4401295920*t+1180272472)-2*(1322567400*t+354665971)=1756161120*t+470940530 := by omega
  have h8y : 2*(1322567400*t+354665971)+2=2645134800*t+709331944 := by omega
  rw [h8x,h8y] at h8
  have p8 := prepend J hc (by omega) (by omega) h8 p9
  clear h8 h8x h8y p9
  have h7 := Edge.high3 (1756161120*t+470940530) (2645134800*t+709331944) (by omega) (by omega) (by omega) (by omega)
  have h7x : 7*(1756161120*t+470940530)-2*(2645134800*t+709331944)+6=7002858240*t+1877919828 := by omega
  have h7y : 2*(2645134800*t+709331944)-3*(1756161120*t+470940530)+2=21786240*t+5842300 := by omega
  rw [h7x,h7y] at h7
  have p7 := prepend J hc (by omega) (by omega) h7 p8
  clear h7 h7x h7y p8
  have h6 := Edge.direct (7002858240*t+1877919828) (21786240*t+5842300) (by omega) (by omega)
  have h6x : 7002858240*t+1877919828-2*(21786240*t+5842300)=6959285760*t+1866235228 := by omega
  have h6y : 2*(21786240*t+5842300)+2=43572480*t+11684602 := by omega
  rw [h6x,h6y] at h6
  have p6 := prepend J hc (by omega) (by omega) h6 p7
  clear h6 h6x h6y p7
  have h5 := Edge.direct (6959285760*t+1866235228) (43572480*t+11684602) (by omega) (by omega)
  have h5x : 6959285760*t+1866235228-2*(43572480*t+11684602)=6872140800*t+1842866024 := by omega
  have h5y : 2*(43572480*t+11684602)+2=87144960*t+23369206 := by omega
  rw [h5x,h5y] at h5
  have p5 := prepend J hc (by omega) (by omega) h5 p6
  clear h5 h5x h5y p6
  have h4 := Edge.direct (6872140800*t+1842866024) (87144960*t+23369206) (by omega) (by omega)
  have h4x : 6872140800*t+1842866024-2*(87144960*t+23369206)=6697850880*t+1796127612 := by omega
  have h4y : 2*(87144960*t+23369206)+2=174289920*t+46738414 := by omega
  rw [h4x,h4y] at h4
  have p4 := prepend J hc (by omega) (by omega) h4 p5
  clear h4 h4x h4y p5
  have h3 := Edge.direct (6697850880*t+1796127612) (174289920*t+46738414) (by omega) (by omega)
  have h3x : 6697850880*t+1796127612-2*(174289920*t+46738414)=6349271040*t+1702650784 := by omega
  have h3y : 2*(174289920*t+46738414)+2=348579840*t+93476830 := by omega
  rw [h3x,h3y] at h3
  have p3 := prepend J hc (by omega) (by omega) h3 p4
  clear h3 h3x h3y p4
  have h2 := Edge.direct (6349271040*t+1702650784) (348579840*t+93476830) (by omega) (by omega)
  have h2x : 6349271040*t+1702650784-2*(348579840*t+93476830)=5652111360*t+1515697124 := by omega
  have h2y : 2*(348579840*t+93476830)+2=697159680*t+186953662 := by omega
  rw [h2x,h2y] at h2
  have p2 := prepend J hc (by omega) (by omega) h2 p3
  clear h2 h2x h2y p3
  have h1 := Edge.direct (5652111360*t+1515697124) (697159680*t+186953662) (by omega) (by omega)
  have h1x : 5652111360*t+1515697124-2*(697159680*t+186953662)=4257792000*t+1141789800 := by omega
  have h1y : 2*(697159680*t+186953662)+2=1394319360*t+373907326 := by omega
  rw [h1x,h1y] at h1
  have p1 := prepend J hc (by omega) (by omega) h1 p2
  clear h1 h1x h1y p2
  have h0 := Edge.direct (4257792000*t+1141789800) (1394319360*t+373907326) (by omega) (by omega)
  have h0x : 4257792000*t+1141789800-2*(1394319360*t+373907326)=1469153280*t+393975148 := by omega
  have h0y : 2*(1394319360*t+373907326)+2=2788638720*t+747814654 := by omega
  rw [h0x,h0y] at h0
  exact prepend J hc (by omega) (by omega) h0 p1

def E (j : Nat) := 903171544+1761607680*j

private theorem pow_period (q : Nat) : (2^(420*q):Nat)%22155=1 := by
  induction q with
  | zero => decide
  | succ q ih =>
    rw [Nat.mul_succ,Nat.pow_add,Nat.mul_mod,ih,show (2^420:Nat)%22155=1 by decide]

theorem exact_root_exists (j : Nat) : ∃ t : Nat, 17300+22155*(t+j)=5*2^(E j) := by
  have hE : E j=184+420*(2150408+4194304*j) := by unfold E; omega
  have hmod : (5*2^(E j):Nat)%22155=17300 := by
    rw [hE,Nat.pow_add,←Nat.mul_assoc,Nat.mul_mod,pow_period]
  let Q := (5*2^(E j))/22155
  have hq : 17300+22155*Q=5*2^(E j) := by
    have h := Nat.mod_add_div (5*2^(E j)) 22155
    rw [hmod] at h
    exact h
  have hE2 : E j<2^(E j) := Nat.lt_pow_self (by decide)
  have hE3 : 22155*j+17300≤E j := by unfold E; omega
  have hj : j≤Q := by omega
  exact ⟨Q-j,by omega⟩

private theorem root_large (j t n : Nat) (hj : n+16≤j) (he : 17300+22155*(t+j)=5*2^(E j)) : 2^n≤t := by
  have hE : 22155*j+17300≤E j := by unfold E; omega
  have hE2 : E j<2^(E j) := Nat.lt_pow_self (by decide)
  have hE3 : n+16≤E j := by unfold E; omega
  have hp := Nat.pow_le_pow_right (by decide : 0<2) hE3
  rw [Nat.pow_add] at hp
  change 2^n*65536≤2^(E j) at hp
  omega

/-- The exact root32 family defeats any uniform path-fuel cutoff augmented
    by any fixed simultaneous finite congruence invariant. The witness j,t
    satisfy the authentic exponential equation; no materialized huge power. -/
theorem root32_mixed_no_uniform_depth (p L n : Nat) (hp : 2≤p) (ho : L%2=1)
    (J : State → Prop) (hj : J (5,0,1)) (hc : Closed J)
    (hcon : Congruent (2^p*L) (secPred J)) :
    ∃ j t : Nat, 17300+22155*(t+j)=5*2^(E j) ∧
      AcceptedPath J (n+10) (1469153280*t+393975148) (2788638720*t+747814654) := by
  obtain ⟨r,hr,hres⟩ := BB6.Agent19Scalar.odd_affine_residue 73577441805 37722959174 (p+n) (by decide)
  let j := r+2^(p+n)*(p+n+16)
  have hjm : j%2^(p+n)=r := by
    dsimp [j]
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr]
  have hjlarge : p+n+16≤j := by
    have h := Nat.mul_le_mul_right (p+n+16) (show 1≤2^(p+n) from Nat.two_pow_pos _)
    simp at h
    dsimp [j]; omega
  obtain ⟨t,he⟩ := exact_root_exists j
  have ht : 2^n≤t := root_large j t n (by omega) he
  have hshadow : 2^(p+n)∣46353788337150*j+23765464279620 := by
    have h := (hres j).mpr hjm
    have heq : 46353788337150*j+23765464279620=630*(37722959174+73577441805*j) := by omega
    rw [heq]
    exact Nat.dvd_mul_left_of_dvd h 630
  have hEq : 22155*(2092249530*t+561067594+2)+(46353788337150*j+23765464279620)=2092249530*(5*2^(E j)) := by rw [←he]; omega
  have hE : p+n≤E j := by unfold E; omega
  have hbig : 2^(p+n)∣2092249530*(5*2^(E j)) := Nat.dvd_mul_left_of_dvd (Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 hE) 5) 2092249530
  rw [←hEq] at hbig
  have hd : 2^(p+n)∣2092249530*t+561067594+2 := (Nat.Coprime.pow_left (p+n) (by decide : Nat.Coprime 2 22155)).dvd_of_dvd_mul_left ((Nat.dvd_add_iff_left hshadow).mpr hbig)
  refine ⟨j,t,he,d_prefix J hc t n ?_⟩
  exact direct_tail p L hp ho J hj hc hcon n _ _ (by omega) (by omega) hd

#print axioms edge_closed
#print axioms d_prefix
#print axioms exact_root_exists
#print axioms root32_mixed_no_uniform_depth
end BB6.Agent19RootModularBarrier
