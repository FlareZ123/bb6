import Lean
set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace CascadeGapTZero

theorem size200 (n : Nat) (hn : 20 ≤ n) : 200*n ≤ 2^(n-8) := by
  have h : ∀k : Nat, 200*(20+k) ≤ 2^(12+k) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show 12+(k+1)=12+k+1 by omega, Nat.pow_succ]
      omega
  have hn1 : n = 20+(n-20) := by omega
  have hn2 : n-8=12+(n-20) := by omega
  simpa only [←hn1, ←hn2] using h (n-20)

/-- Sharpen the published coarse 1973/1979 quotient corridor to 1974/1977. -/
theorem strong_interval (n s r d : Nat) (hn : 20 ≤ n) (hs : 200*n ≤ s)
  (hl : (10934:Int)*16*s-961*n+18609 ≤ 6561*r)
  (hu : (6561:Int)*r ≤ 10942*16*s-10177*n+6321)
  (he : 2*r+5=27*d) :
    1974*s ≤ 1000*d ∧ 1000*d ≤ 1977*s := by
  have hne : (2:Int)*(r:Int)+5=27*(d:Int) := by exact_mod_cast he
  have hsI : (200:Int)*(n:Int) ≤ (s:Int) := by exact_mod_cast hs
  have hnI : (20:Int) ≤ (n:Int) := by exact_mod_cast hn
  have hlo : (1974:Int)*(s:Int) ≤ 1000*(d:Int) := by omega
  have hhi : (1000:Int)*(d:Int) ≤ 1977*(s:Int) := by omega
  exact ⟨by exact_mod_cast hlo,by exact_mod_cast hhi⟩

/-- Exact four-even-gate geometry with enough precision to identify both low odd valutions. -/
theorem strong_g_corridor (n s d a b c f g : Nat) (hn:20≤n)
  (hs:200*n≤s) (hl:1974*s≤1000*d) (hu:1000*d≤1977*s)
  (he0:8*d=8*s+a+(n-8)+5)
  (he1:2*a=8*s+b+(n-8))
  (he2:2*b=8*s+c+(n-8))
  (he3:2*c=8*s+f+(n-8))
  (he4:2*f=8*s+g+(n-8)) :
    9*s+6*(n-8)+12 < 2*g+5 ∧ 2*(2*g+5)+12 < 21*s := by
  have hk:n-8+8=n:=by omega
  constructor <;> omega

#print axioms strong_interval
#print axioms strong_g_corridor
end CascadeGapTZero

namespace CascadeGapTZero

private theorem pow_two_prev (k s:Nat) (hk:1≤k) (hs:s=2^k) :
    s=2*2^(k-1) := by
  have he:k=k-1+1:=by omega
  have hp : 2^k=2^(k-1+1) := congrArg (fun x:Nat => 2^x) he
  rw [Nat.pow_succ] at hp
  rw [hs]
  omega

private theorem odd_band_unique (u k l:Nat)
 (hb:(6*2^k+1≤u ∧ u≤8*2^k-1))
 (hl:(6*2^l+1≤u ∧ u≤8*2^l-1)):k=l:=by
  by_cases he:k=l
  · exact he
  by_cases hkl:k<l
  · have hp:2^(k+1)≤2^l:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    rw [Nat.pow_succ] at hp
    omega
  · have hp:2^(l+1)≤2^k:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    rw [Nat.pow_succ] at hp
    omega

private theorem odd_gap_exclusion (m u:Nat) (hl:2^m<u)
 (hu:2*u+2<3*2^m):∀l, ¬(6*2^l+1≤u ∧ u≤8*2^l-1):=by
  intro l ⟨hlo,hhi⟩
  by_cases hc:l+3≤m
  · have hp:2^(l+3)≤2^m:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) hc
    rw [Nat.pow_add] at hp
    omega
  · have hp:2^m≤2^(l+2):=Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    rw [Nat.pow_add] at hp
    omega

/-- When 27 does not divide the g numerator, every odd inverse valuation is 0 or 1. -/
theorem no27_short (g t z:Nat) (hnot:(2*g+5)%27≠0)
 (he:2*g+5=3^(t+1)*z):t=0∨t=1:=by
  by_cases ht:t≤1
  · omega
  · have he0:t+1=3+(t-2):=by omega
    have hzero:3^(t+1)%27=0:=by rw[he0,Nat.pow_add];simp
    have hdiv:(2*g+5)%27=0:=by rw[he,Nat.mul_mod,hzero];simp
    exact False.elim (hnot hdiv)

/-- At n=5 mod 6, the possible t=0 gap fork is itself a non-rooted
    height in an even-image gap with residue 0 mod 3. -/
theorem tzero_parent_geometry (n k s g l z x:Nat)
 (hn:20≤n) (hk:k=n-8) (hs:s=2^k) (hsector:n%6=5)
 (hconst:(8*s+k)%3=1)
 (hlo:9*s+6*k+12<2*g+5)
 (hhi:2*(2*g+5)+12<21*s)
 (h9:(2*g+5)%9=0)
 (hnum:2*g+5=3*z)
 (hband:6*2^l+1≤z ∧ z≤8*2^l-1)
 (heq:2*z=8*2^l+x+l+5) :
    l=k-1 ∧ 2*s<x ∧ 2*x+2<6*s ∧ x%3=0 := by
  have hklo : 1≤k := by omega
  have hp:=pow_two_prev k s hklo hs
  have hband0:6*2^(k-1)+1≤z ∧ z≤8*2^(k-1)-1:=by
    constructor <;> omega
  have hekl:l=k-1:=odd_band_unique z l (k-1) hband hband0
  have heq0:2*z=4*s+x+k+4:=by rw[hekl] at heq;omega
  have hk3:k%3=0:=by omega
  have hs3:s%3=2:=by omega
  have hz3:z%3=0:=by omega
  refine ⟨hekl,?_,?_,?_⟩
  · omega
  · omega
  · omega

/-- The valuation-one odd-image height lands in a strict dyadic gap. -/
theorem tone_forbidden (n k s g l z x:Nat)
  (hn:20≤n) (hk:k=n-8) (hs:s=2^k)
  (hlo:9*s+6*k+12<2*g+5)
  (hhi:2*(2*g+5)+12<21*s)
  (hnum:2*g+5=9*z)
  (hband:6*2^l+1≤2*z ∧ 2*z≤8*2^l-1)
  (heq:2*(2*z)=8*2^l+x+l+5):False:=by
  have hp:2^(k+1)=2*s:=by rw[hs,Nat.pow_succ];omega
  have hlow:2^(k+1)<2*z:=by rw[hp];omega
  have hhigh:2*(2*z)+2<3*2^(k+1):=by rw[hp];omega
  exact (odd_gap_exclusion (k+1) (2*z) hlow hhigh) l hband

#print axioms no27_short
#print axioms tzero_parent_geometry
#print axioms tone_forbidden
end CascadeGapTZero

namespace CascadeGapTZero

/-- The decisive root-sensitive source-interface theorem: the genuine odd
predecessor grammar and the no-even-image root obstruction suffice to exclude
all no-27 branches of this gap in the n=5 mod 6 sector. -/
theorem generic_gap_no27_root_dead (Reach : Nat → Prop)
 (n k s g : Nat) (hn:20≤n) (hk:k=n-8) (hs:s=2^k)
 (hsector:n%6=5) (hconst:(8*s+k)%3=1)
 (hlo:9*s+6*k+12<2*g+5)
 (hhi:2*(2*g+5)+12<21*s)
 (h9:(2*g+5)%9=0) (hnot27:(2*g+5)%27≠0)
 (hparent:Reach g → ∃x l t z:Nat, Reach x ∧
    6*2^l+1≤2^t*z ∧ 2^t*z≤8*2^l-1 ∧
    2*g+5=3^(t+1)*z ∧ 2*(2^t*z)=8*2^l+x+l+5)
 (hgapdead:∀x, 2*s<x → 2*x+2<6*s → x%3=0 → ¬Reach x):
 ¬Reach g := by
  intro hr
  obtain ⟨x,l,t,z,hroot,hbandlo,hbandhi,hnum,heq⟩ := hparent hr
  rcases no27_short g t z hnot27 hnum with ht | ht
  · subst t
    have hnum0 : 2*g+5=3*z := by simpa using hnum
    have hb0 : 6*2^l+1≤z ∧ z≤8*2^l-1 := by simpa using And.intro hbandlo hbandhi
    obtain ⟨_,hxlo,hxhi,hx3⟩:=tzero_parent_geometry n k s g l z x
      hn hk hs hsector hconst hlo hhi h9 hnum0 hb0 (by simpa using heq)
    exact (hgapdead x hxlo hxhi hx3) hroot
  · subst t
    have hnum1 : 2*g+5=9*z := by simpa using hnum
    have hb1 : 6*2^l+1≤2*z ∧ 2*z≤8*2^l-1 := by simpa using And.intro hbandlo hbandhi
    exact tone_forbidden n k s g l z x hn hk hs hlo hhi hnum1 hb1 (by simpa using heq)

#print axioms generic_gap_no27_root_dead
end CascadeGapTZero
