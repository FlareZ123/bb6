import Lean
set_option maxHeartbeats 0
set_option maxRecDepth 4096
namespace CascadeHighTTwo
theorem size_bound (n:Nat) (hn:20≤n): 64*n≤2^(n-8) := by
  have h:∀k:Nat, 64*(20+k)≤2^(12+k):=by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have he:12+(k+1)=(12+k)+1:=by omega
      rw [he, Nat.pow_succ]
      omega
  have hn1:n=20+(n-20):=by omega
  have hn2:n-8=12+(n-20):=by omega
  simpa only [←hn1,←hn2] using h (n-20)

theorem d_interval (n:Nat)(s d r:Int)
  (hn:20≤n) (hs:64*(n:Int)≤s)
  (hl:10934*16*s-961*n+18609≤6561*r)
  (hu:6561*r≤10942*16*s-10177*n+6321)
  (he:2*r+5=27*d):
  1973*s≤1000*d ∧ 1000*d≤1979*s := by
  have hlo : 349888*s-1922*n+70023≤177147*d := by omega
  have hhi : 177147*d≤350144*s-20354*n+45447 := by omega
  have hs0 : 0≤s := by omega
  have hn20 : (20:Int)≤n := by exact_mod_cast hn
  constructor
  · omega
  · omega
#print axioms d_interval
end CascadeHighTTwo

namespace CascadeHighTTwo
/-- Consecutive exact even parent heights of the odd t2 branch are in one dyadic band. -/
theorem even_four_geometry (n s d a b c f g : Nat)
  (hn : 20≤n) (hs : 64*n≤s)
  (hlo : 1973*s≤1000*d) (hhi : 1000*d≤1979*s)
  (he0 : 8*d=8*s+a+(n-8)+5)
  (he1 : 2*a=8*s+b+(n-8))
  (he2 : 2*b=8*s+c+(n-8))
  (he3 : 2*c=8*s+f+(n-8))
  (he4 : 2*f=8*s+g+(n-8)) :
  (6*s-1≤a ∧ a≤8*s-3) ∧
  (6*s-1≤b ∧ b≤8*s-3) ∧
  (6*s-1≤c ∧ c≤8*s-3) ∧
  (6*s-1≤f ∧ f≤8*s-3) ∧
  (4*s<g ∧ 2*g+2<12*s) := by
  have hk : n-8+8=n := by omega
  have hsBig : 100≤s := by omega
  constructor
  · constructor <;> omega
  constructor
  · constructor <;> omega
  constructor
  · constructor <;> omega
  constructor
  · constructor <;> omega
  · constructor <;> omega
#print axioms even_four_geometry
end CascadeHighTTwo
namespace CascadeHighTTwo
/-- Existence of all four finite, genuine even predecessor equations from the t2 first-parent equation. -/
theorem even_four_witnesses (n s d a:Nat)
  (hn:20≤n) (hs:64*n≤s)
  (hlo:1973*s≤1000*d) (hhi:1000*d≤1979*s)
  (he0:8*d=8*s+a+(n-8)+5):
  ∃b c f g:Nat,
     2*a=8*s+b+(n-8) ∧
     2*b=8*s+c+(n-8) ∧
     2*c=8*s+f+(n-8) ∧
     2*f=8*s+g+(n-8) := by
  have hk:n-8+8=n := by omega
  let K:Nat:=8*s+(n-8)
  have ha:K≤2*a:=by dsimp[K];omega
  let b:Nat:=2*a-K
  have he1:2*a=K+b:=by dsimp[b];omega
  have hb:K≤2*b:=by dsimp[K]; omega
  let c:Nat:=2*b-K
  have he2:2*b=K+c:=by dsimp[c];omega
  have hc:K≤2*c:=by dsimp[K];omega
  let f:Nat:=2*c-K
  have he3:2*c=K+f:=by dsimp[f];omega
  have hf:K≤2*f:=by dsimp[K];omega
  let g:Nat:=2*f-K
  have he4:2*f=K+g:=by dsimp[g];omega
  refine ⟨b,c,f,g,?_,?_,?_,?_⟩
  all_goals dsimp[K] at * <;> omega
#print axioms even_four_witnesses
end CascadeHighTTwo

namespace CascadeHighTTwo
private theorem power_mod_three (j:Nat):
  2^j%3=(if j%2=0 then 1 else 2):=by
  induction j with
  | zero => decide
  | succ j ih =>
      rw [Nat.pow_succ,Nat.mul_mod,ih]
      by_cases hj:j%2=0
      · simp[hj]; omega
      · have hj1:j%2=1:=by omega
        simp[hj1];omega

theorem even_const_mod_three (n:Nat) (hn:20≤n)
  (hsector:n%6=4 ∨ n%6=5):
  (8*2^(n-8)+(n-8))%3=1 := by
  have hpow := power_mod_three (n-8)
  rcases hsector with h|h
  · have he:(n-8)%2=0:=by omega
    rw [if_pos he] at hpow
    omega
  · have he:(n-8)%2≠0:=by omega
    rw [if_neg he] at hpow
    omega

theorem mod_four (s k d a b c f g:Nat)
    (hconst:(8*s+k)%3=1)
    (hd:d%3=2)
    (h0:8*d=8*s+a+k+5)
    (h1:2*a=8*s+b+k)
    (h2:2*b=8*s+c+k)
    (h3:2*c=8*s+f+k)
    (h4:2*f=8*s+g+k) :
    a%3=1 ∧ b%3=1 ∧ c%3=1 ∧ f%3=1 ∧ g%3=1 := by
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · omega
#print axioms even_const_mod_three
#print axioms mod_four
end CascadeHighTTwo

namespace CascadeHighTTwo
/-- The universal r bounds restrict every possible t=2 odd quotient to a narrow interval. -/
theorem high_r_ttwo_interval (n r d:Nat) (hn:20≤n)
  (hl:10934*((2^(n-4):Nat):Int)-961*(n:Int)+18609≤6561*(r:Int))
  (hu:6561*(r:Int)≤10942*((2^(n-4):Nat):Int)-10177*(n:Int)+6321)
  (he:2*r+5=27*d):
  1973*2^(n-8)≤1000*d ∧ 1000*d≤1979*2^(n-8) := by
  have hp:2^(n-4)=16*2^(n-8) := by
    have h:n-4=(n-8)+4:=by omega
    rw [h,Nat.pow_add]
    omega
  have hpI:((2^(n-4):Nat):Int)=16*((2^(n-8):Nat):Int) := by exact_mod_cast hp
  have hsI:(64:Int)*(n:Int)≤((2^(n-8):Nat):Int) := by
    exact_mod_cast size_bound n hn
  have hlI:10934*16*((2^(n-8):Nat):Int)-961*n+18609≤6561*(r:Int) := by
    rw [hpI] at hl
    simpa only [Int.mul_assoc] using hl
  have huI:6561*(r:Int)≤10942*16*((2^(n-8):Nat):Int)-10177*n+6321 := by
    rw [hpI] at hu
    simpa only [Int.mul_assoc] using hu
  have heI:(2:Int)*(r:Int)+5=27*(d:Int) := by exact_mod_cast he
  obtain ⟨hdlo,hdhi⟩ := d_interval n ((2^(n-8):Nat):Int) (d:Int) (r:Int)
    hn hsI hlI huI heI
  constructor
  · apply Int.ofNat_le.mp
    change (1973:Int)*((2^(n-8):Nat):Int)≤1000*(d:Int)
    exact hdlo
  · apply Int.ofNat_le.mp
    change (1000:Int)*(d:Int)≤1979*((2^(n-8):Nat):Int)
    exact hdhi

#print axioms high_r_ttwo_interval
end CascadeHighTTwo
namespace CascadeHighTTwo
/-- The t=2 image numerator necessarily occupies the unique odd dyadic band at n-8. -/
theorem t_two_image_band (n d:Nat) (hn:20≤n)
  (hdlo:1973*2^(n-8)≤1000*d) (hdhi:1000*d≤1979*2^(n-8)) :
  6*2^(n-8)+1≤4*d ∧ 4*d≤8*2^(n-8)-1 := by
  have hs:=size_bound n hn
  constructor <;> omega

/-- Disjointness of odd-image dyadic source bands at distinct exponents. -/
theorem odd_band_scale_unique (u k l:Nat)
  (hk:6*2^k+1≤u ∧ u≤8*2^k-1)
  (hl:6*2^l+1≤u ∧ u≤8*2^l-1):k=l:=by
  by_cases he:k=l
  · exact he
  by_cases hkl:k<l
  · have hp:2^(k+1)≤2^l:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    rw[Nat.pow_succ] at hp
    omega
  · have hp:2^(l+1)≤2^k:=Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    rw[Nat.pow_succ] at hp
    omega

#print axioms t_two_image_band
#print axioms odd_band_scale_unique
end CascadeHighTTwo
