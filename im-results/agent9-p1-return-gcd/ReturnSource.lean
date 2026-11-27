import ReturnTrace

namespace BB6.Agent9ReturnGCD
open BB6.Agent45.DelayedCarry

private theorem natAbs_diff_le (c d : Int) (T : Nat)
    (hc : 1≤c ∧ c≤(T:Int)) (hd : 1≤d ∧ d≤(T:Int)) :
    (d-c).natAbs≤T := by
  by_cases h : 0≤d-c
  · have he := Int.natAbs_of_nonneg h
    omega
  · have he := Int.natAbs_of_nonneg (show 0≤ -(d-c) by omega)
    rw [Int.natAbs_neg] at he
    omega

private theorem slope_initial_bound (c d e u v : Int) (T A : Nat) (g : Int)
    (hg : 0≤g) (hc : 1≤c ∧ c≤(T:Int)) (hd : 1≤d ∧ d≤(T:Int))
    (he : 1≤e ∧ e≤(T:Int))
    (hscale : (u.natAbs+v.natAbs)*T<2^A) :
    -(2:Int)^A < (-u)*(d-c)+(-v)*(e-c) ∧
      (-u)*(d-c)+(-v)*(e-c)<g+(2:Int)^A := by
  let z := (-u)*(d-c)+(-v)*(e-c)
  have h1 := Nat.mul_le_mul_left u.natAbs (natAbs_diff_le c d T hc hd)
  have h2 := Nat.mul_le_mul_left v.natAbs (natAbs_diff_le c e T hc he)
  have hz := Int.natAbs_add_le ((-u)*(d-c)) ((-v)*(e-c))
  rw [Int.natAbs_mul,Int.natAbs_mul,Int.natAbs_neg,Int.natAbs_neg] at hz
  have hbound : z.natAbs<2^A := by
    change z.natAbs≤_ at hz
    rw [Nat.add_mul] at hscale
    omega
  have hI : (z.natAbs:Int)<(2:Int)^A := by
    have hh : (z.natAbs:Int)<((2^A:Nat):Int) := by omega
    push_cast at hh
    exact hh
  have hhi : z≤(z.natAbs:Int) := Int.le_natAbs
  have hlo : -z≤(z.natAbs:Int) := by
    have h := @Int.le_natAbs (-z)
    simpa only [Int.natAbs_neg] using h
  change -(2:Int)^A<z ∧ z<g+(2:Int)^A
  omega

/-- Original delayed-carry selected-word exclusion for separated repeats.
    p and s are forward distances, so their clock offsets are -p and -s.
    h is the odd part of any positive Bezout combination of p,s. -/
theorem trace_no_small_gcd_repeat {n m W a : Nat} (hn : 14≤n) (heven : n%2=0)
    (ht : Trace n m W a) (i p s L A r h K : Nat) (u v : Int)
    (hp : i+p+L≤m) (hs : i+s+L≤m)
    (hrepP : ∀ j<L, W.testBit (i+p+j)=W.testBit (i+j))
    (hrepS : ∀ j<L, W.testBit (i+s+j)=W.testBit (i+j))
    (hodd : h%2=1)
    (hbez : u*(p:Int)+v*(s:Int)=(2:Int)^r*(h:Int))
    (hL : A+r+2*h+K≤L)
    (hA : (u.natAbs+v.natAbs)*total n<2^A)
    (hK : h*(total n+h)<2^K) : False := by
  obtain ⟨c,w,H⟩ := trace_path hn heven ht
  let q : Int := (total n:Int)-n-i-3
  let g : Int := (2:Int)^r*(h:Int)
  have hgp : 0≤g := Int.mul_nonneg (Int.pow_nonneg (by decide)) (by omega)
  have hbz : (-u)*(-(p:Int))+(-v)*(-(s:Int))=g := by
    simpa [g,Int.neg_mul,Int.mul_neg] using hbez
  have h0 := H.bounds i (by omega)
  have hp0 := H.bounds (i+p) (by omega)
  have hs0 := H.bounds (i+s) (by omega)
  apply no_small_gcd_returns q (-1) (total n:Int) (-(p:Int)) (-(s:Int)) (-u) (-v) g h L A r K
    (fun j => c (i+j)) (fun j => c (i+p+j)) (fun j => c (i+s+j))
    (fun j => w (i+j)) (fun j => bit W (i+j)) (Or.inr rfl) hodd hbz rfl hL
  · simpa using slope_initial_bound (c i) (c (i+p)) (c (i+s)) u v (total n) A g hgp
      ⟨h0.1,h0.2.1⟩ ⟨hp0.1,hp0.2.1⟩ ⟨hs0.1,hs0.2.1⟩ hA
  · intro j hj; exact bit_binary W (i+j)
  · intro j hj
    have hh := H.stepV (i+j) (by omega)
    have hclock : (total n:Int)-n-(i+j:Nat)-3=q+(-1)*(j:Int) := by dsimp [q]; simp; omega
    rw [hclock] at hh
    simpa only [Nat.add_assoc] using hh
  · intro j hj
    have hh := H.stepV (i+p+j) (by omega)
    have heq : bit W (i+p+j)=bit W (i+j) := by simp [bit,hrepP j hj]
    rw [heq] at hh
    have hclock : (total n:Int)-n-(i+p+j:Nat)-3=q+(-1)*(j:Int)+(-(p:Int)) := by dsimp [q]; simp; omega
    rw [hclock] at hh
    simpa only [Nat.add_assoc] using hh
  · intro j hj
    have hh := H.stepV (i+s+j) (by omega)
    have heq : bit W (i+s+j)=bit W (i+j) := by simp [bit,hrepS j hj]
    rw [heq] at hh
    have hclock : (total n:Int)-n-(i+s+j:Nat)-3=q+(-1)*(j:Int)+(-(s:Int)) := by dsimp [q]; simp; omega
    rw [hclock] at hh
    simpa only [Nat.add_assoc] using hh
  · intro j hj heq
    have hh := H.stepW (i+j) (by omega)
    simpa [heq,Nat.add_assoc] using hh
  · intro j hj; exact H.bounds (i+j) (by omega)
  · have hh : ((h*(total n+h):Nat):Int)<((2^K:Nat):Int) := by omega
    push_cast at hh
    exact hh

/-- Dyadically separated pairs alone already force a unit slope after
    trimming r bits. The third factor is unnecessary in this case. -/
theorem trace_no_dyadic_repeat {n m W a : Nat} (hn : 14≤n) (heven : n%2=0)
    (ht : Trace n m W a) (i r L A K : Nat)
    (hp : i+2^r+L≤m)
    (hrep : ∀ j<L, W.testBit (i+2^r+j)=W.testBit (i+j))
    (hL : A+r+2+K≤L) (hA : total n<2^A) (hK : total n+1<2^K) : False := by
  apply trace_no_small_gcd_repeat hn heven ht i (2^r) (2^r) L A r 1 K 1 0 hp hp hrep hrep
  · decide
  · simp [Int.natCast_pow]
  · omega
  · simpa using hA
  · simpa using hK

#print axioms trace_no_small_gcd_repeat
#print axioms trace_no_dyadic_repeat

end BB6.Agent9ReturnGCD
