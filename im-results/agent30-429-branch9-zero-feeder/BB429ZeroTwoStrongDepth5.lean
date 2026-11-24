import BB429DyadicSource
import BB429Even16
import BB429RootEven8
import BB429ZeroTwoThree
import Lean.Elab.Tactic.Omega

/-!
# Strong signed root filter for the branch-9 zero-two feeder

The ordinary dyadic source filter remembers only the mod-eight invariant.
This file strengthens it with the source-proved positive-even mod-sixteen
row and the odd/odd three-sum row.  The resulting signed search remains an
overapproximation of genuine blank-root inverse paths.

The depth-five executable residue filter is a reusable necessary condition
for the all-F zero-two feeder.  It is an intermediate result, not a proof
that the remaining residue classes are reachable or impossible.
-/

namespace BB429ZeroTwoStrongDepth5

open BB429NewResidue BB429DyadicTransport BB429DyadicSource

set_option maxHeartbeats 40000000
set_option maxRecDepth 30000

/-- A stronger signed root filter: even16 on even states, the source
    mod-eight predicate on odd states, and the odd/odd three-sum row. -/
def strongTest (a b : Int) : Bool := decide (
  (a%2=0 →
    ((a%4=0 → b%16=2) ∧ (a%4=2 → b%16=10))) ∧
  (a%2=1 → basicTest a b = true) ∧
  (a%2=1 → b%2=1 → a%4=3 → (a+b)%8=2))

private theorem odd_odd_three_sum (a b : Nat) (hr : Reach a b)
    (ha : 13≤a) (hao : a%2=1) (hbo : b%2=1) (ha4 : a%4=3) :
    (a+b)%8=2 := by
  rcases odd_back a b ha hao hr with
    ⟨p,q,hp,hpa,hqb⟩ |
    ⟨p,q,hp,hpa,hqb,hb4⟩
  · have hpos : 0<p := by omega
    have heven : p%2=0 := by omega
    rcases hp with ⟨n,hn⟩
    have hq8 := BB429RootEven8.rooted_positive_even_eight n p q hn hpos heven
    omega
  · omega

/-- The strengthened filter is sound on every genuine high root state
    throughout the weighted 64/128 congruence cylinder. -/
theorem strongTest_sound (a b : Int) (x y : Nat) (hx : 33≤x)
    (hr : Reach x y) (h : Near 64 a b x y) : strongTest a b = true := by
  have hOrig := h
  obtain ⟨i,j,hi,hj⟩ := h
  have ha2 : a%2=(x:Int)%2 := by omega
  have ha4 : a%4=(x:Int)%4 := by omega
  have ha8 : a%8=(x:Int)%8 := by omega
  have ha16 : a%16=(x:Int)%16 := by omega
  have hb2 : b%2=(y:Int)%2 := by omega
  have hb4 : b%4=(y:Int)%4 := by omega
  have hb8 : b%8=(y:Int)%8 := by omega
  have hb16 : b%16=(y:Int)%16 := by omega
  have hprop :
      (a%2=0 →
        ((a%4=0 → b%16=2) ∧ (a%4=2 → b%16=10))) ∧
      (a%2=1 → basicTest a b = true) ∧
      (a%2=1 → b%2=1 → a%4=3 → (a+b)%8=2) := by
    constructor
    · intro haeven
      have hxeven : x%2=0 := by omega
      rcases hr with ⟨n,hn⟩
      have h16 := BB429Even16.rooted_even_sixteen n x y hn (by omega) hxeven
      constructor
      · intro ha0
        have hx0 : x%4=0 := by omega
        have hy16 := h16.1 hx0
        omega
      · intro ha2'
        have hx2 : x%4=2 := by omega
        have hy16 := h16.2 hx2
        omega
    constructor
    · intro haodd
      exact BB429DyadicSource.basicTest_sound a b x y hx hr hOrig
    · intro haodd hbodd ha3
      have hxo : x%2=1 := by omega
      have hyo : y%2=1 := by omega
      have hx3 : x%4=3 := by omega
      have hsum := odd_odd_three_sum x y hr (by omega) hxo hyo hx3
      omega
  unfold strongTest
  exact decide_eq_true hprop

/-- Soundness of the stronger inverse search, using the unchanged source
    inverse grammar and the stronger root filter above. -/
theorem searchStrong_sound (d : Nat) (a b : Int) (x y : Nat)
    (high : 36*2^d ≤ x+3) (hr : Reach x y)
    (near : Near (scale d) a b x y) :
    search strongTest d a b = true :=
  BB429DyadicTransport.search_sound Reach BB429DyadicSource.grammar
    strongTest strongTest_sound d a b x y high hr near

/-- The eleven residue classes left by the existing all-time zero-two
    gateway, expressed as an executable predicate. -/
def zeroTwoGatewayClass (r : Nat) : Bool := decide (
  r%32=1 ∨ r%32=2 ∨ r%32=8 ∨ r%32=9 ∨ r%32=10 ∨
  r%32=14 ∨ r%32=17 ∨ r%32=18 ∨ r%32=25 ∨ r%32=26 ∨ r%32=30)

/-- A parameter residue survives the new depth-five strong inverse sieve
    only if at least one of the two exact zero-two predecessor trees survives. -/
def zeroTwoDepth5Possible (r : Nat) : Bool :=
  zeroTwoGatewayClass r &&
    (search strongTest 5 (3-3*(r:Int)) (2*(3-3*(r:Int))+2) ||
     search strongTest 5 ((3-3*(r:Int))+4) (2*(3-3*(r:Int))+5))

/-- The finite residue certificate is small enough to be kernel-evaluated.
    Exactly 248 of the 2048 residues survive the gateway plus depth-five
    strong inverse filter. -/
def zeroTwoDepth5Residues : List Nat :=
  (List.range 2048).filter zeroTwoDepth5Possible

theorem zeroTwoDepth5Residues_length :
    zeroTwoDepth5Residues.length=216 := by decide

private theorem pred_zero (z : Nat) (hz : 0<z) (hr : Reach 0 z) :
    ∃ u w, Reach u w ∧ BB429.next (u,w)=some (0,z) := by
  obtain ⟨n,hn⟩ := hr
  cases n with
  | zero => simp [BB429.run] at hn; omega
  | succ n =>
    simp only [BB429.run] at hn
    cases h : BB429.run n (0,0) with
    | none => simp [h] at hn
    | some p => exact ⟨p.1,p.2,⟨n,h⟩,by simpa [h] using hn⟩

private theorem incoming_zero_two (u w z : Nat)
    (hs : BB429.next (u,w)=some (0,z)) (hz : z%4=2) :
    (w=2*u+2 ∧ z=4*u+18) ∨ (w+3=2*u ∧ z=4*u+2) := by
  simp only [BB429.next] at hs
  repeat' (split at hs <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq,Option.some.injEq]
  all_goals omega

private theorem near_upper (N : Nat) (q qrep k : Int)
    (hN : 11≤N) (hres : q-qrep=scale 5*k) :
    Near (scale 5) qrep (2*qrep+2)
      (12*(2:Int)^N+q) (24*(2:Int)^N+2*q+2) := by
  have hs : scale 5 = (2:Int)^11 := by decide
  have hs2 : scale 5 = 2048 := by rfl
  have hp : (2:Int)^N = scale 5*(2:Int)^(N-11) := by
    rw [hs, ← Int.pow_add, show 11+(N-11)=N by omega]
  refine ⟨12*(2:Int)^(N-11)+k,12*(2:Int)^(N-11)+k,?_,?_⟩
  · have hleft : (12*(2:Int)^N+q)-qrep = 12*(2:Int)^N+(q-qrep) := by omega
    rw [hleft,hp,hres]
    rw [hs2]
    omega
  · have hleft : (24*(2:Int)^N+2*q+2)-(2*qrep+2) =
        24*(2:Int)^N+2*(q-qrep) := by omega
    rw [hleft,hp,hres]
    rw [hs2]
    omega

private theorem near_odd (N : Nat) (q qrep k : Int)
    (hN : 11≤N) (hres : q-qrep=scale 5*k) :
    Near (scale 5) (qrep+4) (2*qrep+5)
      (12*(2:Int)^N+q+4) (24*(2:Int)^N+2*q+5) := by
  have hs : scale 5 = (2:Int)^11 := by decide
  have hs2 : scale 5 = 2048 := by rfl
  have hp : (2:Int)^N = scale 5*(2:Int)^(N-11) := by
    rw [hs, ← Int.pow_add, show 11+(N-11)=N by omega]
  refine ⟨12*(2:Int)^(N-11)+k,12*(2:Int)^(N-11)+k,?_,?_⟩
  · have hleft : (12*(2:Int)^N+q+4)-(qrep+4) =
        12*(2:Int)^N+(q-qrep) := by omega
    rw [hleft,hp,hres]
    rw [hs2]
    omega
  · have hleft : (24*(2:Int)^N+2*q+5)-(2*qrep+5) =
        24*(2:Int)^N+2*(q-qrep) := by omega
    rw [hleft,hp,hres]
    rw [hs2]
    omega

/-- Source-connected depth-five necessary condition for the entire
    all-F zero-two feeder family. The arithmetic hypotheses are stated
    explicitly so the theorem can be reused with alternative feeder
    parametrizations. -/
theorem zero_two_depth5_restriction_of_parent
    (m J N z u w : Nat) (q : Int)
    (hJ : J=4*m+2) (hJlarge : 3≤J) (hNlarge : 11≤N)
    (hzmod : z%4=2)
    (hfeeder : z+48*2^J+3*J=12*2^(N+2)+36)
    (hzEq : (z:Int)=48*(2:Int)^N+4*q+18)
    (hHigh : (36*2^5:Int)≤12*(2:Int)^N+q+3)
    (hres : ∃ k : Int, q-(3-3*(m%2048:Int))=scale 5*k)
    (hr : Reach u w) (hs : BB429.next (u,w)=some (0,z)) :
    zeroTwoDepth5Possible (m%2048)=true := by
  have hReachCopy := hr
  obtain ⟨n,hn⟩ := hr
  have hparts := incoming_zero_two u w z hs hzmod
  have hu129 : 129≤u := by
    rcases hparts with ⟨hw,hz⟩ | ⟨hw,hz⟩
    · have hu : (u:Int)=12*(2:Int)^N+q := by omega
      have h : (129:Int)≤(u:Int) := by omega
      exact_mod_cast h
    · have hu : (u:Int)=12*(2:Int)^N+q+4 := by omega
      have h : (129:Int)≤(u:Int) := by omega
      exact_mod_cast h
  have hgateway :=
    BB429ZeroTwoThree.diagonal_zero_two_m_power_eleven
      n u w z m J N hn hs hzmod hu129 hJ hJlarge (by omega) hfeeder
  have hclassProp :
      m%32=1 ∨ m%32=2 ∨ m%32=8 ∨ m%32=9 ∨ m%32=10 ∨
      m%32=14 ∨ m%32=17 ∨ m%32=18 ∨ m%32=25 ∨
      m%32=26 ∨ m%32=30 := by
    rcases hgateway with h|h|h|h|h|h|h|h|h|h|h <;> omega
  have hclass : zeroTwoGatewayClass (m%2048)=true := by
    unfold zeroTwoGatewayClass
    apply decide_eq_true
    omega
  rcases hres with ⟨k,hk⟩
  rcases hparts with ⟨hw,hz⟩ | ⟨hw,hz⟩
  · have hu : (u:Int)=12*(2:Int)^N+q := by omega
    have hwI : (w:Int)=24*(2:Int)^N+2*q+2 := by
      have hwi : (w:Int)=2*(u:Int)+2 := by exact_mod_cast hw
      rw [hu] at hwi
      omega
    have hHighU : (36*2^5:Int)≤(u:Int)+3 := by rw [hu]; exact hHigh
    have hHighNat : 36*2^5≤u+3 := by exact_mod_cast hHighU
    have hnear := near_upper N q (3-3*(m%2048:Int)) k hNlarge hk
    have hnear' : Near (scale 5) (3-3*(m%2048:Int))
        (2*(3-3*(m%2048:Int))+2) (u:Int) (w:Int) := by
      rw [hu,hwI]
      exact hnear
    have hsearch := searchStrong_sound 5 (3-3*(m%2048:Int))
      (2*(3-3*(m%2048:Int))+2) u w hHighNat hReachCopy hnear'
    unfold zeroTwoDepth5Possible
    rw [hclass]
    simp [hsearch]
  · have hu : (u:Int)=12*(2:Int)^N+q+4 := by omega
    have hwI : (w:Int)=24*(2:Int)^N+2*q+5 := by
      have hwi : (w:Int)+3=2*(u:Int) := by exact_mod_cast hw
      rw [hu] at hwi
      omega
    have hHighU : (36*2^5:Int)≤(u:Int)+3 := by rw [hu]; omega
    have hHighNat : 36*2^5≤u+3 := by exact_mod_cast hHighU
    have hnear := near_odd N q (3-3*(m%2048:Int)) k hNlarge hk
    have hnear' : Near (scale 5) ((3-3*(m%2048:Int))+4)
        (2*(3-3*(m%2048:Int))+5) (u:Int) (w:Int) := by
      rw [hu,hwI]
      exact hnear
    have hsearch := searchStrong_sound 5 ((3-3*(m%2048:Int))+4)
      (2*(3-3*(m%2048:Int))+5) u w hHighNat hReachCopy hnear'
    unfold zeroTwoDepth5Possible
    rw [hclass]
    simp [hsearch]


/-!
## Specialization to the actual branch-9 zero-two feeder

For m ≥ 2, put J=4m+2, N=8·2^J+J−11,
z=48·2^N−24·2^J−3N+3, and q=−12·2^J−3m+3.
The following arithmetic lemmas discharge the hypotheses of the
source-connected parent theorem, yielding a uniform necessary condition
for every parameter in this feeder family.
-/

private def Jf (m : Nat) : Nat := 4*m+2
private def Nf (m : Nat) : Nat := 8*2^(Jf m)+Jf m-11
private def Zf (m : Nat) : Nat := 48*2^(Nf m)-24*2^(Jf m)-3*Nf m+3
private def Qf (m : Nat) : Int := -12*(2:Int)^(Jf m)-3*(m:Int)+3

private theorem nat_le_two_pow (n : Nat) : n ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hp : 1 ≤ 2^n := Nat.one_le_pow n 2 (by decide)
      have h : n+1 ≤ 2^n+2^n := by omega
      calc
        n+1 ≤ 2^n+2^n := h
        _ = 2^(n+1) := by
          rw [Nat.pow_succ]
          omega

private theorem jpow_ge2 (m : Nat) : 2 ≤ 2^(Jf m) := by
  have hJ : 1 ≤ Jf m := by simp [Jf]
  have hdecomp : Jf m = 1 + (Jf m-1) := by omega
  rw [hdecomp, Nat.pow_add]
  have hp : 1 ≤ 2^(Jf m-1) := Nat.one_le_pow (Jf m-1) 2 (by decide)
  omega

private theorem jpow_ge (m : Nat) (hm : 2≤m) : 1024 ≤ 2^(Jf m) := by
  have hJ : 10 ≤ Jf m := by simp [Jf]; omega
  have hdecomp : Jf m = 10 + (Jf m-10) := by omega
  rw [hdecomp, Nat.pow_add]
  have h10 : 2^10=1024 := by decide
  rw [h10]
  have hp : 1 ≤ 2^(Jf m-10) := Nat.one_le_pow (Jf m-10) 2 (by decide)
  omega

private theorem n_ge_j4 (m : Nat) (hm : 2≤m) : Jf m+4 ≤ Nf m := by
  have hJ : 10 ≤ Jf m := by simp [Jf]; omega
  have hJpow : 2 ≤ 2^(Jf m) := jpow_ge2 m
  simp [Nf]
  omega

private theorem m_le_jpow (m : Nat) : m ≤ 2^(Jf m) := by
  have hMJ : m ≤ Jf m := by simp [Jf]; omega
  have hJpow : Jf m ≤ 2^(Jf m) := nat_le_two_pow (Jf m)
  exact Nat.le_trans hMJ hJpow

private theorem jpow_to_npow (m : Nat) (hm : 2≤m) :
    16*2^(Jf m) ≤ 2^(Nf m) := by
  have hN : Jf m+4 ≤ Nf m := n_ge_j4 m hm
  have hpow : 2^(Jf m+4) ≤ 2^(Nf m) :=
    Nat.pow_le_pow_right (by decide : 0<2) hN
  have h16 : 2^4=16 := by decide
  have hEq : 2^(Jf m+4)=16*2^(Jf m) := by
    rw [Nat.pow_add, h16]
    omega
  calc
    16*2^(Jf m) = 2^(Jf m+4) := hEq.symm
    _ ≤ 2^(Nf m) := hpow

private theorem feeder_high (m : Nat) (hm : 2≤m) :
    (36*2^5:Int) ≤ 12*(2:Int)^(Nf m)+Qf m+3 := by
  have hJpow := jpow_ge m hm
  have hNPow := jpow_to_npow m hm
  have hmPow := m_le_jpow m
  have hNPowI : (16:Int)*(2:Int)^(Jf m) ≤ (2:Int)^(Nf m) := by exact_mod_cast hNPow
  have hmPowI : (m:Int) ≤ (2:Int)^(Jf m) := by exact_mod_cast hmPow
  have hJPowI : (1024:Int) ≤ (2:Int)^(Jf m) := by exact_mod_cast hJpow
  dsimp [Qf]
  omega

private theorem q_residue (m : Nat) (hm : 2≤m) :
    ∃ k : Int, Qf m-(3-3*(m%2048:Int)) = 2048*k := by
  have hJ : 9 ≤ Jf m := by simp [Jf]; omega
  have hmodN : (m:Int)-(m%2048:Int)=2048*(m/2048:Int) := by
    have hh : m%2048+2048*(m/2048)=m := Nat.mod_add_div m 2048
    exact_mod_cast (by omega)
  have hdecomp : Jf m = 9+(Jf m-9) := by omega
  have hpow9 : (12:Int)*(2:Int)^(Jf m) = 2048*(3*(2:Int)^(Jf m-9)) := by
    rw [hdecomp, Int.pow_add]
    have h512 : (2:Int)^9=512 := by decide
    rw [h512]
    have hexp : 9+(Jf m-9)-9=Jf m-9 := by omega
    simp [hexp]
    have hcoeff : (12:Int)*512=2048*3 := by decide
    omega
  refine ⟨-(3*(2:Int)^(Jf m-9)+3*(m/2048:Int)), ?_⟩
  dsimp [Qf]
  omega

private theorem z_nat_eq (m : Nat) (hm : 2≤m) :
    Zf m+24*2^(Jf m)+3*Nf m=48*2^(Nf m)+3 := by
  have hNPow : 16*2^(Jf m)≤2^(Nf m) := jpow_to_npow m hm
  have hNle : Nf m≤2^(Nf m) := nat_le_two_pow (Nf m)
  have hbound : 24*2^(Jf m)+3*Nf m ≤ 48*2^(Nf m)+3 := by omega
  simp [Zf]
  omega

private theorem z_mod_four (m : Nat) (hm : 2≤m) : Zf m%4=2 := by
  have hJmod : Jf m%4=2 := by simp [Jf]
  have hNmod : Nf m%4=3 := by
    have hJpow : 2 ≤ 2^(Jf m) := jpow_ge2 m
    have hNbound : 11 ≤ 8*2^(Jf m)+Jf m := by omega
    unfold Nf
    omega
  have hEq := z_nat_eq m hm
  omega

private theorem z_feeder_eq (m : Nat) (hm : 2≤m) :
    Zf m+48*2^(Jf m)+3*Jf m=12*2^(Nf m+2)+36 := by
  have hEq := z_nat_eq m hm
  have hN : Nf m=8*2^(Jf m)+Jf m-11 := rfl
  have hJpow : 2 ≤ 2^(Jf m) := jpow_ge2 m
  have hNbound : 11 ≤ 8*2^(Jf m)+Jf m := by omega
  have hpow : 2^(Nf m+2)=4*2^(Nf m) := by
    rw [Nat.pow_add]
    have h4 : 2^2=4 := by decide
    rw [h4]
    omega
  rw [hpow]
  omega

private theorem z_int_eq (m : Nat) (hm : 2≤m) :
    (Zf m:Int)=48*(2:Int)^(Nf m)+4*Qf m+18 := by
  have hNat := z_nat_eq m hm
  have hNplus : (Nf m:Int)+11=8*(2:Int)^(Jf m)+(Jf m:Int) := by
    have hJpow : 2 ≤ 2^(Jf m) := jpow_ge2 m
    have hNbound : 11 ≤ 8*2^(Jf m)+Jf m := by omega
    have hNnat' : Nf m+11=8*2^(Jf m)+Jf m := by
      dsimp [Nf]
      omega
    exact_mod_cast hNnat'
  have hJnat : Jf m=4*m+2 := rfl
  have hJ : (Jf m:Int)=4*(m:Int)+2 := by exact_mod_cast hJnat
  have hNatI : (Zf m:Int)+24*(2:Int)^(Jf m)+3*(Nf m:Int)=48*(2:Int)^(Nf m)+3 := by
    exact_mod_cast hNat
  dsimp [Qf]
  omega

/-- Every reachable blank-root state in the branch-9 all-F zero-two feeder
    family has its parameter in the 216-element depth-five residue filter. -/
theorem branch9_zero_two_depth5_restriction (m : Nat) (hm : 2≤m)
    (hr : Reach 0 (Zf m)) :
    zeroTwoDepth5Possible (m%2048)=true := by
  have hJlarge : 3≤Jf m := by simp [Jf]; omega
  have hNge : Jf m+4≤Nf m := n_ge_j4 m hm
  have hJge : 10≤Jf m := by simp [Jf]; omega
  have hNlarge : 11≤Nf m := by omega
  have hzmod := z_mod_four m hm
  have hzpos : 0<Zf m := by omega
  obtain ⟨u,w,hparent,hs⟩ := pred_zero (Zf m) hzpos hr
  obtain ⟨k,hres2048⟩ := q_residue m hm
  have hscale : scale 5 = 2048 := by rfl
  have hres : Qf m-(3-3*(m%2048:Int))=scale 5*k := by
    rw [hscale]
    exact hres2048
  exact zero_two_depth5_restriction_of_parent
    m (Jf m) (Nf m) (Zf m) u w (Qf m)
    rfl hJlarge hNlarge hzmod
    (z_feeder_eq m hm) (z_int_eq m hm) (feeder_high m hm)
    ⟨k,hres⟩ hparent hs

#print axioms strongTest_sound
#print axioms zeroTwoDepth5Residues_length
#print axioms zero_two_depth5_restriction_of_parent

end BB429ZeroTwoStrongDepth5
