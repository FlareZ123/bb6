import BB429Branch9Diagonal

namespace BB429Branch9Clip
open BB429NewResidue BB429DyadicTransport BB429DyadicSource BB429Branch9Diagonal

set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

/-- Exact residue representative of a power modulo the weighted base scale.
    When t is large, avoid building the exponentially large integer. -/
def clipPow (d t : Nat) : Int := if d+6 ≤ t then 0 else 2^t

def clipQuot (d t : Nat) : Int := if d+6 ≤ t then 2^(t-(d+6)) else 0

theorem clip_pow_eq (d t : Nat) : (2:Int)^t = clipPow d t + scale d * clipQuot d t := by
  by_cases ht : d+6 ≤ t
  · simp only [clipPow,clipQuot,ite_eq_left ht,Int.zero_add]
    rw [scale_pow, ← Int.pow_add, show d+6+(t-(d+6))=t by omega]
  · simp [clipPow,clipQuot,ht]

def clipA (J N d k : Nat) : Int := 6*clipPow d (N-(4*k+3))-6*clipPow d J-8-3*(k:Int)
def clipB (J N d k : Nat) : Int := 5-12*clipPow d J-12*clipPow d (N-(4*k+3))-6*(k:Int)

/-- Direct weighted-congruence certificate, avoiding all large power terms
    in the executable search. Applies even at the near-end t boundary. -/
theorem reject_side_clip (J N d k x y : Nat)
    (hN : d+6 ≤ N)
    (hHigh : 36*2^d+6*2^J+8+3*k ≤ 12*2^N)
    (hx : x+6*2^J+8+3*k=12*2^N+6*2^(N-(4*k+3)))
    (hy : y+12*2^J+12*2^(N-(4*k+3))+6*k=24*2^N+5)
    (hc : search basicTest d (clipA J N d k) (clipB J N d k)=false) : ¬Reach x y := by
  let t := N-(4*k+3)
  have hpow : (2:Int)^N = scale d * 2^(N-(d+6)) := by
    rw [scale_pow, ← Int.pow_add, show d+6+(N-(d+6))=N by omega]
  have hxI : (x:Int)+6*2^J+8+3*(k:Int)=12*2^N+6*2^t := by exact_mod_cast hx
  have hyI : (y:Int)+12*2^J+12*2^t+6*(k:Int)=24*2^N+5 := by exact_mod_cast hy
  rw [hpow,clip_pow_eq d t,clip_pow_eq d J] at hxI hyI
  have hnear : Near (scale d) (clipA J N d k) (clipB J N d k) x y := by
    refine ⟨12*2^(N-(d+6))+6*clipQuot d t-6*clipQuot d J,
      12*2^(N-(d+6))-6*clipQuot d J-6*clipQuot d t,?_,?_⟩
    · unfold clipA
      change (x:Int)-(6*clipPow d t-6*clipPow d J-8-3*(k:Int)) = _
      rw [Int.mul_sub,Int.mul_add]
      repeat' rw [Int.mul_left_comm (scale d)]
      rw [Int.mul_add,Int.mul_add] at hxI
      omega
    · unfold clipB
      change (y:Int)-(5-12*clipPow d J-12*clipPow d t-6*(k:Int)) = _
      rw [Int.mul_sub,Int.mul_sub]
      have mul6 (v : Int) : (2*scale d)*(6*v)=12*(scale d*v) := by
        rw [Int.mul_assoc,Int.mul_left_comm (scale d) 6,← Int.mul_assoc 2 6,show (2:Int)*6=12 by decide]
      have mul12 (v : Int) : (2*scale d)*(12*v)=24*(scale d*v) := by
        rw [Int.mul_assoc,Int.mul_left_comm (scale d) 12,← Int.mul_assoc 2 12,show (2:Int)*12=24 by decide]
      rw [mul12,mul6,mul6]
      rw [Int.mul_add,Int.mul_add] at hyI
      omega
  exact exclude d _ _ x y (by omega) hnear hc

/-- Every nonzero zero-row state has a genuine predecessor. -/
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

/-- A zero-two target with an affine signed representative q is excluded
    if both exact source predecessors fail the generic checker. -/
theorem no_zero_two (N d z : Nat) (q : Int)
    (hN : d+6 ≤ N)
    (hz : 0<z) (hzmod : z%4=2)
    (hzEq : (z:Int)=48*2^N+4*q+18)
    (hHigh : (36*2^d:Int) ≤ 12*2^N+q+3)
    (hU : search basicTest d q (2*q+2)=false)
    (hO : search basicTest d (q+4) (2*q+5)=false) : ¬Reach 0 z := by
  intro hr
  obtain ⟨u,w,hroot,hs⟩ := pred_zero z hz hr
  have hpow : (2:Int)^N = scale d * 2^(N-(d+6)) := by
    rw [scale_pow, ← Int.pow_add, show d+6+(N-(d+6))=N by omega]
  rcases incoming_zero_two u w z hs hzmod with ⟨hw,hze⟩ | ⟨hw,hze⟩
  · have hu : (u:Int)=12*2^N+q := by omega
    apply exclude d q (2*q+2) u w _ _ hU hroot
    · exact_mod_cast (show (36*2^d:Int) ≤ (u:Int)+3 by omega)
    · refine ⟨12*2^(N-(d+6)),12*2^(N-(d+6)),?_,?_⟩
      · rw [Int.mul_left_comm (scale d) 12,← hpow]; omega
      · rw [Int.mul_assoc 2,Int.mul_left_comm (scale d) 12,← hpow]; omega
  · have hu : (u:Int)=12*2^N+q+4 := by omega
    apply exclude d (q+4) (2*q+5) u w _ _ hO hroot
    · exact_mod_cast (show (36*2^d:Int) ≤ (u:Int)+3 by omega)
    · refine ⟨12*2^(N-(d+6)),12*2^(N-(d+6)),?_,?_⟩
      · rw [Int.mul_left_comm (scale d) 12,← hpow]; omega
      · rw [Int.mul_assoc 2,Int.mul_left_comm (scale d) 12,← hpow]; omega

private theorem incoming_nine (u w b : Nat)
    (h : BB429.next (u,w)=some (9,b)) : u=3 ∧ w=b+9 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

private theorem incoming_three (u w b : Nat)
    (h : BB429.next (u,w)=some (3,b)) : u=0 ∧ w=b+3 := by
  simp only [BB429.next] at h
  repeat' (split at h <;> try contradiction)
  all_goals simp_all [Prod.mk.injEq, Option.some.injEq]
  all_goals omega

/-- All diagonal inverse routes close from a complete side-parent exclusion and
    a separate zero-feeder exclusion. Unlike the odd-J theorem this has
    no parity condition on N. -/
theorem no_diagonal_of_side (J N : Nat)
    (hside : ∀ k x y : Nat, 4*k+3<N →
      x+6*2^J+8+3*k=12*2^N+6*2^(N-(4*k+3)) →
      y+12*2^J+12*2^(N-(4*k+3))+6*k=24*2^N+5 → ¬Reach x y)
    (hzero : ∀ z, z+24*2^J+3*N=48*2^N+3 → ¬Reach 0 z)
    (t a b : Nat) (ht : t≤N)
    (ha : a+3=12*2^t)
    (hb : b+24*2^t+24*2^J+3*(N-t)=48*2^N+15) : ¬Reach a b := by
  induction t generalizing a b with
  | zero =>
    simp at ha hb
    have h9 : a=9 := by omega
    subst a
    intro hr
    obtain ⟨p,q,hp,hs⟩ := pred 9 b (by decide) hr
    obtain ⟨hp3,hq⟩ := incoming_nine p q b hs
    subst p
    obtain ⟨r,s,hrs,hs⟩ := pred 3 q (by decide) hp
    obtain ⟨hr0,hsq⟩ := incoming_three r s q hs
    subst r
    exact hzero s (by omega) hrs
  | succ t ih =>
    intro hr
    have hpow : (2:Nat)^(t+1)=2*2^t := by rw [Nat.pow_succ, Nat.mul_comm]
    have hpos : 0 < (2:Nat)^t := Nat.two_pow_pos t
    have hao : a%2=1 := by omega
    have halarge : 13≤a := by omega
    rcases odd_back a b halarge hao hr with ⟨x,y,hroot,hax,hy⟩ | ⟨x,y,hroot,hax,hy,hb4⟩
    · apply ih x y (by omega) (by omega) (by omega) hroot
    · let k := (N-(t+1))/4
      have hi : N-(t+1)=4*k+3 := by dsimp [k]; omega
      have hk : 4*k+3<N := by omega
      have ht' : N-(4*k+3)=t+1 := by omega
      have hx' : x+6*2^J+8+3*k=12*2^N+6*2^(N-(4*k+3)) := by rw [ht']; omega
      have hy' : y+12*2^J+12*2^(N-(4*k+3))+6*k=24*2^N+5 := by rw [ht']; omega
      exact hside k x y hk hx' hy' hroot

/-- Specialization to a fixed-depth clipped certificate. -/
theorem no_diagonal_of_clip (J N d : Nat)
    (hN : d+6 ≤ N)
    (hHigh : 36*2^d+6*2^J+8+3*N ≤ 12*2^N)
    (hcert : ∀ k, 4*k+3<N → search basicTest d (clipA J N d k) (clipB J N d k)=false)
    (hzero : ∀ z, z+24*2^J+3*N=48*2^N+3 → ¬Reach 0 z)
    (t a b : Nat) (ht : t≤N)
    (ha : a+3=12*2^t)
    (hb : b+24*2^t+24*2^J+3*(N-t)=48*2^N+15) : ¬Reach a b := by
  apply no_diagonal_of_side J N ?_ hzero t a b ht ha hb
  intro k x y hk hx hy
  exact reject_side_clip J N d k x y hN (by omega) hx hy (hcert k hk)

#print axioms reject_side_clip
#print axioms no_zero_two
#print axioms no_diagonal_of_clip
end BB429Branch9Clip
