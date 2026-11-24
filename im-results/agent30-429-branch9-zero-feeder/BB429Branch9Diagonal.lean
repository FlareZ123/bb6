import BB429DyadicSource

namespace BB429Branch9Diagonal
open BB429NewResidue BB429DyadicTransport BB429DyadicSource

set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

/-- Remove the common top-power terms, preserving signed exact arithmetic.
    The remaining t-power is deliberately not truncated. -/
def sideA (J N k : Nat) : Int := 6*2^(N-(4*k+3))-6*2^J-8-3*(k:Int)
def sideB (J N k : Nat) : Int := 5-12*2^J-12*2^(N-(4*k+3))-6*(k:Int)

theorem scale_pow (d : Nat) : scale d = (2:Int)^(d+6) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    calc
      scale (d+1) = 2*scale d := rfl
      _ = 2*(2:Int)^(d+6) := by rw [ih]
      _ = (2:Int)^(d+6+1) := by rw [Int.pow_succ (2:Int) (d+6), Int.mul_comm 2]
      _ = (2:Int)^(d+1+6) := by congr 1

/-- The checker excludes an entire exact-power side parent, with only the
    N-power removed from its signed representative. No restriction on t or J
    relative to the checker precision is needed. -/
theorem reject_side (J N d k x y : Nat)
    (hN : d+6 ≤ N)
    (hHigh : 36*2^d+6*2^J+8+3*k ≤ 12*2^N)
    (hx : x+6*2^J+8+3*k=12*2^N+6*2^(N-(4*k+3)))
    (hy : y+12*2^J+12*2^(N-(4*k+3))+6*k=24*2^N+5)
    (hc : search basicTest d (sideA J N k) (sideB J N k)=false) : ¬Reach x y := by
  have hpow : (2:Int)^N = scale d * 2^(N-(d+6)) := by
    rw [scale_pow, ← Int.pow_add, show d+6+(N-(d+6))=N by omega]
  have hxI : (x:Int)+6*2^J+8+3*(k:Int)=12*2^N+6*2^(N-(4*k+3)) := by exact_mod_cast hx
  have hyI : (y:Int)+12*2^J+12*2^(N-(4*k+3))+6*(k:Int)=24*2^N+5 := by exact_mod_cast hy
  have hnear : Near (scale d) (sideA J N k) (sideB J N k) x y := by
    refine ⟨12*2^(N-(d+6)),12*2^(N-(d+6)),?_,?_⟩
    · unfold sideA
      rw [Int.mul_left_comm (scale d) 12, ← hpow]
      omega
    · unfold sideB
      rw [Int.mul_assoc 2, Int.mul_left_comm (scale d) 12, ← hpow]
      omega
  exact exclude d _ _ x y (by omega) hnear hc

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

private theorem no_nine_odd (b : Nat) (hb : b%2=1) : ¬ Reach 9 b := by
  intro hr
  obtain ⟨p,q,hp,h⟩ := pred 9 b (by decide) hr
  obtain ⟨hp3,hq⟩ := incoming_nine p q b h
  subst p
  obtain ⟨r,s,hrs,hs⟩ := pred 3 q (by decide) hp
  obtain ⟨hr0,hsq⟩ := incoming_three r s q hs
  subst r
  have hallow := reach_allowed 0 s hrs
  unfold BB429Mod8.Allowed at hallow
  omega

/-- Entire diagonal spine exclusion from a complete finite certificate
    over its exceptional indices. N even makes the unique all-F leaf odd
    at the zero counter, which is impossible at the authentic blank root. -/
theorem no_diagonal_of_certificate (J N d : Nat)
    (hN : d+6 ≤ N) (heven : N%2=0)
    (hHigh : 36*2^d+6*2^J+8+3*N ≤ 12*2^N)
    (hcert : ∀ k, 4*k+3<N → search basicTest d (sideA J N k) (sideB J N k)=false)
    (t a b : Nat) (ht : t≤N)
    (ha : a+3=12*2^t)
    (hb : b+24*2^t+24*2^J+3*(N-t)=48*2^N+15) : ¬Reach a b := by
  induction t generalizing a b with
  | zero =>
    simp at ha hb
    have h9 : a=9 := by omega
    subst a
    exact no_nine_odd b (by omega)
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
      exact reject_side J N d k x y hN (by omega) hx' hy' (hcert k hk) hroot

#print axioms reject_side
#print axioms no_diagonal_of_certificate
end BB429Branch9Diagonal
