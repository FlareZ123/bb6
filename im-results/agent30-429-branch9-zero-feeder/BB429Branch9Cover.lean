import BB429Branch9Clip

namespace BB429Branch9Cover
open BB429NewResidue BB429DyadicTransport BB429DyadicSource BB429Branch9Diagonal BB429Branch9Clip

set_option maxHeartbeats 20000000
set_option maxRecDepth 30000

def classA (J r : Nat) : Int := -6*2^J-8-3*(r:Int)
def classB (J r : Nat) : Int := 5-12*2^J-6*(r:Int)

/-- Reject a complete residue class of interior exceptional indices. -/
theorem reject_class (J N d r q k x y : Nat)
    (hN : d+6 ≤ N) (ht : d+6 ≤ N-(4*k+3))
    (hHigh : 36*2^d+6*2^J+8+3*k ≤ 12*2^N)
    (hk : k=r+2^(d+6)*q)
    (hx : x+6*2^J+8+3*k=12*2^N+6*2^(N-(4*k+3)))
    (hy : y+12*2^J+12*2^(N-(4*k+3))+6*k=24*2^N+5)
    (hc : search basicTest d (classA J r) (classB J r)=false) : ¬Reach x y := by
  let t := N-(4*k+3)
  have hpow (e : Nat) (he : d+6≤e) : (2:Int)^e = scale d * 2^(e-(d+6)) := by
    rw [scale_pow,← Int.pow_add,show d+6+(e-(d+6))=e by omega]
  have hkI : (k:Int)=(r:Int)+(2:Int)^(d+6)*(q:Int) := by exact_mod_cast hk
  rw [← scale_pow] at hkI
  have hxI : (x:Int)+6*2^J+8+3*(k:Int)=12*2^N+6*2^t := by exact_mod_cast hx
  have hyI : (y:Int)+12*2^J+12*2^t+6*(k:Int)=24*2^N+5 := by exact_mod_cast hy
  rw [hpow N hN,hpow t ht] at hxI hyI
  have hnear : Near (scale d) (classA J r) (classB J r) x y := by
    refine ⟨12*2^(N-(d+6))+6*2^(t-(d+6))-3*(q:Int),
      12*2^(N-(d+6))-6*2^(t-(d+6))-3*(q:Int),?_,?_⟩
    · unfold classA
      rw [Int.mul_sub,Int.mul_add]
      repeat' rw [Int.mul_left_comm (scale d)]
      omega
    · unfold classB
      rw [Int.mul_sub,Int.mul_sub]
      have mul3 (v : Int) : (2*scale d)*(3*v)=6*(scale d*v) := by
        rw [Int.mul_assoc,Int.mul_left_comm (scale d) 3,← Int.mul_assoc 2 3,show (2:Int)*3=6 by decide]
      have mul6 (v : Int) : (2*scale d)*(6*v)=12*(scale d*v) := by
        rw [Int.mul_assoc,Int.mul_left_comm (scale d) 6,← Int.mul_assoc 2 6,show (2:Int)*6=12 by decide]
      have mul12 (v : Int) : (2*scale d)*(12*v)=24*(scale d*v) := by
        rw [Int.mul_assoc,Int.mul_left_comm (scale d) 12,← Int.mul_assoc 2 12,show (2:Int)*12=24 by decide]
      rw [mul12,mul6,mul3]
      omega
  exact exclude d _ _ x y (by omega) hnear hc

/-- A low-bit trie, with shallow whole-class rejection at each internal node.
    At a leaf, there is at most one possible k in [0,K), checked at full D.
    Empty classes are accepted vacuously. -/
def cover (J N D K : Nat) : Nat → Nat → Nat → Bool
  | 0, _, r => if r<K then !search basicTest D (clipA J N D r) (clipB J N D r) else true
  | fuel+1, bits, r =>
    if K≤r then true
    else if 6≤bits ∧ search basicTest (bits-6) (classA J r) (classB J r)=false then true
    else cover J N D K fuel (bits+1) r && cover J N D K fuel (bits+1) (r+2^bits)

/-- Soundness of a complete cover, directly in the genuine Reach relation.
    The common interior lower bound guarantees that every omitted t-power
    vanishes at the shallow certificate precision. -/
theorem cover_sound (J N D K : Nat)
    (hN : D+6≤N)
    (hHigh : 36*2^D+6*2^J+8+3*N≤12*2^N)
    (fuel bits r q k x y : Nat)
    (hbits : bits+fuel≤D+6) (hsize : K≤2^(bits+fuel))
    (hinterior : 4*K+(bits+fuel)+3≤N)
    (hk : k<K) (hrep : k=r+2^bits*q)
    (hx : x+6*2^J+8+3*k=12*2^N+6*2^(N-(4*k+3)))
    (hy : y+12*2^J+12*2^(N-(4*k+3))+6*k=24*2^N+5)
    (hc : cover J N D K fuel bits r=true) : ¬Reach x y := by
  induction fuel generalizing bits r q with
  | zero =>
    have hr : r<K := by omega
    have hq : q=0 := by
      by_cases hn : q=0
      · exact hn
      · have hp := Nat.le_mul_of_pos_right (2^bits) (show 0<q by omega)
        simp at hsize
        omega
    have hkr : k=r := by simp [hq] at hrep; exact hrep
    simp only [cover,ite_eq_left hr] at hc
    rw [← hkr] at hc
    exact reject_side_clip J N D k x y hN (by omega) hx hy (by cases h : search basicTest D (clipA J N D k) (clipB J N D k) <;> simp_all)
  | succ fuel ih =>
    have hr : ¬K≤r := by omega
    rw [cover,ite_eq_right hr] at hc
    by_cases hs : 6≤bits ∧ search basicTest (bits-6) (classA J r) (classB J r)=false
    · have hbits' : bits-6+6=bits := by omega
      have hp : (2:Nat)^(bits-6) ≤ 2^D := Nat.pow_le_pow_right (by decide) (by omega)
      apply reject_class J N (bits-6) r q k x y (by omega) (by omega) (by omega) _ hx hy hs.2
      simpa only [hbits'] using hrep
    · rw [ite_eq_right hs,Bool.and_eq_true_iff] at hc
      have hnext : bits+1+fuel=bits+(fuel+1) := by omega
      have hbitsN : bits+1+fuel≤D+6 := by omega
      have hsizeN : K≤2^(bits+1+fuel) := by simpa only [hnext] using hsize
      have hIntN : 4*K+(bits+1+fuel)+3≤N := by omega
      have hq : q=2*(q/2)+q%2 := by omega
      have hmul : 2^bits*q=2^(bits+1)*(q/2)+2^bits*(q%2) := by
        conv => lhs; rw [hq]
        rw [Nat.mul_add,← Nat.mul_assoc,Nat.pow_succ]
      by_cases he : q%2=0
      · have hrepN : k=r+2^(bits+1)*(q/2) := by simp [he] at hmul; omega
        exact ih (bits+1) r (q/2) hbitsN hsizeN hIntN hrepN hc.1
      · have ho : q%2=1 := by omega
        have hrepN : k=(r+2^bits)+2^(bits+1)*(q/2) := by simp [ho] at hmul; omega
        exact ih (bits+1) (r+2^bits) (q/2) hbitsN hsizeN hIntN hrepN hc.2

#print axioms reject_class
#print axioms cover_sound
end BB429Branch9Cover
