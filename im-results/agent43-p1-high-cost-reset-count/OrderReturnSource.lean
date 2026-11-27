import OrderReturn
import ReturnScaled
namespace BB6.Agent43OrderReturn
open BB6.Agent9ReturnGCD BB6.Agent45.DelayedCarry

/-- A bound on the first return of any confined slope. The order can be
    supplied by a Mersenne divisibility witness, or bounded by the modulus. -/
def ReturnBound (h K : Nat) : Prop :=
  h≤K ∨ (0<K ∧ (h:Int) ∣ (2:Int)^K-1)

theorem no_scaled_bounded_return (q dir C g : Int) (h L A r B K : Nat)
    (a c w x : Nat→Int)
    (hdir : dir=1∨dir= -1) (hodd : h%2=1)
    (hg : g=(2:Int)^r*(h:Int)) (hK : ReturnBound h K)
    (hL : A+r+2*K+B≤L)
    (hinit : -(2:Int)^(A+r)<a 0 ∧ a 0<g+(2:Int)^(A+r))
    (hx : ∀ j<L, x j=0∨x j=1)
    (hs : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hw : ∀ j<L, x j=1 → 2*w (j+1)=w j)
    (ha : ∀ j<L, 2*a (j+1)=a j+g*x j)
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C ∧ 1≤w j ∧ w j≤C)
    (hscale : 2*C<(2:Int)^B) : False := by
  obtain ⟨b,_,hb,hinit'⟩ := scale_slope g h L r A a x hg ha (by omega) hinit
  have hconf := slope_confined (h:Int) b x A (by omega)
    (fun j hj => hx j (by omega)) (fun j hj => hb j (by omega)) hinit'
  let f : Nat→Int := fun j => b (A+j)
  let y : Nat→Int := fun j => x (A+j)
  have hy : ∀ j<L-r-A, y j=0∨y j=1 := fun j hj => hx (A+j) (by omega)
  have hf : ∀ j<L-r-A, 2*f (j+1)=f j+(h:Int)*y j := by
    intro j hj; simpa [f,y,Nat.add_assoc] using hb (A+j) (by omega)
  apply no_bounded_return_slope (q+dir*(A:Int)) dir C (h:Int) K (L-r-A) B f
    (fun j => c (A+j)) (fun j => w (A+j)) y hdir (by omega) _ (by omega)
    (by simpa [f] using hconf) hy _ _ hf _ hscale
  · intro hi
    have hint := slope_interior (h:Int) f y (L-r-A) hi hy hf
    rcases hK with hh|⟨hk,ho⟩
    · obtain ⟨p,hp,hpg,hret,_⟩ := slope_primitive_return h (L-r-A) f y (by omega) (by omega) hint hy hf
      exact ⟨p,hp,by omega,hret⟩
    · exact ⟨K,hk,Nat.le_refl _,order_return (h:Int) f y K ho hi (hint K (by omega)) (fun j hj => hf j (by omega))⟩
  · intro j hj
    have hh := hs (A+j) (by omega)
    simp only [Int.natCast_add,Int.mul_add] at hh
    simpa only [Nat.add_assoc,Int.add_assoc,y] using hh
  · intro j hj h1
    simpa only [Nat.add_assoc] using hw (A+j) (by omega) h1
  · intro j hj; exact hbound (A+j) (by omega)

/-- In a full original delayed-carry trace, two factors a distance 2^r*h
    apart cannot agree, even up to bitwise complement, for 2n+2K+7 bits
    when K bounds the odd slope return. The result is independent of the
    magnitude of h if h divides 2^K-1. -/
theorem trace_no_short_return_repeat {n m W a : Nat} (hn : 14≤n) (heven : n%2=0)
    (ht : Trace n m W a) (i r h K : Nat) (flip : Bool)
    (hodd : h%2=1) (hK : ReturnBound h K)
    (hp : i+2^r*h+(2*n+2*K+7)≤m)
    (hrep : ∀ j<2*n+2*K+7,
      bit W (i+2^r*h+j)=if flip then 1-bit W (i+j) else bit W (i+j)) : False := by
  obtain ⟨c,w,H⟩ := trace_path hn heven ht
  let p := (2:Nat)^r*h
  let L := 2*n+2*K+7
  have hpm : i+p+L≤m := hp
  have hT : total n<2^(n+3) := by
    unfold total
    rw [Nat.pow_add]
    change 7*2^n<2^n*8
    have hpos := Nat.two_pow_pos n
    omega
  have hm := H.mass m (by omega)
  have hb := H.bounds m (by omega)
  have hmul : 2^r≤p := by
    dsimp [p]
    have hh := Nat.mul_le_mul_left (2^r) (show 1≤h by omega)
    simpa using hh
  have hr : r≤n+3 := by
    by_cases hle : r≤n+3
    · exact hle
    · have hpow := Nat.pow_le_pow_right (show 0<2 by decide) (show n+3≤r by omega)
      omega
  let A := n+3-r
  have hAr : A+r=n+3 := by dsimp [A]; omega
  have hTI : (total n:Int)<(2:Int)^(n+3) := by
    have hh : (total n:Int)<((2^(n+3):Nat):Int) := by omega
    push_cast at hh
    exact hh
  have hscale : 2*(total n:Int)<(2:Int)^(n+4) := by
    rw [show n+4=(n+3)+1 by omega,Int.pow_succ]
    omega
  let q : Int := (total n:Int)-n-i-3
  let d : Nat→Int := fun j => if flip then w (i+p+j) else c (i+p+j)
  have hd : ∀ j<L, 2*d (j+1)=d j+(q+(-1)*(j:Int)-(p:Int))*bit W (i+j) := by
    intro j hj
    have hrp := hrep j hj
    change bit W (i+p+j)=if flip then 1-bit W (i+j) else bit W (i+j) at hrp
    have hclock : (total n:Int)-n-(i+p+j:Nat)-3=q+(-1)*(j:Int)-(p:Int) := by
      dsimp [q]; simp; omega
    cases flip with
    | false =>
      have hh := H.stepV (i+p+j) (by omega)
      rw [hclock,show bit W (i+p+j)=bit W (i+j) by simpa using hrp] at hh
      simpa [d,Nat.add_assoc] using hh
    | true =>
      have hh := H.stepW (i+p+j) (by omega)
      have hbit : 1-bit W (i+p+j)=bit W (i+j) := by simp at hrp; omega
      rw [hclock,hbit] at hh
      simpa [d,Nat.add_assoc] using hh
  have hgp : (p:Int)=(2:Int)^r*(h:Int) := by simp [p,Int.natCast_pow,Int.natCast_mul]
  apply no_scaled_bounded_return q (-1) (total n:Int) (p:Int) h L A r (n+4) K
    (fun j => c (i+j)-d j) (fun j => c (i+j)) (fun j => w (i+j)) (fun j => bit W (i+j))
    (Or.inr rfl) hodd hgp hK (by dsimp [L]; omega)
  · have h0 := H.bounds i (by omega)
    have h1 := H.bounds (i+p) (by omega)
    simp only [Nat.add_zero,hAr]
    cases flip <;> simp [d] <;> omega
  · intro j hj; exact bit_binary W (i+j)
  · intro j hj
    have hh := H.stepV (i+j) (by omega)
    have hclock : (total n:Int)-n-(i+j:Nat)-3=q+(-1)*(j:Int) := by dsimp [q]; simp; omega
    rw [hclock] at hh
    simpa only [Nat.add_assoc] using hh
  · intro j hj h1
    have hh := H.stepW (i+j) (by omega)
    simpa [h1,Nat.add_assoc] using hh
  · intro j hj
    have h1 := H.stepV (i+j) (by omega)
    have h2 := hd j hj
    have hclock : (total n:Int)-n-(i+j:Nat)-3=q+(-1)*(j:Int) := by dsimp [q]; simp; omega
    rw [hclock] at h1
    rw [←Nat.add_assoc]
    rcases bit_binary W (i+j) with h0|h1'
    · rw [h0] at h1 h2 ⊢; simp at h1 h2 ⊢; omega
    · rw [h1'] at h1 h2 ⊢; simp at h1 h2 ⊢; omega
  · intro j hj; exact H.bounds (i+j) (by omega)
  · exact hscale

#print axioms no_scaled_bounded_return
#print axioms trace_no_short_return_repeat
end BB6.Agent43OrderReturn
