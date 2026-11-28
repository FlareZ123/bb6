import CyclicTraceShort
import ReturnTrace
set_option maxHeartbeats 0
namespace BB6.Agent9CyclicTraceLocal
open BB6.Agent9ReturnGCD BB6.Agent45.DelayedCarry BB6.Agent9CyclicShort

/-- Cost-adaptive P1 repeated-factor restriction. Unlike the global
    n+3+K+B bound, both the slope-settling time A+r and the integer
    logarithmic extinction margin B now depend on the *remaining*
    positive mass C=7*2^n-(n+i+2) at the factor's starting location i.
    This is a local relative bound and can be dramatically shorter near
    a hypothetical late critical clock. -/
theorem trace_no_odd_short_repeat_local {n m W a : Nat}
    (hn : 14≤n) (heven : n%2=0) (ht : Trace n m W a)
    (i A r h K B : Nat) (flip : Bool)
    (hodd : h%2=1)
    (horder : (h:Int)∣(2:Int)^K-1) (hK : 0<K)
    (hsettle : total n-(n+i+2)<2^(A+r))
    (hmass : h*(total n-(n+i+2)+K+1)<2^B)
    (hp : i+2^r*h+(A+r+K+B)≤m)
    (hrep : ∀ j<A+r+K+B,
      bit W (i+2^r*h+j)=if flip then 1-bit W (i+j) else bit W (i+j)) :
    False := by
  obtain ⟨c,w,H⟩ := trace_path hn heven ht
  let p := (2:Nat)^r*h
  let L := A+r+K+B
  have hpm : i+p+L≤m := by dsimp [p,L]; omega
  have hmi := H.mass i (by omega)
  have hbi := H.bounds i (by omega)
  have hTi : n+i+2≤total n := by omega
  let C : Nat := total n-(n+i+2)
  have hCeq : (C:Int)=(total n:Int)-n-i-2 := by
    dsimp [C]
    omega
  have hCpower : (C:Int)<(2:Int)^(A+r) := by
    have hh : (C:Int)<((2^(A+r:Nat):Nat):Int) := by
      dsimp [C]
      omega
    push_cast at hh
    exact hh
  have hoddI : (h:Int)%2=1 := by
    have hh : ((h%2:Nat):Int)=1 := by omega
    push_cast at hh
    exact hh
  have hscale : (h:Int)*((C:Int)+(K:Int)+1)<(2:Int)^B := by
    have hi : ((h*(C+K+1):Nat):Int)<((2^B:Nat):Int) := by
      dsimp [C]
      omega
    push_cast at hi
    exact hi
  have hlocal : ∀ j≤L,
      1≤c (i+j) ∧ c (i+j)≤(C:Int) ∧
      1≤w (i+j) ∧ w (i+j)≤(C:Int) := by
    intro j hj
    have hcb := H.bounds (i+j) (by omega)
    have hcm := H.mass (i+j) (by omega)
    rw [hCeq]
    omega
  let q : Int := (total n:Int)-n-i-3
  let d : Nat→Int := fun j => if flip then w (i+p+j) else c (i+p+j)
  have hd : ∀ j<L, 2*d (j+1)=
      d j+(q+(-1)*(j:Int)-(p:Int))*bit W (i+j) := by
    intro j hj
    have hrp := hrep j (by dsimp [L] at hj; omega)
    have hrp' : bit W (i+p+j)=
        if flip then 1-bit W (i+j) else bit W (i+j) := by
      simpa only [p,Nat.mul_comm] using hrp
    have hclock : (total n:Int)-n-(i+p+j:Nat)-3=
        q+(-1)*(j:Int)-(p:Int) := by
      dsimp [q]; simp; omega
    cases flip with
    | false =>
      have hh := H.stepV (i+p+j) (by omega)
      rw [hclock,show bit W (i+p+j)=bit W (i+j) by simpa using hrp'] at hh
      simpa [d,Nat.add_assoc] using hh
    | true =>
      have hh := H.stepW (i+p+j) (by omega)
      have hbit : 1-bit W (i+p+j)=bit W (i+j) := by
        simp at hrp'
        omega
      rw [hclock,hbit] at hh
      simpa [d,Nat.add_assoc] using hh
  have hgp : (p:Int)=(2:Int)^r*(h:Int) := by
    simp [p,Int.natCast_pow,Int.natCast_mul]
  apply no_scaled_short h K A r B L q (-1) (C:Int) (p:Int)
    (fun j => c (i+j)-d j) (fun j => c (i+j))
    (fun j => w (i+j)) (fun j => bit W (i+j))
    (by omega) hoddI horder hK (Or.inr rfl) hgp
    (by dsimp [L]; omega)
  · have h0 := H.bounds i (by omega)
    have h1 := H.bounds (i+p) (by omega)
    have hm1 := H.mass (i+p) (by omega)
    have hp0 : 0≤(p:Int) := by omega
    simp only [Nat.add_zero]
    cases flip <;> simp [d] <;> omega
  · intro j hj
    exact bit_binary W (i+j)
  · intro j hj
    have h1 := H.stepV (i+j) (by omega)
    have h2 := hd j hj
    have hclock : (total n:Int)-n-(i+j:Nat)-3=
        q+(-1)*(j:Int) := by dsimp [q]; simp; omega
    rw [hclock] at h1
    rw [←Nat.add_assoc]
    rcases bit_binary W (i+j) with h0|h1'
    · rw [h0] at h1 h2 ⊢
      simp at h1 h2 ⊢
      omega
    · rw [h1'] at h1 h2 ⊢
      simp at h1 h2 ⊢
      omega
  · intro j hj
    have hh := H.stepV (i+j) (by omega)
    have hclock : (total n:Int)-n-(i+j:Nat)-3=
        q+(-1)*(j:Int) := by dsimp [q]; simp; omega
    rw [hclock] at hh
    simpa only [Nat.add_assoc] using hh
  · intro j hj
    have hh := H.stepW (i+j) (by omega)
    have hclock : (total n:Int)-n-(i+j:Nat)-3=
        q+(-1)*(j:Int) := by dsimp [q]; simp; omega
    rw [hclock] at hh
    simpa only [Nat.add_assoc] using hh
  · intro j hj
    exact hlocal j hj
  · exact hscale

#print axioms trace_no_odd_short_repeat_local
end BB6.Agent9CyclicTraceLocal
