import AntiShortScaled
set_option maxHeartbeats 0
namespace BB6.Agent9AntiShortTrace
open BB6.Agent9ReturnGCD BB6.Agent45.DelayedCarry BB6.Agent9AntiShortScaled

/-- General original-source forbidden-factor theorem for any odd h dividing
    2^K+1, with no coprimality hypothesis. The required length is n+3+K+B, where
    the mass inequality h*(total n+K+1)<2^B gives the second transient. -/
theorem trace_no_odd_antishort_repeat {n m W a : Nat}
    (hn : 14≤n) (heven : n%2=0) (ht : Trace n m W a)
    (i r h K B : Nat) (flip : Bool)
    (hodd : h%2=1) (hK : 0<K)
    (hmod : (h:Int) ∣ (2:Int)^K+1)
    (hmass : h*(total n+K+1)<2^B)
    (hp : i+2^r*h+(n+3+K+B)≤m)
    (hrep : ∀ j<n+3+K+B,
      bit W (i+2^r*h+j)=if flip then 1-bit W (i+j) else bit W (i+j)) : False := by
  obtain ⟨c,w,H⟩ := trace_path hn heven ht
  let p := (2:Nat)^r*h
  let L := n+3+K+B
  have hpm : i+p+L≤m := by dsimp [p,L]; omega
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
    have hh : (total n:Int)<((2^(n+3:Nat):Nat):Int) := by omega
    push_cast at hh
    exact hh
  have hoddI : (h:Int)%2=1 := by
    have hh : ((h%2:Nat):Int)=1 := by omega
    push_cast at hh
    exact hh
  have hscale : (h:Int)*((total n:Int)+(K:Int)+1)<(2:Int)^B := by
    have hi : ((h*(total n+K+1):Nat):Int)<((2^B:Nat):Int) := by omega
    push_cast at hi
    exact hi
  let q : Int := (total n:Int)-n-i-3
  let d : Nat→Int := fun j => if flip then w (i+p+j) else c (i+p+j)
  have hd : ∀ j<L, 2*d (j+1)=d j+(q+(-1)*(j:Int)-(p:Int))*bit W (i+j) := by
    intro j hj
    have hrp := hrep j (by dsimp [L] at hj; omega)
    have hrp' : bit W (i+p+j)=if flip then 1-bit W (i+j) else bit W (i+j) := by
      simpa only [p,Nat.mul_comm] using hrp
    have hclock : (total n:Int)-n-(i+p+j:Nat)-3=q+(-1)*(j:Int)-(p:Int) := by
      dsimp [q]; simp; omega
    cases flip with
    | false =>
      have hh := H.stepV (i+p+j) (by omega)
      rw [hclock,show bit W (i+p+j)=bit W (i+j) by simpa using hrp'] at hh
      simpa [d,Nat.add_assoc] using hh
    | true =>
      have hh := H.stepW (i+p+j) (by omega)
      have hbit : 1-bit W (i+p+j)=bit W (i+j) := by simp at hrp'; omega
      rw [hclock,hbit] at hh
      simpa [d,Nat.add_assoc] using hh
  have hgp : (p:Int)=(2:Int)^r*(h:Int) := by simp [p,Int.natCast_pow,Int.natCast_mul]
  apply no_scaled_antishort h K A r B L q (-1) (total n:Int) (p:Int)
    (fun j => c (i+j)-d j) (fun j => c (i+j)) (fun j => w (i+j)) (fun j => bit W (i+j))
    (by omega) hoddI hmod hK (Or.inr rfl) hgp (by dsimp [L]; omega)
  · have h0 := H.bounds i (by omega)
    have h1 := H.bounds (i+p) (by omega)
    simp only [Nat.add_zero,hAr]
    cases flip <;> simp [d] <;> omega
  · intro j hj; exact bit_binary W (i+j)
  · intro j hj
    have h1 := H.stepV (i+j) (by omega)
    have h2 := hd j hj
    have hclock : (total n:Int)-n-(i+j:Nat)-3=q+(-1)*(j:Int) := by dsimp [q]; simp; omega
    rw [hclock] at h1
    rw [←Nat.add_assoc]
    rcases bit_binary W (i+j) with h0|h1'
    · rw [h0] at h1 h2 ⊢; simp at h1 h2 ⊢; omega
    · rw [h1'] at h1 h2 ⊢; simp at h1 h2 ⊢; omega
  · intro j hj
    have hh := H.stepV (i+j) (by omega)
    have hclock : (total n:Int)-n-(i+j:Nat)-3=q+(-1)*(j:Int) := by dsimp [q]; simp; omega
    rw [hclock] at hh
    simpa only [Nat.add_assoc] using hh
  · intro j hj
    have hh := H.stepW (i+j) (by omega)
    have hclock : (total n:Int)-n-(i+j:Nat)-3=q+(-1)*(j:Int) := by dsimp [q]; simp; omega
    rw [hclock] at hh
    simpa only [Nat.add_assoc] using hh
  · intro j hj; exact H.bounds (i+j) (by omega)
  · exact hscale

#print axioms trace_no_odd_negacyclic_repeat
end BB6.Agent9AntiShortTrace
