import Anti5Source
set_option maxHeartbeats 0
namespace BB6.Agent9Anti5
open BB6.Agent9ReturnGCD BB6.Agent45.DelayedCarry

/-- Any two equal or bitwise-complementary factors of the genuine delayed
    carry selected word at distance five times a power of two have length
    strictly less than 2n+11. This sharpens a general period-two bound. -/
theorem trace_no_five_dyadic_repeat {n m W a : Nat} (hn : 14≤n) (heven : n%2=0)
    (ht : Trace n m W a) (i r : Nat) (flip : Bool)
    (hp : i+5*2^r+(2*n+11)≤m)
    (hrep : ∀ j<2*n+11,
      bit W (i+5*2^r+j)=if flip then 1-bit W (i+j) else bit W (i+j)) : False := by
  obtain ⟨c,w,H⟩ := trace_path hn heven ht
  let p := (2:Nat)^r*5
  let L := 2*n+11
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
    have hh := Nat.mul_le_mul_left (2^r) (show 1≤(5:Nat) by omega)
    simpa using hh
  have hr : r≤n+3 := by
    by_cases hle : r≤n+3
    · exact hle
    · have hpow := Nat.pow_le_pow_right (show 0<2 by decide) (show n+3≤r by omega)
      omega
  let B := n/2+3
  have hB : 2*B=n+6 := by dsimp [B]; omega
  let A := n+3-r
  have hAr : A+r=n+3 := by dsimp [A]; omega
  have hTI : (total n:Int)<(2:Int)^(n+3) := by
    have hh : (total n:Int)<((2^(n+3):Nat):Int) := by omega
    push_cast at hh
    exact hh
  have hscale : 5*((total n:Int)+3)<(2:Int)^(2*B) := by
    have hnscale : 5*(total n+3)<2^(n+6) := by
      unfold total
      rw [Nat.pow_add]
      change 5*(7*2^n+3)<2^n*64
      have hpos := Nat.two_pow_pos n
      omega
    have hi : ((5*(total n+3):Nat):Int)<((2^(n+6):Nat):Int) := by omega
    rw [← hB] at hi
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
  have hgp : (p:Int)=(2:Int)^r*5 := by simp [p,Int.natCast_pow,Int.natCast_mul]
  apply no_scaled_five q (-1) (total n:Int) (p:Int) L A r B
    (fun j => c (i+j)-d j) (fun j => c (i+j)) (fun j => w (i+j)) (fun j => bit W (i+j))
    (Or.inr rfl) hgp (by dsimp [L]; omega)
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

#print axioms trace_no_five_dyadic_repeat
end BB6.Agent9Anti5
