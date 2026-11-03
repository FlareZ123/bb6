import ForwardEdgeAlgebra

namespace BB6.Agent17Forward

private theorem p_shift_same (r c b k : Nat) :
    P r c (b+3^k) % 3^k = P r c b % 3^k := by
  have hdiv : 3^k ∣ 3^(k+1) := by
    rw [Nat.pow_succ]
    exact Nat.dvd_mul_right (3^k) 3
  have hs := congrArg (fun z : Nat => z % 3^k) (p_shift_mod r c b k)
  rw [Nat.mod_mod_of_dvd _ hdiv, Nat.mod_mod_of_dvd _ hdiv] at hs
  have hv : (P r c b + 3^k) % 3^k = P r c b % 3^k := by
    rw [Nat.add_mod_right]
  exact hs.trans hv

private theorem odd_pow_three (k : Nat) : (3^k)%2=1 := by
  calc
    (3^k)%2 = ((3%2)^k)%2 := Nat.pow_mod 3 k 2
    _ = 1 := by simp

/-- A positive exponent solving the polynomial congruence exists at every 3-power. -/
theorem positive_root_three (r c k : Nat) :
    ∃ B, 1 ≤ B ∧ P r c B % 3^k = 0 := by
  obtain ⟨b,hbnd,hroot⟩ := p_root_lt r c k
  refine ⟨b+3^k, ?_, ?_⟩
  · have hq : 0<3^k := Nat.pow_pos (by decide)
    omega
  · rw [p_shift_same]
    exact hroot

/-- Complete 3-adic synthetic generic first-even quotient, with arbitrarily large
    legal integer witnesses and exact source/target residues. -/
theorem three_power_all_edges (k r s N : Nat)
    (hr : r < 3^k) (hs : s < 3^k) :
    ∃ b u x y : Nat, 1 ≤ b ∧ N ≤ x ∧ 5 ≤ u ∧
      u%2=1 ∧ u%4=1 ∧ x=4^b*u ∧ x=2^(2*b)*u ∧
      y=x+2*b+(u-1)/2 ∧
      x%2=0 ∧ y%2=0 ∧
      x%(3^k)=r ∧ y%(3^k)=s := by
  let q := 3^k
  let t := (q-1)/2
  let d := r+q-s-1
  have hqodd : q%2=1 := by simpa [q] using odd_pow_three k
  have hqpos : 0<q := Nat.pow_pos (by decide)
  have hq : 2*t+1=q := by dsimp [t]; omega
  have hds : d+s+1=r+q := by dsimp [d]; omega
  obtain ⟨b,hb,hroot⟩ := positive_root_three r (1+2*d) k
  obtain ⟨u,x,y,hxn,hu,hu4,hx,hy,hx2,hy2,hxr,hys⟩ :=
     generic_edge_from_root_unbounded t r s d b N
       (by simpa [hq,q] using hr) (by simpa [hq,q] using hs)
       hb (by simpa [hq] using hds) (by simpa [hq,q] using hroot)
  have huodd : u%2=1 := by omega
  have hpow : (4:Nat)^b=2^(2*b) := by
    rw [show (4:Nat)=2^2 by decide]
    exact (Nat.pow_mul 2 2 b).symm
  have hxpow : x=2^(2*b)*u := by simpa [hpow] using hx
  exact ⟨b,u,x,y,hb,hxn,hu,huodd,hu4,hx,hxpow,hy,hx2,hy2,
         by simpa [hq,q] using hxr,
         by simpa [hq,q] using hys⟩

#print axioms positive_root_three
#print axioms three_power_all_edges
end BB6.Agent17Forward
