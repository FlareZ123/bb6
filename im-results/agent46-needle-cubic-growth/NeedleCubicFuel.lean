
import NeedleFourStep
import Lean.Elab.Tactic.Omega

namespace NeedleFourStep

def Prefix (f : Nat → Nat) (N : Nat) : Prop :=
  ∀ i, i<N → Edge (f i) (f (i+1))

theorem prefix_mono (f : Nat → Nat) (N i t : Nat)
    (hp : Prefix f N) (ht : i+t≤N) : f i≤f (i+t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hi := ih (by omega)
    have hs := edge_strict (hp (i+t) (by omega))
    rw [show i+(t+1)=i+t+1 by omega]
    omega

theorem prefix_end_bound (f : Nat → Nat) (N i : Nat)
    (hp : Prefix f N) (hi : i≤N) : f i≤f N := by
  have h := prefix_mono f N i (N-i) hp (by omega)
  rwa [show i+(N-i)=N by omega] at h

theorem block_gain (f : Nat → Nat) (N i L H m : Nat)
    (hp : Prefix f N) (hi : i+4≤N)
    (hL : 0<L) (hbits : f N<2^L)
    (hH : 16*L≤H^3) (hm : m^3≤f i) :
    H*f i+m^2≤H*f (i+4) := by
  have hbit : f i<2^L := Nat.lt_of_le_of_lt (prefix_end_bound f N i hp (by omega)) hbits
  have h0 := hp i (by omega)
  have h1 := hp (i+1) (by omega)
  have h2 := hp (i+2) (by omega)
  have h3 := hp (i+3) (by omega)
  have hg : (f i)^2≤16*L*(f (i+4)-f i)^3 :=
    four_step_cube_gain hL hbit h0 h1 h2 h3
  let G := f (i+4)-f i
  change (f i)^2≤16*L*G^3 at hg
  have hpow1 := Nat.pow_le_pow_left hm 2
  have hpow2 : (m^2)^3≤(f i)^2 := by
    have heq : (m^2)^3=(m^3)^2 := by grind
    rwa [heq]
  have hpow3 : (f i)^2≤(H*G)^3 := by
    calc
      (f i)^2 ≤ (16*L)*G^3 := hg
      _ ≤ H^3*G^3 := Nat.mul_le_mul_right _ hH
      _ = (H*G)^3 := by grind
  have hgain : m^2≤H*G := by
    by_cases h : m^2≤H*G
    · exact h
    · have hlt := Nat.pow_lt_pow_left (by omega : H*G<m^2) (by decide : 3≠0)
      omega
  have hmon := prefix_mono f N i 4 hp hi
  have heq : f i+G=f (i+4) := by dsimp [G]; omega
  have hmulteq : H*(f i+G)=H*f (i+4) := by rw [heq]
  rw [Nat.mul_add] at hmulteq
  omega

theorem batch_gain (f : Nat → Nat) (N i L H m t : Nat)
    (hp : Prefix f N) (hi : i+4*t≤N)
    (hL : 0<L) (hbits : f N<2^L)
    (hH : 16*L≤H^3) (hm : m^3≤f i) :
    H*f i+t*m^2≤H*f (i+4*t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hprev := ih (by omega)
    have hmon := prefix_mono f N i (4*t) hp (by omega)
    have hmnow : m^3≤f (i+4*t) := by omega
    have hs := block_gain f N (i+4*t) L H m hp (by omega) hL hbits hH hmnow
    rw [show i+4*(t+1)=i+4*t+4 by omega,Nat.add_mul]
    omega

theorem cube_next (m : Nat) (hm : 1≤m) :
    (m+1)^3≤m^3+7*m^2 := by
  have h1 : m≤m^2 := by
    have h := Nat.mul_le_mul_left m hm
    simpa [Nat.pow_succ] using h
  have h2 : 1≤m^2 := by omega
  have heq : (m+1)^3=m^3+3*m^2+3*m+1 := by grind
  omega

theorem batch_cube_gain (f : Nat → Nat) (N i L H m : Nat)
    (hp : Prefix f N) (hi : i+28*H≤N)
    (hL : 0<L) (hbits : f N<2^L)
    (hH : 16*L≤H^3) (hm : 1≤m) (hstart : m^3≤f i) :
    (m+1)^3≤f (i+28*H) := by
  have ht : i+4*(7*H)≤N := by omega
  have h := batch_gain f N i L H m (7*H) hp ht hL hbits hH hstart
  have heq : i+4*(7*H)=i+28*H := by omega
  rw [heq] at h
  have hfactor : H*(f i+7*m^2)≤H*f (i+28*H) := by
    have heq2 : H*(f i+7*m^2)=H*f i+(7*H)*m^2 := by grind
    rwa [heq2]
  have hpos : 0<H := by
    cases H with
    | zero => simp at hH; omega
    | succ H => omega
  have hle := Nat.le_of_mul_le_mul_left hfactor hpos
  have hn := cube_next m hm
  omega

theorem prefix_cubic (f : Nat → Nat) (N L H k : Nat)
    (hp : Prefix f N) (hbase : 1≤f 0)
    (hL : 0<L) (hbits : f N<2^L) (hH : 16*L≤H^3)
    (hk : 28*H*k≤N) :
    (k+1)^3≤f (28*H*k) := by
  induction k with
  | zero => simpa using hbase
  | succ k ih =>
    have heq : 28*H*(k+1)=28*H*k+28*H := by rw [Nat.mul_add]; simp
    have hkprev : 28*H*k≤N := by omega
    have hstart := ih hkprev
    have hnext := batch_cube_gain f N (28*H*k) L H (k+1) hp
      (by omega) hL hbits hH (by omega) hstart
    rwa [heq]

theorem prefix_cutoff (f : Nat → Nat) (N L H R : Nat)
    (hp : Prefix f N) (hbase : 1≤f 0)
    (hL : 0<L) (hbits : f N<2^L) (hH : 16*L≤H^3)
    (hR : f N<R^3) :
    N<28*H*R := by
  by_cases hN : N<28*H*R
  · exact hN
  · have hk : 28*H*R≤N := by omega
    have h := prefix_cubic f N L H R hp hbase hL hbits hH hk
    have hmono := prefix_end_bound f N (28*H*R) hp hk
    have hpow := Nat.pow_le_pow_left (by omega : R≤R+1) 3
    omega

def cubeFuel (d : Nat) : Nat :=
  let L := Nat.log2 (d+2)+1
  let H := 4*2^((Nat.log2 L+1)/3)
  let R := 2^((L+2)/3)
  28*H*R

/-- For any successful exact edge prefix starting positive, if its final
shifted counter is d+2, its length is below the executable cubeFuel. -/
theorem prefix_cube_fuel (f : Nat → Nat) (N d : Nat)
    (hp : Prefix f N) (hbase : 1≤f 0) (hend : f N=d+2) :
    N<cubeFuel d := by
  let L := Nat.log2 (d+2)+1
  let H := 4*2^((Nat.log2 L+1)/3)
  let R := 2^((L+2)/3)
  have hL : 0<L := by dsimp [L]; omega
  have hbit : f N<2^L := by
    rw [hend]
    exact ((Nat.log2_eq_iff (by omega : d+2≠0)).mp rfl).2
  have hHL : L<2^(Nat.log2 L+1) := ((Nat.log2_eq_iff (by omega : L≠0)).mp rfl).2
  have hHindex : Nat.log2 L+1≤3*((Nat.log2 L+1)/3)+2 := by omega
  have hHpow := Nat.pow_le_pow_right (n:=2) (by decide : 0<2) hHindex
  have hH : 16*L≤H^3 := by
    have hE : H^3=64*2^(3*((Nat.log2 L+1)/3)) := by
      unfold H
      rw [Nat.mul_pow, ←Nat.pow_mul, Nat.mul_comm ((Nat.log2 L+1)/3) 3]
    have hpow2 : 2^(3*((Nat.log2 L+1)/3)+2)=4*2^(3*((Nat.log2 L+1)/3)) := by
      rw [Nat.pow_add]
      simp [Nat.mul_comm]
    rw [hE]
    calc
      16*L≤16*2^(Nat.log2 L+1) := Nat.mul_le_mul_left 16 (Nat.le_of_lt hHL)
      _ ≤16*2^(3*((Nat.log2 L+1)/3)+2) := Nat.mul_le_mul_left 16 hHpow
      _ =64*2^(3*((Nat.log2 L+1)/3)) := by rw [hpow2]; ring

  have hRindex : L≤3*((L+2)/3) := by omega
  have hRpow := Nat.pow_le_pow_right (n:=2) (by decide : 0<2) hRindex
  have hR : f N<R^3 := by
    have hE : R^3=2^(3*((L+2)/3)) := by
      unfold R
      rw [←Nat.pow_mul, Nat.mul_comm ((L+2)/3) 3]
    rw [hE]
    omega
  exact prefix_cutoff f N L H R hp hbase hL hbit hH hR

#print axioms prefix_cubic
#print axioms prefix_cutoff
#print axioms prefix_cube_fuel
end NeedleFourStep
