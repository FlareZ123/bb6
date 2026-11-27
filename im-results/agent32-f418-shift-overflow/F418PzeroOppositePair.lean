import F418TopPairGate
import F418PzeroGate
import F418SparseGate

namespace BB6.Agent32F418.PzeroBlock
open ReturnBounds.Prefix

/-- The normalized lower component remains a witness to an even bit:
    a near-power window centered at an even exponent cannot become
    an odd-only word by subtracting seven. -/
theorem near_even_power_noEven {s v : Nat} (hs : s%2=0)
    (hv : v%2=1) (h7 : 7≤v)
    (hl : 15*2^s<16*v) (hu : 16*v<17*2^s) :
    ¬NoEven (v-7) := by
  intro hn
  by_cases hsmall : s<6
  · have hcases : s=0 ∨ s=2 ∨ s=4 := by omega
    rcases hcases with rfl|rfl|rfl <;> simp at hl hu <;> omega
  · have h64 : 64≤2^s := pow_mono (by omega : 6≤s)
    have hpow : 2^(s+1)=2^s*2 := Nat.pow_succ 2 s
    have hlow : v-7<2^(s+1) := by rw [hpow]; omega
    have hbound := SparseGate.noEven_bound (s+1) hlow hn
    have hodd : (s+1)%2≠0 := by omega
    simp only [if_neg hodd,Nat.add_zero] at hbound
    rw [hpow] at hbound
    omega

/-- Subtracting seven from two opposite-parity, widely separated
    near-power components cannot remove every even-position bit. -/
theorem opposite_pair_noEven {a s v : Nat} (ha : s+5≤a)
    (hpar : (a-s)%2=1) (hv : v%2=1)
    (hl : 15*2^s<16*v) (hu : 16*v<17*2^s) :
    ¬NoEven (2^a+v-7) := by
  intro hn
  have h32 : 32≤2^a := pow_mono (by omega : 5≤a)
  have hp : 2^(s+1)=2^s*2 := Nat.pow_succ 2 s
  have hvs : v<2^(s+1) := by rw [hp]; omega
  have hva : v<2^a := Nat.lt_of_lt_of_le hvs (pow_mono (by omega))
  by_cases h7 : 7≤v
  · have hsplit : 2^a+v-7=2^a+(v-7) := Nat.add_sub_assoc h7 _
    have hr : v-7<2^a := by omega
    have hb : (2^a+v-7).testBit a=true := by
      rw [hsplit,show 2^a+(v-7)=2^a*1+(v-7) by omega,
        Nat.testBit_two_pow_mul_add _ hr]
      simp
    have hao : a%2=1 := by
      by_cases h : a%2=1
      · exact h
      · have hh := hn a (by omega)
        rw [hb] at hh
        contradiction
    have hse : s%2=0 := by omega
    have hnr : NoEven (v-7) := by
      apply noEven_low (H:=1) hr
      rw [Nat.mul_one,←hsplit]
      exact hn
    exact near_even_power_noEven hse hv h7 hl hu hnr
  · have h8 : 8≤2^(a-2) := pow_mono (by omega : 3≤a-2)
    have he : 2^a=4*2^(a-2) := by
      rw [←Nat.pow_add (a:=2) (m:=2) (n:=a-2)]
      congr 1
      omega
    exact top_pair_not_noEven (h:=a-2)
      (by rw [he]; omega : 3*2^(a-2)≤2^a+v-7)
      (by rw [he]; omega) hn

/-- A maximal p=0 run cannot reach an odd-only endpoint from a pair
    of separated opposite-parity top powers whose lower component is
    within 1/16 of its nominal power. This includes a zero-length run. -/
theorem opposite_pair_survives_pzero {B h T l u : Nat}
    (hgap : h+5≤B) (hpar : (B-h)%2=1)
    (hlo : 15*2^h<16*T) (hhi : 16*T<17*2^h)
    (hu : u%2=1) (he : 2^B+T=2^l*u) :
    ¬NoEven (replay (2^B+T) (B+1) l-7) := by
  have hTpos : 0<T := by have := Nat.two_pow_pos h; omega
  have hTbound : T<2^(h+1) := by rw [Nat.pow_succ]; omega
  have hl : l≤h := by
    by_cases hle : l≤h
    · exact hle
    · have hd1 : 2^(h+1) ∣ 2^B := by
        refine ⟨2^(B-(h+1)),?_⟩
        rw [←Nat.pow_add]
        congr 1
        omega
      have hd2 : 2^(h+1) ∣ 2^l*u := by
        refine ⟨2^(l-(h+1))*u,?_⟩
        rw [←Nat.mul_assoc,←Nat.pow_add]
        congr 2
        omega
      have hm := Nat.mod_eq_zero_of_dvd hd2
      rw [←he,Nat.add_mod,Nat.mod_eq_zero_of_dvd hd1,Nat.zero_add,Nat.mod_mod,
        Nat.mod_eq_of_lt hTbound] at hm
      omega
  let a := B-l
  let s := h-l
  have hBa : 2^B=2^l*2^a := by rw [←Nat.pow_add]; congr 1; dsimp [a]; omega
  have hhs : 2^h=2^l*2^s := by rw [←Nat.pow_add]; congr 1; dsimp [s]; omega
  have hu_gt : 2^a<u := by
    by_cases hle : u≤2^a
    · have hm := Nat.mul_le_mul_left (2^l) hle
      rw [←hBa,←he] at hm
      omega
    · omega
  let v := u-2^a
  have huv : u=2^a+v := by dsimp [v]; omega
  have hTv : T=2^l*v := by
    have hh := he
    rw [huv,Nat.mul_add,←hBa] at hh
    omega
  have ha : s+5≤a := by dsimp [a,s]; omega
  have hap : (a-s)%2=1 := by
    have he' : a-s=B-h := by dsimp [a,s]; omega
    rw [he']; exact hpar
  have hae : 2^a%2=0 := by
    have hapos : 0<a := by omega
    rw [show a=(a-1)+1 by omega,Nat.pow_succ]
    simp
  have hvo : v%2=1 := by
    rw [huv,Nat.add_mod,hae,Nat.zero_add,Nat.mod_mod] at hu
    exact hu
  have hlo' : 15*2^s<16*v := by
    have hh := hlo
    rw [hhs,hTv,show 15*(2^l*2^s)=2^l*(15*2^s) by ac_rfl,
      show 16*(2^l*v)=2^l*(16*v) by ac_rfl] at hh
    exact (Nat.mul_lt_mul_left (Nat.two_pow_pos l)).mp hh
  have hhi' : 16*v<17*2^s := by
    have hh := hhi
    rw [hhs,hTv,show 16*(2^l*v)=2^l*(16*v) by ac_rfl,
      show 17*(2^l*2^s)=2^l*(17*2^s) by ac_rfl] at hh
    exact (Nat.mul_lt_mul_left (Nat.two_pow_pos l)).mp hh
  have hvs : v<2^(s+1) := by rw [Nat.pow_succ]; omega
  have hva : v<2^a := Nat.lt_of_lt_of_le hvs (pow_mono (by omega))
  have h32 : 32≤2^a := pow_mono (by omega : 5≤a)
  have hu7 : 7≤u := by omega
  have huvbound : u-7<2^(a+4) := by
    have hh : u<2^(a+1) := by rw [huv,Nat.pow_succ]; omega
    exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hh) (pow_mono (by omega))
  have hreplay : replay (2^B+T) (B+1) l-7=
      2^(a+4)*pulses l+(u-7) := by
    rw [he,replay_terminal u l (B+1) (by omega),
      show B+1-l+3=a+4 by dsimp [a]; omega]
    omega
  intro hn
  have hun := noEven_low (H:=pulses l) huvbound (by rw [←hreplay]; exact hn)
  rw [huv] at hun
  exact opposite_pair_noEven ha hap hvo hlo' hhi' hun

/-- Source-return specialization. A modest odd-p return whose old high
    tail is strictly below 17/16 of its top power cannot enter an
    odd-only gate even after a maximal run of p=0 returns. -/
theorem normal_odd_sparse_pzero_exclusion {b : Prefix} {Q W l u : Nat}
    (hp : b.p%2=1) (hW : 9*b.p+8≤W)
    (hQlo : 2^(W-b.L-1)≤Q)
    (hQhi : 16*Q<17*2^(W-b.L-1))
    (hu : u%2=1) (he : b.next Q W+7=2^l*u) :
    ¬NoEven (replay (b.next Q W+7) (W+b.E+1) l-7) := by
  let h := W-b.L-1
  let B := W+b.E
  have hh : 4≤h := by simp [h,L]; omega
  have hC : b.C<2^(h-4) :=
    Nat.lt_of_lt_of_le (correction_upper b) (pow_mono (by simp [h,L,E]; omega))
  have hClo : 7<b.C := by
    have hgt := correction_gt_pow (b:=b) (by omega : 0<b.p)
    have h8 : 8≤2^b.E := pow_mono (by simp [E]; omega : 3≤b.E)
    omega
  have hpower : 2^h=16*2^(h-4) := by
    rw [←Nat.pow_add (a:=2) (m:=4) (n:=h-4)]
    congr 1
    omega
  have hb : b.C≤Q := by omega
  let T := Q-b.C+7
  have hTlo : 15*2^h<16*T := by dsimp [T]; omega
  have hThi : 16*T<17*2^h := by dsimp [T]; omega
  have hn : b.next Q W+7=2^B+T := by
    unfold next
    dsimp [B,T]
    rw [Nat.add_sub_assoc hb]
    omega
  have hgap : h+5≤B := by simp [h,B,L,E]; omega
  have hpar : (B-h)%2=1 := by
    have hdiff : B-h=7*b.p+4 := by simp [h,B,L,E]; omega
    rw [hdiff]
    omega
  rw [hn]
  exact opposite_pair_survives_pzero hgap hpar hTlo hThi hu (hn.symm.trans he)

#print axioms near_even_power_noEven
#print axioms opposite_pair_noEven
#print axioms opposite_pair_survives_pzero
#print axioms normal_odd_sparse_pzero_exclusion
end BB6.Agent32F418.PzeroBlock
