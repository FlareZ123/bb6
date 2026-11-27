import WeightedDigitGap
namespace BB6.Agent43PackedWeight
open BB6.Agent45WeightedDigitGap (digitWeight corr_le_mul)
open BB6.Agent45ReverseBlock (corr)

/-- Sum of bit indices weighted by their powers of two. This formulation
is independent of padding above the highest selected bit. -/
def idx : Nat → Nat → Nat
  | 0,_ => 0
  | k+1,B => 2*(idx k (B/2)+B/2)

theorem idx_eq (k B : Nat) (hb : B<2^k) : idx k B=digitWeight k B := by
  induction k generalizing B with
  | zero =>
    have h : B=0 := by simpa using hb
    simp [h,idx,digitWeight,corr]
  | succ k ih =>
    have hdiv : B/2<2^k := by rw [Nat.pow_succ] at hb; omega
    have hle := corr_le_mul k (B/2) hdiv
    have hB : B=2*(B/2)+B%2 := by omega
    have hprod : (k+1)*B=2*(k*(B/2))+2*(B/2)+(k+1)*(B%2) := by
      calc
        _ = (k+1)*(2*(B/2)+B%2) := congrArg ((k+1)*·) hB
        _ = _ := by simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul]; ac_rfl
    rw [idx,ih _ hdiv,digitWeight,digitWeight,corr,hprod]
    omega

theorem idx_zero (k : Nat) : idx k 0=0 := by induction k <;> simp_all [idx]

/-- Exact concatenation: high indices gain the width of the low word. -/
theorem idx_split (k j B : Nat) :
    idx (k+j) B = idx k (B%2^k)+2^k*(idx j (B/2^k)+k*(B/2^k)) := by
  induction k generalizing B with
  | zero => simp [idx]
  | succ k ih =>
    let p := 2^k
    have hp : 0<p := Nat.two_pow_pos _
    have hdiv : B/2/p=B/(p*2) := by rw [Nat.div_div_eq_div_mul,Nat.mul_comm]
    have hm : B%(p*2)=B%2+2*((B/2)%p) := by
      rw [Nat.mul_comm p 2,Nat.mod_mul]
    have hmoddiv : (B%(p*2))/2=(B/2)%p := by rw [hm]; omega
    have hdecomp : B/2=(B/2)%p+p*(B/(p*2)) := by rw [←hdiv]; simpa [Nat.add_comm] using (Nat.div_add_mod (B/2) p).symm
    rw [show k+1+j=k+j+1 by omega,idx,ih (B/2),Nat.pow_succ,idx,hmoddiv,hdiv]
    change 2*(idx k (B/2%p)+p*(idx j (B/(p*2))+k*(B/(p*2)))+B/2) =
      2*(idx k (B/2%p)+B/2%p)+p*2*(idx j (B/(p*2))+(k+1)*(B/(p*2)))
    calc
      _ = 2*(idx k (B/2%p)+p*(idx j (B/(p*2))+k*(B/(p*2)))+(B/2%p+p*(B/(p*2)))) := congrArg (fun x => 2*(idx k (B/2%p)+p*(idx j (B/(p*2))+k*(B/(p*2)))+x)) hdecomp
      _ = _ := by simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul]; ac_rfl

theorem idx_pad (k j B : Nat) (hb : B<2^k) : idx (k+j) B=idx k B := by
  rw [idx_split,Nat.mod_eq_of_lt hb,Nat.div_eq_of_lt hb,idx_zero]
  simp

/-- Binary index bit j for all positions in a 2^L-bit word.
The upper half repeats low planes; the new top plane is all upper bits. -/
def indexMask (j : Nat) : Nat → Nat
  | 0 => 0
  | L+1 =>
    let p := 2^(2^L)
    if j=L then p*(p-1)
    else let m := indexMask j L; m+p*m

theorem mask_bound (j L : Nat) : indexMask j L<2^(2^L) := by
  induction L with
  | zero => simp [indexMask]
  | succ L ih =>
    let p := 2^(2^L)
    have hp : 0<p := Nat.two_pow_pos _
    have hp2 : 2^(2^(L+1))=p*p := by
      rw [Nat.pow_succ,show 2^L*2=2^L+2^L by omega,Nat.pow_add]
    rw [hp2,indexMask]
    change (if j=L then p*(p-1) else indexMask j L+p*indexMask j L)<p*p
    split
    · exact Nat.mul_lt_mul_of_pos_left (by omega) hp
    · have hm : indexMask j L+1≤p := by omega
      have h := Nat.mul_le_mul_left p hm
      rw [Nat.mul_add,Nat.mul_one] at h
      omega

theorem and_bound (w x y : Nat) (hx : x<2^w) : x&&&y<2^w := by
  exact Nat.lt_of_le_of_lt (Nat.and_le_left x y) hx

theorem and_join (w lo hi m n : Nat) (hlo : lo<2^w) (hm : m<2^w) :
    (lo+2^w*hi)&&&(m+2^w*n) = (lo&&&m)+2^w*(hi&&&n) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and,Nat.add_comm lo,Nat.testBit_two_pow_mul_add _ hlo,
    Nat.add_comm m,Nat.testBit_two_pow_mul_add _ hm,
    Nat.add_comm (lo&&&m),Nat.testBit_two_pow_mul_add _ (and_bound w lo m hlo)]
  split <;> simp [Nat.testBit_and,*]

theorem and_mask (w a : Nat) (ha : a<2^w) : a&&&(2^w-1)=a := by
  rw [Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt ha]

/-- Only L broadword intersections, with precomputable index masks. -/
def planeSum (L B : Nat) : Nat → Nat
  | 0 => 0
  | j+1 => planeSum L B j+2^j*(B&&&indexMask j L)

theorem planes_split (L j lo hi : Nat) (hj : j≤L) (hlo : lo<2^(2^L)) :
    planeSum (L+1) (lo+2^(2^L)*hi) j =
      planeSum L lo j+2^(2^L)*planeSum L hi j := by
  induction j with
  | zero => simp [planeSum]
  | succ j ih =>
    have hj' : j≠L := by omega
    rw [planeSum,planeSum,planeSum,ih (by omega),indexMask,if_neg hj',
      and_join _ _ _ _ _ hlo (mask_bound j L)]
    simp only [Nat.mul_add]
    ac_rfl

theorem planes_full (L lo hi : Nat) (hlo : lo<2^(2^L)) (hhi : hi<2^(2^L)) :
    planeSum (L+1) (lo+2^(2^L)*hi) (L+1) =
      planeSum L lo L+2^(2^L)*(planeSum L hi L+2^L*hi) := by
  let p := 2^(2^L)
  have hp : 0<p := Nat.two_pow_pos _
  rw [planeSum,planes_split L L lo hi (by omega) hlo,indexMask,if_pos rfl]
  have htop : p*(p-1)=0+p*(p-1) := by simp
  change planeSum L lo L+p*planeSum L hi L+2^L*((lo+p*hi)&&&(p*(p-1)))=_
  rw [htop,and_join _ _ _ _ _ hlo (by omega : 0<2^(2^L))]
  simp only [Nat.and_zero,Nat.zero_add,and_mask _ hi hhi,Nat.mul_add]
  ac_rfl

theorem planes_eq (L B : Nat) (hb : B<2^(2^L)) :
    planeSum L B L=idx (2^L) B := by
  induction L generalizing B with
  | zero =>
    have hd : B/2=0 := by simp at hb; omega
    simp [planeSum,idx,hd]
  | succ L ih =>
    let M := 2^L
    let p := 2^M
    let lo := B%p
    let hi := B/p
    have hp : 0<p := Nat.two_pow_pos _
    have hlo : lo<p := Nat.mod_lt _ hp
    have hp2 : 2^(2^(L+1))=p*p := by
      rw [Nat.pow_succ,show 2^L*2=2^L+2^L by omega,Nat.pow_add]
    have hhi : hi<p := by
      apply (Nat.div_lt_iff_lt_mul hp).2
      simpa [hp2] using hb
    have he : B=lo+p*hi := by simpa [lo,hi,Nat.add_comm] using (Nat.div_add_mod B p).symm
    rw [show 2^(L+1)=M+M by rw [Nat.pow_succ]; dsimp [M]; omega,idx_split]
    change planeSum (L+1) B (L+1)=idx M lo+p*(idx M hi+M*hi)
    conv_lhs => rw [he]
    rw [planes_full L lo hi hlo hhi,ih lo hlo,ih hi hhi]

def fastWeight (L B : Nat) : Nat := planeSum L B L

theorem fastWeight_eq (L k B : Nat) (hk : k≤2^L) (hb : B<2^k) :
    fastWeight L B=digitWeight k B := by
  unfold fastWeight
  rw [planes_eq L B (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0<2) hk)),
      show 2^L=k+(2^L-k) by omega,idx_pad k (2^L-k) B hb,idx_eq k B hb]

#print axioms idx_split
#print axioms planes_eq
#print axioms fastWeight_eq
end BB6.Agent43PackedWeight
