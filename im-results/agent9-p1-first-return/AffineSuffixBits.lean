import AffineSuffix
namespace BB6.Agent9AffineResidue
open BB6.P1CarryExtinction
open BB6.P1CarryExact (weightedTail)

/-- A cyclic subset-sum addition in a packed residue mask. M is the
    number of bits in the mask, not its numeric size. -/
def addResidue (M w bits : Nat) : Nat :=
  let a := w%M
  (bits ||| (bits <<< a) ||| (bits >>> (M-a))) &&& (2^M-1)

theorem addResidue_bound (M w bits i : Nat) (hi : M≤i) :
    (addResidue M w bits).testBit i=false := by
  simp [addResidue,Nat.testBit_and,Nat.testBit_two_pow_sub_one,
    show ¬ i<M by omega]

theorem addResidue_keep (M w bits i : Nat) (hi : i<M)
    (hb : bits.testBit i=true) :
    (addResidue M w bits).testBit i=true := by
  simp [addResidue,Nat.testBit_and,Nat.testBit_or,Nat.testBit_two_pow_sub_one,hi,hb]

theorem addResidue_shift (M w bits i : Nat) (hi : i<M)
    (hb : bits.testBit i=true) :
    (addResidue M w bits).testBit ((i+w)%M)=true := by
  let a := w%M
  have hM : 0<M := by omega
  have ha : a<M := Nat.mod_lt _ hM
  have hz : (i+w)%M=(i+a)%M := by
    rw [Nat.add_mod i w M,Nat.mod_eq_of_lt hi]
  rw [hz]
  unfold addResidue
  change ((bits ||| (bits <<< a) ||| (bits >>> (M-a))) &&& (2^M-1)).testBit ((i+a)%M)=true
  by_cases h : i+a<M
  · rw [Nat.mod_eq_of_lt h]
    simp [Nat.testBit_and,Nat.testBit_or,Nat.testBit_two_pow_sub_one,Nat.testBit_shiftLeft,
      show a≤i+a by omega,show i+a-a=i by omega,h,hb]
  · have hr : i+a-M<M := by omega
    rw [Nat.mod_eq_sub_mod (by omega : M≤i+a),Nat.mod_eq_of_lt hr]
    simp [Nat.testBit_and,Nat.testBit_or,Nat.testBit_two_pow_sub_one,Nat.testBit_shiftRight,
      show M-a+(i+a-M)=i by omega,hr,hb]

/-- Packed exact cyclic support for weighted suffixes starting at absolute
    weight position j, retaining the modulus M throughout. -/
def suffixBits (M n k : Nat) : Nat → Nat → Nat
  | j, 0 => 1
  | j, d+1 =>
    addResidue M ((n+3+k+j)*2^j) (suffixBits M n k (j+1) d)

theorem suffixBits_sound (M n k j : Nat) (hM : 0<M) (ys : List Bool) :
    (suffixBits M n k j ys.length).testBit
      ((2^j*weightedTail n (k+j) ys)%M)=true := by
  induction ys generalizing j with
  | nil => simp [suffixBits,weightedTail]
  | cons b bs ih =>
    have hs := ih (j+1)
    have hk : k+(j+1)=k+j+1 := by omega
    rw [hk] at hs
    let t := 2^(j+1)*weightedTail n (k+j+1) bs
    have ht : t%M<M := Nat.mod_lt _ hM
    have hs' : (suffixBits M n k (j+1) bs.length).testBit (t%M)=true := hs
    change (addResidue M ((n+3+k+j)*2^j)
      (suffixBits M n k (j+1) bs.length)).testBit
      ((2^j*((if b then n+3+(k+j) else 0)+2*weightedTail n (k+j+1) bs))%M)=true
    cases b
    · have he : 2^j*((if false then n+3+(k+j) else 0)+2*weightedTail n (k+j+1) bs)=t := by
        simp only [Bool.false_eq_true,if_false,Nat.zero_add,t,Nat.pow_succ]
        ac_rfl
      rw [he]
      exact addResidue_keep _ _ _ _ ht hs'
    · have he : 2^j*((if true then n+3+(k+j) else 0)+2*weightedTail n (k+j+1) bs)
          =t+(n+3+k+j)*2^j := by
        simp only [if_true,t,Nat.pow_succ,Nat.mul_add,Nat.add_mul]
        ac_rfl
      rw [he]
      have h := addResidue_shift M ((n+3+k+j)*2^j) _ _ ht hs'
      rwa [Nat.mod_add_mod] at h

theorem residue_neg_eq (M A S : Nat) (hM : 0<M)
    (h : (A+S)%M=0) : S%M=(M-A%M)%M := by
  have ha := Nat.mod_lt A hM
  have hs := Nat.mod_lt S hM
  rw [Nat.add_mod] at h
  by_cases hlt : A%M+S%M<M
  · rw [Nat.mod_eq_of_lt hlt] at h
    have hza : A%M=0 := by omega
    have hzs : S%M=0 := by omega
    rw [hza,hzs,Nat.sub_zero,Nat.mod_self]
  · rw [Nat.mod_eq_sub_mod (by omega : M≤A%M+S%M),
      Nat.mod_eq_of_lt (by omega : A%M+S%M-M<M)] at h
    have he : S%M=M-A%M := by omega
    rw [←he,Nat.mod_mod]

/-- Boolean rejection for one parameter. Only a suffix-support
    overapproximation is needed for its soundness; no affine inverse or
    enumeration of full words is required. -/
def suffixReject (k d n : Nat) : Bool :=
  let M := 2^d
  let r := n%2^k
  let T := n/2^k
  let bits := suffixBits M r k 0 d
  (nodes (k-1)).all fun p =>
    p.r != r || !(bits.testBit ((M-(p.a+T*p.B)%M)%M))

theorem suffixReject_sound (k d n : Nat) (hk : 0<k) (hd : d≤k)
    (hc : suffixReject k d n=true) : width (k+d) n=0 := by
  by_cases h : width (k+d) n=0
  · exact h
  exfalso
  have hw : 0<width (k+d) n := by omega
  obtain ⟨p,hp,hr,ys,hy,he⟩ := (width_pos_iff_suffix k d n hk hd).mp hw
  let M := 2^d
  have hM : 0<M := Nat.two_pow_pos _
  have hneg := residue_neg_eq M (p.a+n/2^k*p.B) (weightedTail p.r k ys) hM he
  have hb := suffixBits_sound M p.r k 0 hM ys
  simp only [Nat.pow_zero,Nat.one_mul,Nat.add_zero,hy,hneg] at hb
  unfold suffixReject at hc
  have hh := List.all_eq_true.mp hc p hp
  rw [←hr] at hh
  simp [M,hb] at hh

theorem suffixReject_critical (k d n : Nat) (hk : 0<k) (hd : d≤k)
    (hn : 14≤n) (hKn : k+d≤n) (hc : suffixReject k d n=true) :
    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  intro h
  have hw := BB6.P1CarryExact.critical_reset_requires_width_full n (k+d) (by omega) hn hKn h
  have hz := suffixReject_sound k d n hk hd hc
  omega

/-- The same check certifies an entire residue cylinder at depth k+d. -/
theorem suffixReject_cylinder (k d r n : Nat) (hk : 0<k) (hd : d≤k)
    (hn : 14≤n) (hKn : k+d≤n) (hr : n%2^(k+d)=r)
    (hc : suffixReject k d r=true) :
    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  have hz := suffixReject_sound k d r hk hd hc
  have he : n=r+2^(k+d)*(n/2^(k+d)) := by
    rw [←hr]
    exact (Nat.mod_add_div n _).symm
  intro h
  have hw := BB6.P1CarryExact.critical_reset_requires_width_full n (k+d) (by omega) hn hKn h
  rw [he,width_period,hz] at hw
  omega

#print axioms suffixBits_sound
#print axioms suffixReject_sound
#print axioms suffixReject_critical
#print axioms suffixReject_cylinder
end BB6.Agent9AffineResidue
