import F418QueueInvariant

namespace BB6.Agent32F418.ReturnBounds.Prefix

inductive QueuePath : Nat → Nat → Int → List Nat → Nat → Nat → Prop where
  | seed : QueuePath 268311341 29 268311341 [] 0 0
  | step {b : Prefix} {Q W : Nat} {x : Int} {hs : List Nat} {t P : Nat} :
      QueuePath (b.value Q) W x hs t P →
      QueuePath (b.next Q W) (W+b.E+1) (updateOffset b x hs)
        (updateQueue b W hs) (t+1) (max P b.p)

theorem queuePath_normal {N W : Nat} {x : Int} {hs : List Nat} {t P : Nat}
    (h : QueuePath N W x hs t P) : NormalPath N W := by
  induction h with
  | seed => exact NormalPath.seed
  | step _ ih => exact NormalPath.step ih

theorem normalPath_queue {N W : Nat} (h : NormalPath N W) :
    ∃ x hs t P, QueuePath N W x hs t P := by
  induction h with
  | seed => exact ⟨_,_,_,_,QueuePath.seed⟩
  | step _ ih =>
    obtain ⟨x,hs,t,P,h⟩ := ih
    exact ⟨_,_,_,_,QueuePath.step h⟩

theorem queuePath_sound {N W : Nat} {x : Int} {hs : List Nat} {t P : Nat}
    (h : QueuePath N W x hs t P) :
    (N:Int)=x+powerSum hs ∧ Spaced hs ∧ ∀ i ∈ hs, i<W := by
  induction h with
  | seed => simp [powerSum,Spaced]
  | @step b Q W x hs t P h ih =>
    obtain ⟨he,hsp,hw⟩ := ih
    exact ⟨queue_return_split (normalPath_safe (queuePath_normal h)).2 he,
      queue_spaced_update hsp hw⟩

theorem intPow_mono {a b : Nat} (h : a≤b) : (2:Int)^a ≤ (2:Int)^b := by
  have hc := Int.ofNat_le.mpr (pow_mono h)
  simpa [Int.natCast_pow] using hc

theorem intPow_pos (a : Nat) : 0<(2:Int)^a := Int.pow_pos (by decide)
theorem intPow_two {a : Nat} (ha : 1≤a) : 2≤(2:Int)^a := by
  simpa using intPow_mono ha

theorem C_ge_three (b : Prefix) : (3:Int)≤(b.C:Int) := by
  apply Int.ofNat_le.mpr
  have hp := Nat.two_pow_pos (b.E-2)
  exact Nat.le_trans (by simpa using Nat.mul_le_mul_left 3 hp) (correction_lower b)

theorem offset_upper_step {b : Prefix} {x : Int} {hs : List Nat} {t : Nat}
    (hsp : Spaced hs) (hx : x≤(2:Int)^(29-t)) :
    updateOffset b x hs ≤ (2:Int)^(29-(t+1))-3 := by
  let T : Int := (2:Int)^(29-(t+1))
  let D : Int := (2:Int)^b.L
  have hD : 2≤D := intPow_two (by simp [L])
  have hT : 0<T := intPow_pos _
  have hpow : (2:Int)^(29-t) ≤ 2*T := by
    dsimp [T]
    by_cases ht : t<29
    · rw [show 29-t=(29-(t+1))+1 by omega,Int.pow_succ]
      omega
    · simp [show 29-t=0 by omega,show 29-(t+1)=0 by omega]
  obtain ⟨_,hl⟩ := lowQueue_bounds hsp b.L
  change powerSum (lowQueue b.L hs)<D at hl
  have hmul := Int.mul_le_mul_of_nonneg_left hD (Int.le_of_lt hT)
  have hq : (x+powerSum (lowQueue b.L hs))/D<T+1 := by
    apply (Int.ediv_lt_iff_lt_mul (by omega : 0<D)).2
    rw [Int.add_mul,Int.one_mul]
    omega
  have hc := C_ge_three b
  unfold updateOffset
  change (x+powerSum (lowQueue b.L hs))/D-(b.C:Int)≤T-3
  omega

theorem offset_lower_step {b : Prefix} {x : Int} {hs : List Nat} {P : Nat}
    (hsp : Spaced hs) (hx : -(2:Int)^(7*P+3)<x) :
    -(2:Int)^(7*max P b.p+3)<updateOffset b x hs := by
  let M : Int := (2:Int)^(7*max P b.p+2)
  let D : Int := (2:Int)^b.L
  have hD : 2≤D := intPow_two (by simp [L])
  have hM : 0<M := intPow_pos _
  have hpow : (2:Int)^(7*max P b.p+3)=2*M := by
    dsimp [M]
    rw [show 7*max P b.p+3=(7*max P b.p+2)+1 by omega,Int.pow_succ]
    omega
  have hle := intPow_mono (a:=7*P+3) (b:=7*max P b.p+3)
    (by have := Nat.le_max_left P b.p; omega)
  have hc : (b.C:Int)<M := by
    have h := correction_upper b
    have h' := Nat.lt_of_lt_of_le h (pow_mono (b:=7*max P b.p+2) (by
      simp [E]; have := Nat.le_max_right P b.p; omega))
    simpa [M,Int.natCast_pow] using Int.ofNat_lt.mpr h'
  obtain ⟨hl,_⟩ := lowQueue_bounds hsp b.L
  have hmul := Int.mul_le_mul_of_nonneg_left hD (Int.le_of_lt hM)
  have hq : -M≤(x+powerSum (lowQueue b.L hs))/D := by
    apply (Int.le_ediv_iff_mul_le (by omega : 0<D)).2
    rw [Int.neg_mul]
    omega
  rw [hpow]
  unfold updateOffset
  change -2*M<(x+powerSum (lowQueue b.L hs))/D-(b.C:Int)
  omega

theorem queuePath_offset_bounds {N W : Nat} {x : Int} {hs : List Nat} {t P : Nat}
    (h : QueuePath N W x hs t P) :
    -(2:Int)^(7*P+3)<x ∧ x≤(2:Int)^(29-t) := by
  induction h with
  | seed => decide
  | @step b Q W x hs t P h ih =>
    have hs' := (queuePath_sound h).2.1
    exact ⟨offset_lower_step hs' ih.1,by have := offset_upper_step (b:=b) hs' ih.2; omega⟩

theorem queuePath_negative {N W : Nat} {x : Int} {hs : List Nat} {t P : Nat}
    (h : QueuePath N W x hs t P) (ht : 29≤t) : x<0 := by
  cases h with
  | seed => omega
  | @step b Q W x hs t P h =>
    have hu := offset_upper_step (b:=b) (queuePath_sound h).2.1 (queuePath_offset_bounds h).2
    simp [show 29-(t+1)=0 by omega] at hu
    omega

theorem high_even_source_exclusion {N W : Nat} {x : Int} {hs : List Nat} {t P : Nat}
    (h : QueuePath N W x hs t P) (ht : 29≤t) (hn : NoEven N) {i : Nat}
    (hi : i%2=0) (hh : 7*P+5≤i) : i∉hs := by
  intro hm
  obtain ⟨he,hsp,_⟩ := queuePath_sound h
  have hx := queuePath_negative h ht
  have hlo := (queuePath_offset_bounds h).1
  let c : Nat := (-x).toNat
  have hc : (c:Int) = -x := Int.toNat_of_nonneg (by omega)
  have hcs : c≤nPowerSum hs := by
    apply Int.ofNat_le.mp
    rw [hc,←powerSum_cast]
    have := Int.natCast_nonneg N
    omega
  have hN : N=nPowerSum hs-c := by
    apply Int.ofNat_inj.mp
    rw [Int.natCast_sub hcs,hc,←powerSum_cast]
    omega
  have hpow : c<2^(i-2) := by
    apply Int.ofNat_lt.mp
    rw [hc,Int.natCast_pow]
    change -x<(2:Int)^(i-2)
    have hp := intPow_mono (a:=7*P+3) (b:=i-2) (by omega)
    omega
  have hn' : NoEven (nPowerSum hs-c) := hN ▸ hn
  have hb := sub_high_even hcs hpow (show (i-2)%2=0 by omega) hn'
  rw [show i-2+2=i by omega,nPowerSum_bits (spaced_strict hsp)] at hb
  simp [hm] at hb

#print axioms queuePath_sound
#print axioms queuePath_offset_bounds
#print axioms queuePath_negative
#print axioms high_even_source_exclusion

end BB6.Agent32F418.ReturnBounds.Prefix
