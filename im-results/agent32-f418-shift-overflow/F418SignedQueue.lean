import F418NormalPath

namespace BB6.Agent32F418.ReturnBounds.Prefix

/-- The prefix fixes the low L bits and leaves the high register arbitrary. -/
theorem value_affine (b : Prefix) (Q : Nat) :
    b.value Q=2^b.L*Q+b.value 0 := by
  induction b with
  | last r =>
    simp only [value,L_last,Nat.mul_zero,Nat.zero_add,Nat.mul_one,Nat.pow_succ]
    rw [Nat.mul_add,Nat.mul_one,←Nat.mul_assoc]
  | more r t ih =>
    simp only [value,L_more]
    rw [ih,Nat.mul_add 2,Nat.add_assoc,Nat.mul_add]
    have h : 2^(2*r+2+t.L)=2^(2*r+1)*2*2^t.L := by
      rw [show 2*r+2+t.L=(2*r+1)+1+t.L by omega,Nat.pow_add,Nat.pow_succ]
    rw [h]
    ac_rfl

/-- Signed offset plus deferred positive high powers. -/
def powerSum (hs : List Nat) : Int := (hs.map fun h => (2:Int)^h).sum

def shiftQueue (L : Nat) (hs : List Nat) := hs.map (· - L)

theorem powerSum_shift (L : Nat) (hs : List Nat) (h : ∀ i ∈ hs, L≤i) :
    powerSum hs = (2:Int)^L*powerSum (shiftQueue L hs) := by
  induction hs with
  | nil => simp [powerSum,shiftQueue]
  | cons i is ih =>
    have hi := h i (by simp)
    have his : ∀ j ∈ is, L≤j := by intro j hj; exact h j (by simp [hj])
    simp only [powerSum,shiftQueue,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih his,Int.mul_add,←Int.pow_add,show L+(i-L)=i by omega]

theorem powerSum_append (as bs : List Nat) :
    powerSum (as++bs)=powerSum as+powerSum bs := by
  simp [powerSum]

/-- A known signed prefix plus a queue strictly above it yields the
    exact natural-register prefix and tail. No sign condition on x. -/
theorem prefix_from_signed {b : Prefix} {x q : Int} {hs : List Nat} {N : Nat}
    (hx : x=(2:Int)^b.L*q+(b.value 0:Int))
    (hN : (N:Int)=x+powerSum hs)
    (hh : ∀ i ∈ hs, b.L≤i) :
    ∃ Q : Nat, N=b.value Q ∧ (Q:Int)=q+powerSum (shiftQueue b.L hs) := by
  let q' := q+powerSum (shiftQueue b.L hs)
  have hp : 0 < (2:Int)^b.L := Int.pow_pos (by decide)
  have hlow : (b.value 0:Int)<(2:Int)^b.L := by
    have he : ((2^b.L:Nat):Int)=(2:Int)^b.L := by simp [Int.natCast_pow]
    rw [←he]
    exact Int.ofNat_lt.mpr (by simpa using (value_bounds b 0).2)
  have hsum := powerSum_shift b.L hs hh
  have hN' : (N:Int)=(2:Int)^b.L*q'+(b.value 0:Int) := by
    rw [hN,hx,hsum]
    dsimp [q']
    rw [Int.mul_add]
    ac_rfl
  have hq' : 0≤q' := by
    by_cases hq : 0≤q'
    · exact hq
    · have hneg : q'≤-1 := by omega
      have hprod := Int.mul_le_mul_of_nonneg_left hneg (Int.le_of_lt hp)
      have hn := Int.natCast_nonneg N
      omega
  refine ⟨q'.toNat,?_,Int.toNat_of_nonneg hq'⟩
  apply Int.ofNat_inj.mp
  rw [value_affine,Int.natCast_add,Int.natCast_mul,Int.natCast_pow,Int.toNat_of_nonneg hq']
  exact hN'

/-- Lazy update of the signed offset and high source queue is exactly
    the full-register normal return. -/
theorem queue_return {b : Prefix} {Q W : Nat} {x : Int} {hs : List Nat}
    (hwidth : b.value Q<2^W)
    (hN : (b.value Q:Int)=x+powerSum hs)
    (hh : ∀ i ∈ hs, b.L≤i) :
    (b.next Q W:Int) =
      x/(2:Int)^b.L-(b.C:Int)+powerSum (shiftQueue b.L hs++[W+b.E]) := by
  have hp : (2:Int)^b.L≠0 := Int.pow_ne_zero (by decide)
  have hq : (Q:Int)=x/(2:Int)^b.L+powerSum (shiftQueue b.L hs) := by
    have h := congrArg (fun z : Int => z/(2:Int)^b.L) hN
    have he : ((2^b.L:Nat):Int)=(2:Int)^b.L := by simp [Int.natCast_pow]
    rw [←he,←Int.natCast_ediv,value_div_length,he] at h
    rw [powerSum_shift b.L hs hh,Int.add_mul_ediv_left _ _ hp] at h
    exact h
  have hL := (width_tail hwidth).1
  have hc : b.C < 2^(W+b.E) :=
    Nat.lt_of_lt_of_le (correction_upper b) (pow_mono (by simp [L] at hL; omega))
  rw [next,Int.natCast_sub (by omega),Int.natCast_add,Int.natCast_pow,hq,
    powerSum_append]
  simp [powerSum]
  omega

#print axioms value_affine
#print axioms prefix_from_signed
#print axioms queue_return

end BB6.Agent32F418.ReturnBounds.Prefix
