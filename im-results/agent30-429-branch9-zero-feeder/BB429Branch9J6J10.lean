import BB429Branch9Clip

namespace BB429Branch9J6J10
open BB429NewResidue BB429DyadicTransport BB429DyadicSource BB429Branch9Clip
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- Every exceptional index, including the short-power tail. -/
theorem side6 : ∀ k : Fin 126,
    search basicTest 12 (clipA 6 507 12 k.val) (clipB 6 507 12 k.val)=false := by decide +kernel

theorem side10 : ∀ k : Fin 2047,
    search basicTest 20 (clipA 10 8191 20 k.val) (clipB 10 8191 20 k.val)=false := by decide +kernel

theorem zero6U : search basicTest 9 (-768) (-1534)=false := by decide +kernel
theorem zero6O : search basicTest 9 (-764) (-1531)=false := by decide +kernel
theorem zero10U : search basicTest 13 (-12291) (-24580)=false := by decide +kernel
theorem zero10O : search basicTest 13 (-12287) (-24577)=false := by decide +kernel

private theorem zero6 (z : Nat)
    (hz : z+24*2^6+3*507=48*2^507+3) : ¬Reach 0 z := by
  have hp : (2:Nat)^40≤2^507 := Nat.pow_le_pow_right (by decide) (by decide)
  have hpI : (2:Int)^40≤2^507 := by exact_mod_cast hp
  have hzI : (z:Int)+24*2^6+3*507=48*2^507+3 := by exact_mod_cast hz
  apply no_zero_two 507 9 z (-768) (by decide) (by omega) (by omega) (by omega) (by omega)
  · exact zero6U
  · exact zero6O

private theorem zero10 (z : Nat)
    (hz : z+24*2^10+3*8191=48*2^8191+3) : ¬Reach 0 z := by
  have hp : (2:Nat)^40≤2^8191 := Nat.pow_le_pow_right (by decide) (by decide)
  have hpI : (2:Int)^40≤2^8191 := by exact_mod_cast hp
  have hzI : (z:Int)+24*2^10+3*8191=48*2^8191+3 := by exact_mod_cast hz
  apply no_zero_two 8191 13 z (-12291) (by decide) (by omega) (by omega) (by omega) (by omega)
  · exact zero10U
  · exact zero10O

/-- Complete exclusion of the J=6 last-reset diagonal target. -/
theorem no_diagonal_J6 (a b : Nat)
    (ha : a+3=12*2^507)
    (hb : b+24*2^507+24*2^6=48*2^507+15) : ¬Reach a b := by
  have hp : (2:Nat)^40≤2^507 := Nat.pow_le_pow_right (by decide) (by decide)
  refine no_diagonal_of_clip 6 507 12 (by decide) (by omega) ?_ zero6 507 a b (by decide) ha ?_
  · intro k hk
    exact side6 ⟨k,by omega⟩
  · simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero] using hb

/-- Complete exclusion of the J=10 last-reset diagonal target. -/
theorem no_diagonal_J10 (a b : Nat)
    (ha : a+3=12*2^8191)
    (hb : b+24*2^8191+24*2^10=48*2^8191+15) : ¬Reach a b := by
  have hp : (2:Nat)^40≤2^8191 := Nat.pow_le_pow_right (by decide) (by decide)
  refine no_diagonal_of_clip 10 8191 20 (by decide) (by omega) ?_ zero10 8191 a b (by decide) ha ?_
  · intro k hk
    exact side10 ⟨k,by omega⟩
  · simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero] using hb

#print axioms side6
#print axioms side10
#print axioms zero6U
#print axioms zero6O
#print axioms zero10U
#print axioms zero10O
#print axioms no_diagonal_J6
#print axioms no_diagonal_J10
end BB429Branch9J6J10
