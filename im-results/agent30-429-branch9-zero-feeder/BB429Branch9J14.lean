import BB429Branch9Cover

namespace BB429Branch9J14
open BB429NewResidue BB429DyadicTransport BB429DyadicSource BB429Branch9Clip BB429Branch9Cover

set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- N=8*2^14+14-11. There are 32768 exceptional indices, of
    which 32752 are covered by the low-bit trie. -/
theorem interior : cover 14 131075 30 32752 15 0 0=true := by decide +kernel

theorem tail : ∀ k : Fin 16,
    search basicTest 30 (clipA 14 131075 30 (32752+k.val))
      (clipB 14 131075 30 (32752+k.val))=false := by decide +kernel

private theorem high_bound : 36*2^30+6*2^14+8+3*131075≤12*2^131075 := by
  have hp : (2:Nat)^40≤2^131075 := Nat.pow_le_pow_right (by decide) (by decide)
  omega

theorem sideRejected (k x y : Nat) (hk : 4*k+3<131075)
    (hx : x+6*2^14+8+3*k=12*2^131075+6*2^(131075-(4*k+3)))
    (hy : y+12*2^14+12*2^(131075-(4*k+3))+6*k=24*2^131075+5) : ¬Reach x y := by
  by_cases h : k<32752
  · apply cover_sound 14 131075 30 32752 (by decide) high_bound 15 0 0 k k x y
      (by decide) (by decide) (by decide) h (by simp) hx hy interior
  · have hf : k-32752<16 := by omega
    have hc := tail ⟨k-32752,hf⟩
    have he : 32752+(k-32752)=k := by omega
    change search basicTest 30 (clipA 14 131075 30 (32752+(k-32752)))
      (clipB 14 131075 30 (32752+(k-32752)))=false at hc
    rw [he] at hc
    exact reject_side_clip 14 131075 30 k x y (by decide) (by have hh:=high_bound; omega) hx hy hc

private theorem feeder_aux (N z : Nat) (hN : 40≤N)
    (hz : z+786441=48*2^N+3) : ¬Reach 0 z := by
  have hp : (2:Nat)^40≤2^N := Nat.pow_le_pow_right (by decide) hN
  have hzmod : z%4=2 := by omega
  have hpI : (2:Int)^40≤2^N := by exact_mod_cast hp
  apply no_zero_two N 1 z (-196614) (by omega) (by omega) hzmod ?_ (by omega) (by decide) (by decide)
  have hzI : (z:Int)+786441=48*2^N+3 := by
    have h := congrArg (fun x : Nat => (x:Int)) hz
    simpa only [Int.natCast_add,Int.natCast_mul,Int.natCast_pow,show ((786441:Nat):Int)=786441 by decide,show ((48:Nat):Int)=48 by decide,show ((2:Nat):Int)=2 by decide,show ((3:Nat):Int)=3 by decide] using h
  omega

theorem zeroRejected (z : Nat)
    (hz : z+24*2^14+3*131075=48*2^131075+3) : ¬Reach 0 z :=
  feeder_aux 131075 z (by decide) (by simpa only [show (24*2^14+3*131075:Nat)=786441 by decide, Nat.add_assoc] using hz)

theorem no_diagonal_J14 (a b : Nat)
    (ha : a+3=12*2^131075)
    (hb : b+24*2^131075+24*2^14=48*2^131075+15) : ¬Reach a b := by
  apply no_diagonal_of_side 14 131075 sideRejected zeroRejected 131075 a b (by decide) ha
  simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero] using hb

#print axioms interior
#print axioms tail
#print axioms sideRejected
#print axioms zeroRejected
#print axioms no_diagonal_J14
end BB429Branch9J14
