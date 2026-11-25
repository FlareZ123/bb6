import ShadowBits

namespace BB6.Agent19ShadowBits
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

def sourceS (a b : Nat) : Int := -(a:Int)-2*(b:Int)
def sourceZ (a b : Nat) : Int := (-(a:Int)-2-sourceS a b%2)/2

private theorem sourceZ_twice (a b : Nat) :
    2*sourceZ a b=-(a:Int)-2-sourceS a b%2 := by
  unfold sourceZ sourceS
  omega

theorem source_lift_signed (m x u v a b n : Nat)
    (hm : u+2*v=5+211*m)
    (hu : u=2*x+211*(2+(m+1)%2))
    (ha : 2^(n+1)∣211*a+u)
    (hb : 2^(n+1)∣211*b+v) :
    ∃ k l : Int,
      211*sourceS a b=5+211*(m:Int)+P (n+1)*k ∧
      211*sourceZ a b=(x:Int)+P n*l := by
  obtain ⟨A,hA⟩ := ha
  obtain ⟨B,hB⟩ := hb
  have hAi : 211*(a:Int)+(u:Int)=P (n+1)*(A:Int) := by
    have h := congrArg (fun t : Nat => (t:Int)) hA
    simp only [Int.natCast_add,Int.natCast_mul,Int.natCast_pow] at h
    exact h
  have hBi : 211*(b:Int)+(v:Int)=P (n+1)*(B:Int) := by
    have h := congrArg (fun t : Nat => (t:Int)) hB
    simp only [Int.natCast_add,Int.natCast_mul,Int.natCast_pow] at h
    exact h
  have hmi : (u:Int)+2*(v:Int)=5+211*(m:Int) := by
    have h := congrArg (fun t : Nat => (t:Int)) hm
    simp only [Int.natCast_add,Int.natCast_mul] at h
    exact h
  have hui : (u:Int)=2*(x:Int)+211*(2+((m+1)%2:Nat)) := by
    have h := congrArg (fun t : Nat => (t:Int)) hu
    simp only [Int.natCast_add,Int.natCast_mul] at h
    exact h
  clear hA hB hm hu
  let k : Int := -(A:Int)-2*(B:Int)
  have hS : 211*sourceS a b=5+211*(m:Int)+P (n+1)*k := by
    unfold sourceS
    dsimp [k]
    rw [Int.mul_sub,Int.mul_neg,Int.mul_left_comm 211 2,Int.mul_sub,Int.mul_neg,
      Int.mul_left_comm (P (n+1)) 2]
    clear hui
    omega
  refine ⟨k,-(A:Int),hS,?_⟩
  have hpow : P (n+1)=2*P n := by unfold P; rw [Int.pow_succ,Int.mul_comm]
  have hpar : sourceS a b%2=((m+1)%2:Nat) := by
    rw [hpow,Int.mul_assoc] at hS
    clear hAi hBi hmi hui hpow
    omega
  have hz' : 2*(211*sourceZ a b)=211*(-(a:Int)-2-sourceS a b%2) := by
    rw [Int.mul_left_comm 2 211,sourceZ_twice]
  rw [hpar,Int.mul_sub,Int.mul_sub,Int.mul_neg] at hz'
  rw [hpow,Int.mul_assoc] at hAi
  rw [Int.mul_neg]
  clear hS hpar hBi hmi hpow
  omega

theorem source_frontier_nonempty (m x u v a b n : Nat)
    (hm : u+2*v=5+211*m)
    (hu : u=2*x+211*(2+(m+1)%2))
    (ha : 2^(n+1)∣211*a+u)
    (hb : 2^(n+1)∣211*b+v)
    (ho : SignedOpen (sourceS a b) (sourceZ a b) n) :
    ∃ v, v∈frontier m x n := by
  obtain ⟨k,l,hs,hz⟩ := source_lift_signed m x u v a b n hm hu ha hb
  exact signed_open_frontier m x n _ _ k l hs hz ho

#print axioms source_lift_signed
#print axioms source_frontier_nonempty

end BB6.Agent19ShadowBits
