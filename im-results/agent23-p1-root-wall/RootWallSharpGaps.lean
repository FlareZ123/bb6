import RootWallSharpArithmetic

namespace BB6.Agent23RootWall

private theorem half_pow (n:Nat) (hn:1≤n) :
    2^n=2*2^(n-1) := by
  have he:n=(n-1)+1:=by omega
  calc
    2^n=2^((n-1)+1):=by congr 1
    _=2*2^(n-1):=by rw [Nat.pow_succ]; omega

/-- Low inverse cost below the exact sharp budget excludes any
    14-power reset seed on the affine wall, for all n>=14. -/
theorem sharp_no_low_wall_reset_power (n m r z:Nat)
    (hn:14≤n) (hbudget:6*m+14*n+10<14*2^n)
    (hbalance:r+4*n+2*m+16=14*2^n)
    (hpower:r+8=14*2^z) : False := by
  have hhalf:=half_pow n (by omega)
  have hg:=exp_growth n (by omega)
  have hlo:7*2^n<r+8:=by omega
  have hhi:r+8<14*2^n:=by omega
  by_cases hzlt:z<n
  · have hle:z≤n-1:=by omega
    have hp:2^z≤2^(n-1):=Nat.pow_le_pow_right (by decide) hle
    omega
  · have hge:n≤z:=by omega
    have hp:2^n≤2^z:=Nat.pow_le_pow_right (by decide) hge
    omega

/-- The same bound excludes every reachable eight-multiple right-three
    feeder via the authenticated six-times-counter power normal form. -/
theorem sharp_no_low_wall_eight_three_power (n m u z:Nat)
    (hn:14≤n) (hbudget:6*m+14*n+10<14*2^n)
    (hbalance:8*u+4*n+2*m+22=14*2^n)
    (hpower:6*u+8=14*2^z) : False := by
  have hhalf:=half_pow n (by omega)
  have hlo:7*2^n<6*u+8:=by omega
  have hhi:6*u+8<14*2^n:=by omega
  by_cases hzlt:z<n
  · have hle:z≤n-1:=by omega
    have hp:2^z≤2^(n-1):=Nat.pow_le_pow_right (by decide) hle
    omega
  · have hge:n≤z:=by omega
    have hp:2^n≤2^z:=Nat.pow_le_pow_right (by decide) hge
    omega

#print axioms sharp_no_low_wall_reset_power
#print axioms sharp_no_low_wall_eight_three_power
end BB6.Agent23RootWall
