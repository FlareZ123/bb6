import OddRayForced
set_option maxHeartbeats 0
namespace CascadeOddRay

/-- Exact closed deficit identity for all n>=1, all symbolic depths. -/
theorem deficit_closed (n j:Nat) (hn:1≤n):
    deficit n j+(n-1)=2^j*(2*n+3):=by
  induction j with
  | zero=>simp [deficit];omega
  | succ j ih=>
    calc
      deficit n (j+1)+(n-1)=2*(deficit n j+(n-1)):=by
        simp only [deficit]
        omega
      _ =2*(2^j*(2*n+3)):=by rw [ih]
      _ =2^(j+1)*(2*n+3):=by rw [Nat.pow_succ];ac_rfl

private theorem large_pow (j:Nat):8*j+51≤2^(3*j+24):=by
  induction j with
  | zero=>decide
  | succ j ih=>
    have he:3*(j+1)+24=(3*j+24)+3:=by omega
    rw [he,Nat.pow_add]
    have h8:(2:Nat)^3=8:=by decide
    rw [h8]
    omega

/-- All symbolic depths j admit an explicit large index n=4j+24
    whose jth ray target lies in the same high dyadic even-image band. -/
theorem deep_margin (j:Nat):
    deficit (4*j+24) j≤2^(4*j+24)+1:=by
  let n:=4*j+24
  have hn:1≤n:=by dsimp[n];omega
  have hlin:2*n+3≤2^(3*j+24):=by
    have hh:=large_pow j
    dsimp[n]
    omega
  have hclosed:=deficit_closed n j hn
  have hbound:deficit n j≤2^j*(2*n+3):=by omega
  have hmul:2^j*(2*n+3)≤2^j*2^(3*j+24):=
    Nat.mul_le_mul_left (2^j) hlin
  have hp:2^j*2^(3*j+24)=2^n:=by
    rw [←Nat.pow_add]
    congr 1
    dsimp[n]
    omega
  dsimp[n] at *
  omega

/-- Arbitrarily deep odd ray positions with true blank-root source-C
    reachability equivalence exist, using j=2J+1 and n=4j+24. -/
theorem unbounded_odd_ray_root_iff (J:Nat):
    ∃n j:Nat, J<j ∧ j%2=1 ∧
       (CascadeSweep.ReachC (2,0) (ray n j,0) ↔
        CascadeSweep.ReachC (2,0) (ray n (j+1),0)):=by
  let j:=2*J+1
  let n:=4*j+24
  have hn:4≤n:=by dsimp[n];omega
  have hj:j%2=1:=by dsimp[j];omega
  have hm:deficit n j≤2^n+1:=by
    simpa only [n] using deep_margin j
  exact ⟨n,j,(by dsimp[j];omega),hj,odd_ray_root_iff n j hn hj hm⟩

#print axioms deficit_closed
#print axioms deep_margin
#print axioms unbounded_odd_ray_root_iff
end CascadeOddRay
