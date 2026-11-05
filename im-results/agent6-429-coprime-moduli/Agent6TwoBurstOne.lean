import BB429Rank
import BB429Burst
import BB429DyadicStarts
import Lean.Elab.Tactic.Omega

namespace Agent6TwoBurstOne
set_option maxHeartbeats 10000000

def depth (q : Nat) : Nat := 4*q+5
def power (q : Nat) : Nat := 2^(depth q)
def demand (q : Nat) : Nat := 12*power q-(24*q+53)
def firstU (q : Nat) : Nat := 3*power q-3
def firstW (q : Nat) : Nat := 6*power q-(12*q+32)
def secondDemand (q : Nat) : Nat := 12*power q-(12*q+28)

private theorem power_bound (q : Nat) : 4*q+32 ≤ power q := by
  induction q with
  | zero => decide
  | succ q ih =>
    have hp : power (q+1)=16*power q := by
      simp only [power, depth]
      have he : 4*(q+1)+5 = (4*q+5)+4 := by omega
      rw [he, Nat.pow_add]
      simp only [show (2:Nat)^4=16 by decide]
      omega
    rw [hp]
    omega

private theorem branch_arith (q : Nat) :
  24*q+53 ≤ 12*power q ∧
  12*q+32 ≤ 6*power q ∧
  12*q+28 ≤ 12*power q ∧
  3 ≤ 3*power q := by
  have h := power_bound q
  omega

private theorem first_formula (q : Nat) :
  2*firstU q + firstW q = demand q+3*depth q ∧
  firstU q+3=3*power q ∧
  6*power q = firstW q + 12*q+32 ∧
  12*power q = demand q+24*q+53 ∧
  12*power q = secondDemand q+12*q+28 := by
  obtain ⟨h1,h2,h3,h4⟩ := branch_arith q
  simp only [firstU, firstW, demand, secondDemand, depth]
  omega

private theorem first_success (q : Nat) :
  BB429Burst.firstRun (depth q) (0,demand q) = some (firstU q,firstW q) := by
  have hpow : power q=2*2^(4*q+4) := by
    simp only [power, depth]
    have he : 4*q+5=(4*q+4)+1 := by omega
    rw [he, Nat.pow_succ]
    omega
  have ha : 6*power q ≤ demand q+3*(4*q+4)+9 := by
    have h := first_formula q
    have hb := power_bound q
    omega
  have hg : 4*((0+3)*2^(4*q+4)) ≤ 2*0+demand q+3*(4*q+4)+9 := by
    omega
  obtain ⟨a,b,hfirst⟩ := (BB429Burst.prefix_exists_iff 0 (demand q) (4*q+4)).mpr hg
  have hform := BB429Burst.prefix_formula 0 (demand q) (depth q) a b (by
    simpa [depth] using hfirst)
  have h := first_formula q
  have hp := power_bound q
  have ha' : a=firstU q := by
    have hpa : (0+3)*2^(depth q)=3*power q := by simp [power]
    omega
  have hb' : b=firstW q := by omega
  simpa [ha',hb',depth] using hfirst

private theorem reset_success (q : Nat) :
  BB429.next (firstU q,firstW q)=some (0,secondDemand q) := by
  have hh := first_formula q
  have hb := branch_arith q
  have hpow := power_bound q
  have hU : firstU q=3*power q-3 := rfl
  have hW : firstW q=6*power q-(12*q+32) := rfl
  have hwlt : firstW q < 2*firstU q := by omega
  have heven : firstW q%2=0 := by omega
  have hd : firstU q-firstW q/2=6*q+13 := by omega
  have hodd : (firstU q-firstW q/2)%2≠0 := by omega
  have hnon1 : firstU q-firstW q/2≠1 := by omega
  have hout : 2*firstU q+firstW q+10=secondDemand q := by omega
  simp [BB429.next,show ¬ (firstW q≥2*firstU q+3) by omega,
      show firstW q≠2*firstU q+2 by omega,
      show firstW q≠2*firstU q+1 by omega,
      show firstW q≠2*firstU q by omega,
      heven,hnon1,hodd,hout]

private theorem second_gateway (q : Nat) :
  ∃ n a b, BB429.run n (0,secondDemand q)=some (a,b) ∧
    BB429.next (a,b)=none := by
  have h := first_formula q
  have hgate : 2*0+secondDemand q+3*depth q+13 = 4*((0+3)*2^(depth q)) := by
    have hp : power q = 2^(depth q) := rfl
    omega
  obtain ⟨n,a,b,hr,hline⟩ :=
    (BB429Burst.burst_gateway_iff 0 (secondDemand q)).mpr ⟨depth q,hgate⟩
  exact ⟨n,a,b,BB429DyadicStarts.first_prefix_is_source _ _ n hr,
    (BB429.next_none_iff_halt_line a b).mpr hline⟩

/-- Entire all-parameter (w ≡ 1 mod 3) two-burst family halts synthetically
under the authentic 12-branch accelerated map. -/
theorem full_source_synthetic_halt (q : Nat) :
  ∃ n a b, BB429.run n (0,demand q)=some (a,b) ∧
    BB429.next (a,b)=none := by
  obtain ⟨k,a,b,hsecond,hhalt⟩ := second_gateway q
  have hfirst : BB429.run (depth q) (0,demand q) =
      some (firstU q, firstW q) :=
    BB429DyadicStarts.first_prefix_is_source _ _ _ (first_success q)
  have hreset := reset_success q
  refine ⟨depth q+1+k,a,b,?_,hhalt⟩
  rw [show depth q+1+k = (depth q+1)+k by omega, BB429.run_add]
  have hmid : BB429.run (depth q+1) (0,demand q)=some (0,secondDemand q) := by
    change (BB429.run (depth q) (0,demand q)).bind BB429.next = _
    simp [hfirst,hreset]
  simp [hmid,hsecond]

#print axioms full_source_synthetic_halt
end Agent6TwoBurstOne
