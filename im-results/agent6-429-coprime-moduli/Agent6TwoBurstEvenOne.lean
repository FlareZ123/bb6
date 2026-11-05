import BB429Rank
import BB429Burst
import BB429DyadicStarts
import Lean.Elab.Tactic.Omega

namespace Agent6TwoBurstEvenOne
set_option maxHeartbeats 10000000

def k (q : Nat) : Nat := 4*q+5
def depth (q : Nat) : Nat := k q+3
def power (q : Nat) : Nat := 2^(k q)
def demand (q : Nat) : Nat := 56*power q - (6*k q+42)
def firstU (q : Nat) : Nat := 24*power q-3
def firstW (q : Nat) : Nat := 8*power q-(3*k q+27)
def secondW (q : Nat) : Nat := 56*power q-(3*k q+35)

private theorem pow_bound (q : Nat) : 3*k q+35 ≤ 8*power q := by
  induction q with
  | zero => decide
  | succ q ih =>
      have hp : power (q+1)=16*power q := by
        simp only [power,k]
        have he : 4*(q+1)+5=(4*q+5)+4 := by omega
        rw [he,Nat.pow_add]
        simp only [show (2:Nat)^4=16 by decide]
        omega
      have hk : k (q+1)=k q+4 := by simp [k]; omega
      rw [hp,hk]
      omega

private theorem arithmetic (q : Nat) :
  6*k q+42 ≤ 56*power q ∧
  3*k q+27 ≤ 8*power q ∧
  3*k q+35 ≤ 56*power q ∧
  firstU q+3 = 24*power q ∧
  firstW q +3*k q+27 = 8*power q ∧
  demand q+6*k q+42=56*power q ∧
  secondW q+3*k q+35=56*power q ∧
  2*firstU q+firstW q = demand q+3*depth q ∧
  2*firstU q+firstW q-2=secondW q := by
  have h := pow_bound q
  have hp : 0<power q := Nat.pow_pos (by omega)
  simp only [demand,firstU,firstW,secondW,depth]
  omega

private theorem first_success (q : Nat) :
  BB429Burst.firstRun (depth q) (0,demand q)=some (firstU q,firstW q) := by
  have he : depth q=(depth q-1)+1 := by simp only [depth,k]; omega
  have hpower : 2^(depth q-1)=4*power q := by
    have hx : depth q-1=k q+2 := by simp [depth,k]
    rw [hx, Nat.pow_add]
    simp only [show (2:Nat)^2=4 by decide, power]
    omega
  have hbound : 4*((0+3)*2^(depth q-1)) ≤ 2*0+demand q+3*(depth q-1)+9 := by
    have h := pow_bound q
    have h2 := arithmetic q
    have hd : depth q-1=k q+2 := by simp [depth,k]
    omega
  obtain ⟨a,b,hfirst⟩ :=
    (BB429Burst.prefix_exists_iff 0 (demand q) (depth q-1)).mpr hbound
  have hf : BB429Burst.firstRun (depth q) (0,demand q)=some (a,b) := by
    rw [he]
    exact hfirst
  obtain ⟨ha,hb⟩ := BB429Burst.prefix_formula 0 (demand q) (depth q) a b hf
  have hp : 2^(depth q)=8*power q := by
    simp only [depth]
    rw [Nat.pow_add]
    simp only [show (2:Nat)^3=8 by decide, power]
    omega
  have h := arithmetic q
  have ha' : a=firstU q := by omega
  have hb' : b=firstW q := by omega
  simpa [ha',hb'] using hf

private theorem even_reset (q : Nat) :
  BB429.next (firstU q,firstW q)=some (11,secondW q) := by
  have h := arithmetic q
  have hb := pow_bound q
  have hU : firstU q=24*power q-3 := rfl
  have hW : firstW q=8*power q-(3*k q+27) := rfl
  have hwlt : firstW q<2*firstU q := by omega
  have heven : firstW q%2=0 := by
    have hk : k q=4*q+5 := rfl
    omega
  have hd : firstU q-firstW q/2=20*power q+6*q+18 := by
    have hk : k q=4*q+5 := rfl
    omega
  have hdne : firstU q-firstW q/2≠1 := by omega
  have hde : (firstU q-firstW q/2)%2=0 := by omega
  have hout : 2*firstU q+firstW q-2=secondW q := h.2.2.2.2.2.2.2.2
  simp [BB429.next,show ¬ (firstW q≥2*firstU q+3) by omega,
    show firstW q≠2*firstU q+2 by omega,
    show firstW q≠2*firstU q+1 by omega,
    show firstW q≠2*firstU q by omega,
    heven,hdne,hde,hout]

private theorem second_gateway (q : Nat) :
  ∃ n a b, BB429.run n (11,secondW q)=some (a,b) ∧
    BB429.next (a,b)=none := by
  have h := arithmetic q
  have hgate : 2*11+secondW q+3*k q+13 = 4*((11+3)*2^(k q)) := by
    have hp : power q=2^(k q) := rfl
    omega
  obtain ⟨n,a,b,hr,hline⟩ :=
    (BB429Burst.burst_gateway_iff 11 (secondW q)).mpr ⟨k q,hgate⟩
  exact ⟨n,a,b,BB429DyadicStarts.first_prefix_is_source _ _ _ hr,
    (BB429.next_none_iff_halt_line a b).mpr hline⟩

/-- Genuine full-map two-burst synthetic halts for the even 1 mod 3 class. -/
theorem full_source_synthetic_halt (q : Nat) :
  ∃ n a b, BB429.run n (0,demand q)=some (a,b) ∧
    BB429.next (a,b)=none := by
  obtain ⟨j,a,b,hr,hh⟩ := second_gateway q
  have h1 : BB429.run (depth q) (0,demand q)=some (firstU q,firstW q) :=
    BB429DyadicStarts.first_prefix_is_source _ _ _ (first_success q)
  have h2 := even_reset q
  refine ⟨depth q+1+j,a,b,?_,hh⟩
  rw [show depth q+1+j=(depth q+1)+j by omega,BB429.run_add]
  have hm : BB429.run (depth q+1) (0,demand q)=some (11,secondW q) := by
    change (BB429.run (depth q) (0,demand q)).bind BB429.next = _
    simp [h1,h2]
  simp [hm,hr]

#print axioms full_source_synthetic_halt
end Agent6TwoBurstEvenOne
