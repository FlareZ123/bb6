import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 200000
set_option maxRecDepth 12000

namespace BB6.Agent15D0E

def directParent (p : Nat × Nat) : Nat × Nat :=
  (p.1+p.2-2,(p.2-2)/2)

def d0e0 (u : Nat) : Nat × Nat := (218624*u+14700,414976*u+27902)
def d0e1 (u : Nat) : Nat × Nat := (633600*u+42600,207488*u+13950)
def d0e2 (u : Nat) : Nat × Nat := (841088*u+56548,103744*u+6974)
def d0e3 (u : Nat) : Nat × Nat := (944832*u+63520,51872*u+3486)
def d0e4 (u : Nat) : Nat × Nat := (996704*u+67004,25936*u+1742)
def d0e5 (u : Nat) : Nat × Nat := (1022640*u+68744,12968*u+870)
def d0e6 (u : Nat) : Nat × Nat := (1035608*u+69612,6484*u+434)
def d0e7 (u : Nat) : Nat × Nat := (1042092*u+70044,3242*u+216)
def d0e8 (u : Nat) : Nat × Nat := (1045334*u+70258,1621*u+107)

theorem d0e_direct_chain (u : Nat) :
    directParent (d0e0 u)=d0e1 u ∧
    directParent (d0e1 u)=d0e2 u ∧
    directParent (d0e2 u)=d0e3 u ∧
    directParent (d0e3 u)=d0e4 u ∧
    directParent (d0e4 u)=d0e5 u ∧
    directParent (d0e5 u)=d0e6 u ∧
    directParent (d0e6 u)=d0e7 u ∧
    directParent (d0e7 u)=d0e8 u := by
  simp [directParent,d0e0,d0e1,d0e2,d0e3,d0e4,d0e5,d0e6,d0e7,d0e8]
  omega

private def evenEvenSumTwo (p : Nat × Nat) : Prop :=
  p.1%2=0 ∧ p.2%2=0 ∧ 6≤p.2 ∧ (p.1+p.2)%4=2

theorem d0e_intermediate_profile (t : Nat) :
    evenEvenSumTwo (d0e0 (1802+6720*t)) ∧
    evenEvenSumTwo (d0e1 (1802+6720*t)) ∧
    evenEvenSumTwo (d0e2 (1802+6720*t)) ∧
    evenEvenSumTwo (d0e3 (1802+6720*t)) ∧
    evenEvenSumTwo (d0e4 (1802+6720*t)) ∧
    evenEvenSumTwo (d0e5 (1802+6720*t)) ∧
    evenEvenSumTwo (d0e6 (1802+6720*t)) := by
  simp [evenEvenSumTwo,d0e0,d0e1,d0e2,d0e3,d0e4,d0e5,d0e6]
  omega

/-- Exact arithmetic at the end of the seven-step direct-parent chain
for u=1802+6720*t. The final direct parent is even/odd, 3-divisible,
and has sum-plus-one of exact 2-adic valuation two. -/
theorem d0e_terminal_profile (t : Nat) :
    let u := 1802+6720*t
    let p := d0e8 u
    p.1 = 7024644480*t+1883762126 ∧
    p.2 = 10893120*t+2921149 ∧
    p.1%2=0 ∧ p.2%2=1 ∧ 5≤p.2 ∧
    (p.1+p.2)%3=0 ∧
    (p.1+p.2+1)%4=0 ∧
    (p.1+p.2+1)%8=4 := by
  dsimp [d0e8]
  omega

/-- The unique odd-a, depth-zero parent forced by the terminal
even/odd three-divisible target has odd/odd coordinates and sum 2 mod 4. -/
theorem d0e_terminal_parent_profile (t : Nat) :
    let u := 1802+6720*t
    let x := (d0e8 u).1
    let y := (d0e8 u).2
    let a := 3517768800*t+943341635
    let k := 1764330960*t+473131391
    2*a+6=x+y+1 ∧
    2*k+a+7=x+2*y ∧
    a%2=1 ∧ k%2=1 ∧ 5≤k ∧ (a+k)%4=2 := by
  dsimp [d0e8]
  omega

/-- The two arithmetic candidates at the state immediately before
the terminal target: its direct parent is d0e8, and its depth-one
even-a bounce parent is E7(t). -/
theorem d0e7_parent_profile (t : Nat) :
    let u := 1802+6720*t
    let p := d0e7 u
    let S := 878080560*t+235470266
    let direct := (7024644480*t+1883762126,10893120*t+2921149)
    let bounce := (1756161120*t+470940530,2645134800*t+709331944)
    p.1+p.2=8*S ∧ S%4=2 ∧ 2<S ∧
    directParent p=direct ∧
    (2*S-2,(p.1+2*p.2-2*S-8)/2)=bounce := by
  constructor
  · dsimp [d0e7]
    omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · apply Prod.ext <;> dsimp [directParent,d0e7] <;> omega
  · apply Prod.ext <;> dsimp [d0e7] <;> omega

/-- The E7 residual's direct parent is even/odd with sum-plus-one
of exact 2-adic valuation two. Its odd-a depth-zero parent is the
odd/even family R(t), whose sum residue is 6t+5 mod 8. -/
theorem e7_parent_profile (t : Nat) :
    let e := (1756161120*t+470940530,2645134800*t+709331944)
    let p := directParent e
    let a := 2861931660*t+767469219
    let k := 2092249530*t+561067594
    e.1%2=0 ∧ e.2%2=0 ∧ (e.1+e.2)%4=2 ∧
    p=(4401295920*t+1180272472,1322567400*t+354665971) ∧
    p.1%2=0 ∧ p.2%2=1 ∧ p.2≥5 ∧
    (p.1+p.2+1)%8=4 ∧
    2*a+6=p.1+p.2+1 ∧
    2*k+a+7=p.1+2*p.2 ∧
    a%2=1 ∧ k%2=0 ∧
    (a+k)%8=(6*t+5)%8 := by
  dsimp [directParent]
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · apply Prod.ext <;> omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · omega

/-- The exact root equation fixes the residue of the D0E parameter:
if r=32+64*j and u=1802+6720*t, then t+j is divisible by four. -/
theorem root32_t_mod4 (t j E r : Nat)
    (hr : r=32+64*j)
    (hroot : 18018+211*(1802+6720*t)+22155*r=20*2^(E-13))
    (hE : 21≤E) :
    (t+j)%4=0 := by
  have hpow : 256∣2^(E-13) := by
    refine ⟨2^(E-21),?_⟩
    have hexp : E-13=8+(E-21) := by omega
    rw [hexp,Nat.pow_add,show (2:Nat)^8=256 by decide]
  have hdiv : 256∣20*2^(E-13) := by
    rcases hpow with ⟨q,hq⟩
    refine ⟨20*q,?_⟩
    rw [hq]
    omega
  have hdivL : 256∣18018+211*(1802+6720*t)+22155*r := by
    rw [hroot]
    exact hdiv
  have hfactor :
      18018+211*(1802+6720*t)+22155*(32+64*j) =
        64*(17300+22155*(t+j)) := by omega
  have hdivL' : 256∣18018+211*(1802+6720*t)+22155*(32+64*j) := by
    simpa [hr] using hdivL
  have hdiv64 : 256∣64*(17300+22155*(t+j)) := by
    rw [← hfactor]
    exact hdivL'
  rcases hdiv64 with ⟨q,hq⟩
  have hdiv4 : 4∣17300+22155*(t+j) := by
    refine ⟨q,?_⟩
    have heq : 64*(17300+22155*(t+j))=64*(4*q) := by
      calc
        64*(17300+22155*(t+j)) = 256*q := hq
        _ = 64*(4*q) := by omega
    exact Nat.mul_left_cancel (by omega) heq
  have hmod : (17300+22155*(t+j))%4=0 :=
    Nat.mod_eq_zero_of_dvd hdiv4
  have hmod' : (22155*(t+j))%4=0 := by
    have h17300 : 17300%4=0 := by decide
    simpa [Nat.add_mod,h17300] using hmod
  omega

theorem d0e_exceptional_root_class (t j r : Nat)
    (hr : r=32+64*j)
    (htj : (t+j)%4=0)
    (ht : t%4=3) :
    j%4=1 ∧ r%256=96 := by omega

theorem e7_R_even_right_conditions (t : Nat) (ht : t%4≠3) :
    (6*t+5)%8≠0 ∧ (6*t+5)%8≠7 := by omega

#print axioms d0e_direct_chain
#print axioms d0e_terminal_profile
#print axioms d0e_terminal_parent_profile
#print axioms d0e7_parent_profile
#print axioms d0e_intermediate_profile
#print axioms e7_parent_profile
#print axioms root32_t_mod4
#print axioms d0e_exceptional_root_class
#print axioms e7_R_even_right_conditions

end BB6.Agent15D0E
