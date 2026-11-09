import Std
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace CascadeFatal46

/-- A certificate on the residue j mod486 for the source valuation-one
    fatal odd predecessor. Both displayed tests are integer remainders.
    The fixed shifts avoid natural-number subtraction underflow. -/
def good (r : Nat) : Prop :=
  let q := 2^((r+160)%162)%243
  (r%18=4 ∨ r%18=5) ∧
  (112*q+243*100-34*(r%243)-33)%243 ≠ 0 ∧
  (80*q+81*300-86*(r%243)-75)%81 ≠ 0

instance (r : Nat) : Decidable (good r) := by
  unfold good
  infer_instance

/-- Exactly 46 of the 54 valuation-one odd-feeder residue classes
    j mod486 pass both strict modular root-exclusion gates.
    The finite 486-row arithmetic table is kernel-computed. -/
theorem exact_good_residue_count :
    ((List.range 486).filter (fun r => decide (good r))).length=46 := by
  decide

private theorem pow_period162 (k : Nat) :
    2^(k+162)%243=2^k%243 := by
  rw [Nat.pow_add, Nat.mul_mod]
  have h : 2^162%243=1 := by decide
  rw [h]
  simp

private theorem pow_mod162 (k : Nat) :
    2^k%243=2^(k%162)%243 := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hk : k<162
    · simp [Nat.mod_eq_of_lt hk]
    · have hk' : k-162<k := by omega
      have he : k=(k-162)+162 := by omega
      rw [he,pow_period162,ih (k-162) hk']
      have hre : ((k-162)+162)%162=(k-162)%162 := by omega
      rw [hre]

private theorem growth (k : Nat) (hk : 20≤k) :
    12*(k+2)+40<2^k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : 20≤k
    · have hp := ih h
      rw [Nat.pow_succ]
      omega
    · have he : k=19 := by omega
      subst k
      decide

private theorem modular_raw (n : Nat) (hn : 22≤n)
    (hg : good (n%486)) :
    let p := 2^(n-2)
    (112*p-34*n-33)%243≠0 ∧
    (80*p-86*n-75)%81≠0 := by
  let k := n-2
  let p := 2^k
  let r := n%486
  let q := 2^((r+160)%162)%243
  have hk : 20≤k := by dsimp [k]; omega
  have hpbound : 12*n+40<p := by
    have he : n=k+2 := by dsimp [k]; omega
    rw [he]
    exact growth k hk
  have hrk : k%162=(r+160)%162 := by dsimp [k,r]; omega
  have hpn : p%243=q := by
    dsimp [p,q]
    rw [pow_mod162, hrk]
  have hrn : n%243=r%243 := by dsimp [r]; omega
  have hg1 : (112*q+243*100-34*(r%243)-33)%243≠0 := hg.2.1
  have hg2 : (80*q+81*300-86*(r%243)-75)%81≠0 := hg.2.2
  have hx : (112*p-34*n-33)%243≠0 := by omega
  have hh : (80*p-86*n-75)%81≠0 := by omega
  exact ⟨hx,hh⟩

/-- Periodic arithmetic transport from a source fatal candidate x and
    its forced parent h to both exact no-image tests. Period 162 for
    powers of two mod243 and period 243 for the linear index combine
    into period 486, with no finite-bound restriction on n. -/
theorem source_bridge (n x h : Nat)
    (hrelx : 9*x+17*n+39=56*2^(n-2))
    (hrelh : 9*h+43*n+60=40*2^(n-2))
    (hn : 22≤n) (hg : good (n%486)) :
    (2*x+5)%27≠0 ∧ (2*h+5)%9≠0 := by
  obtain ⟨hxraw,hhraw⟩ := modular_raw n hn hg
  have hx : 9*(2*x+5)=112*2^(n-2)-34*n-33 := by omega
  have hh : 9*(2*h+5)=80*2^(n-2)-86*n-75 := by omega
  constructor
  · intro hzero
    have hhx : (9*(2*x+5))%243=0 := by omega
    rw [hx] at hhx
    exact hxraw hhx
  · intro hzero
    have hhy : (9*(2*h+5))%81=0 := by omega
    rw [hh] at hhy
    exact hhraw hhy

#print axioms exact_good_residue_count
#print axioms source_bridge
end CascadeFatal46
