import SweepOddFatalNine

namespace CascadeFastReturn
open CascadeBitSweep

private theorem pow2_six (n : Nat) : 2^(n+6)%9=2^n%9 := by
  rw [Nat.pow_add]
  simp [Nat.mul_mod]

private theorem pow2_mod9_reduced (n : Nat) :
    2^n%9=2^(n%6)%9 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n<6
    · rw [Nat.mod_eq_of_lt hn]
    · have ht : n=(n-6)+6 := by omega
      have hm : n%6=(n-6)%6 := by omega
      calc
        2^n%9 = 2^((n-6)+6)%9 := congrArg (fun e : Nat => 2^e%9) ht
        _ = 2^(n-6)%9 := pow2_six (n-6)
        _ = 2^((n-6)%6)%9 := ih (n-6) (by omega)
        _ = 2^(n%6)%9 := by rw [hm]

private theorem mod_gate_reduced (k m : Nat) :
    ((16*2^k+2*k+5)%9 = (2^(m+1)*(4*k+10))%9) ↔
    ((16*2^(k%6)+2*(k%9)+5)%9 =
         (2^((m+1)%6)*(4*(k%9)+10))%9) := by
  have hp : (2^k)%9=(2^(k%6))%9 := pow2_mod9_reduced k
  have hl : (16*2^k+2*k+5)%9 = (16*2^(k%6)+2*(k%9)+5)%9 := by omega
  have hq : (2^(m+1))%9 = (2^((m+1)%6))%9 := pow2_mod9_reduced (m+1)
  have hr : (4*k+10)%9 = (4*(k%9)+10)%9 := by omega
  have hright : (2^(m+1)*(4*k+10))%9 =
      (2^((m+1)%6)*(4*(k%9)+10))%9 := by
    have hxy : ((2^(m+1)%9)*((4*k+10)%9))%9 =
      ((2^((m+1)%6)%9)*((4*(k%9)+10)%9))%9 := by rw [hq, hr]
    simpa only [Nat.mul_mod, Nat.mod_mod] using hxy
  rw [hl,hright]

/-- This exhaustive finite check is only 18*6=108 numeral pairs.
    Mathematical periodicity of 2 modulo 9 lifts it to all k and m. -/
private theorem finite_gate_table (r s : Nat)
    (hr : r<18) (hs : s<6)
    (hsector : r%6=3 ∨ r%6=4)
    (hgate : (16*2^(r%6)+2*(r%9)+5)%9 =
          (2^((s+1)%6)*(4*(r%9)+10))%9) :
    (r=3∧s=5)∨(r=4∧s=5)∨(r=9∧s=3)∨
    (r=10∧s=1)∨(r=15∧s=1)∨(r=16∧s=3) := by
  have table : ∀ (x : Fin 18) (y : Fin 6),
    (x.val%6=3 ∨ x.val%6=4) →
    (16*2^(x.val%6)+2*(x.val%9)+5)%9 =
      (2^((y.val+1)%6)*(4*(x.val%9)+10))%9 →
    (x.val=3∧y.val=5)∨(x.val=4∧y.val=5)∨
    (x.val=9∧y.val=3)∨(x.val=10∧y.val=1)∨
    (x.val=15∧y.val=1)∨(x.val=16∧y.val=3) := by decide
  exact table ⟨r, hr⟩ ⟨s, hs⟩ hsector hgate

/-- For a surviving fatal level k=3 or 4 modulo 6, the necessary
    high odd-entry fatal gate selects one m class modulo 6. -/
theorem odd_fatal_depth_residue_table (k m : Nat)
    (hsector : k%6=3 ∨ k%6=4)
    (hgate : (16*2^k+2*k+5)%9=(2^(m+1)*(4*k+10))%9) :
    (k%18=3∧m%6=5)∨(k%18=4∧m%6=5)∨
    (k%18=9∧m%6=3)∨(k%18=10∧m%6=1)∨
    (k%18=15∧m%6=1)∨(k%18=16∧m%6=3) := by
  let r := k%18
  let s := m%6
  have hr : r<18 := Nat.mod_lt k (by decide)
  have hs : s<6 := Nat.mod_lt m (by decide)
  have hk6 : k%6=r%6 := by dsimp [r]; omega
  have hk9 : k%9=r%9 := by dsimp [r]; omega
  have hm6 : (m+1)%6=(s+1)%6 := by dsimp [s]; omega
  have hred := (mod_gate_reduced k m).mp hgate
  have hgate' : (16*2^(r%6)+2*(r%9)+5)%9 =
      (2^((s+1)%6)*(4*(r%9)+10))%9 := by
    rw [←hk6, ←hk9, ←hm6]
    exact hred
  have hsector' : r%6=3 ∨ r%6=4 := by simpa only [←hk6] using hsector
  exact finite_gate_table r s hr hs hsector' hgate'

/-- Full authenticated first-return consequence, uniform in all levels and
    arbitrary same-level depths. A blank-root reachability claim is not used.
    The hhigh hypothesis is equivalent, given the adjacent-fatal deficit
    identity, to the directly checkable condition
      2^m*(4k+10) ≤ 2*2^k+k. -/
theorem odd_entry_adjacent_fatal_depth_residue (k a entry z v m : Nat)
    (hsector : k%6=3 ∨ k%6=4)
    (haodd : (a+firstFailIndex a)%2=1)
    (ha : bitOutcome a=some entry)
    (hk : firstFailIndex entry=k)
    (hhigh : 6*2^k≤entry)
    (hp : SameLevelPath k entry z m)
    (hz : bitOutcome z=some v)
    (hu : firstFailIndex v=k+1)
    (hf : fatalAt v) :
    (k%18=3∧m%6=5)∨(k%18=4∧m%6=5)∨
    (k%18=9∧m%6=3)∨(k%18=10∧m%6=1)∨
    (k%18=15∧m%6=1)∨(k%18=16∧m%6=3) := by
  exact odd_fatal_depth_residue_table k m hsector
    (high_odd_entry_adjacent_fatal_mod_nine k a entry z v m
      haodd ha hk hhigh hp hz hu hf)

#print axioms odd_fatal_depth_residue_table
#print axioms odd_entry_adjacent_fatal_depth_residue
end CascadeFastReturn
