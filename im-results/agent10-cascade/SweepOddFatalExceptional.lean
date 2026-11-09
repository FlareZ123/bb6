import SweepOddFatalResidue

namespace CascadeFastReturn
open CascadeBitSweep

/-- An exact source odd entry to level k, followed by genuine same-level
    returns and a successful adjacent even fatal exit. Blank-root
    reachability is not assumed. -/
def OddFatalHistory (k m : Nat) : Prop :=
  ∃a e z v, (a+firstFailIndex a)%2=1 ∧
    bitOutcome a=some e ∧ firstFailIndex e=k ∧
    SameLevelPath k e z m ∧ bitOutcome z=some v ∧
    firstFailIndex v=k+1 ∧ fatalAt v

private theorem low_entry_depth_unique (k m₁ m₂ e₁ e₂ : Nat)
    (hm₁ : m₁%2=1) (hm₂ : m₂%2=1)
    (hlt : m₁<m₂)
    (hdef₁ : e₁+2^m₁*(4*k+10)=8*2^k+k)
    (hdef₂ : e₂+2^m₂*(4*k+10)=8*2^k+k)
    (hentrylow : e₁<6*2^k) : False := by
  have hstep : m₁+2≤m₂ := by omega
  have hpowle : 2^(m₁+2)≤2^m₂ := Nat.pow_le_pow_right (by decide) hstep
  have hpow : 2^(m₁+2)=4*2^m₁ := by
    rw [Nat.pow_add]
    simp
    ac_rfl
  rw [hpow] at hpowle
  have hmul : 4*(2^m₁*(4*k+10)) ≤ 2^m₂*(4*k+10) := by
    calc
      4*(2^m₁*(4*k+10)) = (4*2^m₁)*(4*k+10) := by ac_rfl
      _ ≤ 2^m₂*(4*k+10) := Nat.mul_le_mul_right _ hpowle
  omega

/-- In every source-level k, among any two odd-entry histories into the
    adjacent even fatal threshold, the smaller same-level depth must have
    entry height at least 6*2^k. At most one candidate depth can be lower. -/
theorem earlier_odd_fatal_entry_high (k m₁ m₂ : Nat)
    (hlt : m₁<m₂)
    (h₁ : OddFatalHistory k m₁)
    (h₂ : OddFatalHistory k m₂) :
    ∃a e z v, (a+firstFailIndex a)%2=1 ∧
      bitOutcome a=some e ∧ firstFailIndex e=k ∧
      SameLevelPath k e z m₁ ∧ bitOutcome z=some v ∧
      firstFailIndex v=k+1 ∧ fatalAt v ∧ 6*2^k≤e := by
  obtain ⟨a₁,e₁,z₁,v₁,hodd₁,ha₁,hk₁,hpath₁,hz₁,hu₁,hf₁⟩ := h₁
  obtain ⟨a₂,e₂,z₂,v₂,hodd₂,ha₂,hk₂,hpath₂,hz₂,hu₂,hf₂⟩ := h₂
  have hm₁ := odd_entry_adjacent_fatal_depth_odd k a₁ e₁ z₁ v₁ m₁
    hodd₁ ha₁ hk₁ hpath₁ hz₁ hu₁ hf₁
  have hm₂ := odd_entry_adjacent_fatal_depth_odd k a₂ e₂ z₂ v₂ m₂
    hodd₂ ha₂ hk₂ hpath₂ hz₂ hu₂ hf₂
  have hdef₁ := adjacent_fatal_after_same_level_path k e₁ z₁ v₁ m₁
    hpath₁ hz₁ hu₁ hf₁
  have hdef₂ := adjacent_fatal_after_same_level_path k e₂ z₂ v₂ m₂
    hpath₂ hz₂ hu₂ hf₂
  have hbd₁ := (firstFailIndex_spec e₁).2
  have hbd₂ := (firstFailIndex_spec e₂).2
  rw [hk₁] at hbd₁
  rw [hk₂] at hbd₂
  have heq₁ : e₁+2^m₁*(4*k+10)=8*2^k+k := by
    dsimp [deficitAt] at hdef₁
    omega
  have heq₂ : e₂+2^m₂*(4*k+10)=8*2^k+k := by
    dsimp [deficitAt] at hdef₂
    omega
  have hhigh : 6*2^k≤e₁ := by
    by_cases hh : 6*2^k≤e₁
    · exact hh
    · have hlo : e₁<6*2^k := by omega
      exact False.elim (low_entry_depth_unique k m₁ m₂ e₁ e₂ hm₁ hm₂
        hlt heq₁ heq₂ hlo)
  exact ⟨a₁,e₁,z₁,v₁,hodd₁,ha₁,hk₁,hpath₁,hz₁,hu₁,hf₁,hhigh⟩

/-- Two distinct odd-entry adjacent-fatal histories in the surviving sector
    force the smaller depth into the unique class of the mod-18 table.
    Only a possibly largest odd depth can evade the congruence. -/
theorem earlier_odd_fatal_depth_residue (k m₁ m₂ : Nat)
    (hlt : m₁<m₂)
    (h₁ : OddFatalHistory k m₁)
    (h₂ : OddFatalHistory k m₂) :
    (k%18=3∧m₁%6=5)∨(k%18=4∧m₁%6=5)∨
    (k%18=9∧m₁%6=3)∨(k%18=10∧m₁%6=1)∨
    (k%18=15∧m₁%6=1)∨(k%18=16∧m₁%6=3) := by
  obtain ⟨a,e,z,v,hodd,ha,hk,hpath,hz,hu,hf,hh⟩ :=
    earlier_odd_fatal_entry_high k m₁ m₂ hlt h₁ h₂
  have hsector := odd_entry_adjacent_fatal_level_sector k a e z v m₁
    hodd ha hk hpath hz hu hf
  exact odd_entry_adjacent_fatal_depth_residue k a e z v m₁
    hsector hodd ha hk hh hpath hz hu hf

#print axioms earlier_odd_fatal_entry_high
#print axioms earlier_odd_fatal_depth_residue
end CascadeFastReturn
