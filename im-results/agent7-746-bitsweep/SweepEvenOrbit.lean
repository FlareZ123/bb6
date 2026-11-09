import SweepEvenBlock
import SweepBitOutcome

namespace CascadeFastReturn
open CascadeBitSweep

/-- One genuine source-C first-reset even return from an entire affine cylinder. -/
theorem bitOutcome_even_block_one (k m d : Nat)
    (hd : 2*k+6 ≤ d)
    (hlo : 4*2^k ≤ atHeight k (m+1) d) :
    bitOutcome (atHeight k (m+1) d) = some (atHeight k m d) := by
  obtain ⟨hk,hpar,hval⟩ := even_block_one k m d hd hlo
  have hfat : atHeight k (m+1) d + k + 4 ≠ 4 * 2 ^ k := by omega
  simp [bitOutcome, hk, hfat, hpar, hval]

/-- First-step composition for the forward source-C reset iteration. -/
theorem runBit_succ_start (start steps : Nat) :
    runBit start (steps+1) =
      (bitOutcome start).bind (fun u => runBit u steps) := by
  induction steps with
  | zero => simp [runBit]
  | succ steps ih =>
    change (runBit start (steps+1)).bind bitOutcome =
      (bitOutcome start).bind (fun u => runBit u (steps+1))
    rw [ih]
    cases h : bitOutcome start with
    | none => simp
    | some u => simp [runBit]

/-- A source-exact block of m successive even returns with a closed endpoint. -/
theorem runBit_even_block (k m d : Nat)
    (hd : 2*k+6 ≤ d) :
    4*2^k ≤ atHeight k m d →
    runBit (atHeight k m d) m = some (atHeight k 0 d) := by
  induction m with
  | zero =>
    intro hlo
    rfl
  | succ m ih =>
    intro hlo
    have hmono : atHeight k (m+1) d ≤ atHeight k m d := by
      have hp : 2^m ≤ 2^(m+1) := Nat.pow_le_pow_right (by omega) (by omega)
      have hd' := Nat.mul_le_mul_right d hp
      dsimp [atHeight]
      omega
    have hlo' : 4*2^k ≤ atHeight k m d := by omega
    rw [runBit_succ_start]
    rw [bitOutcome_even_block_one k m d hd hlo]
    simpa using ih hlo'

/-- Every prefix of a same-band even block has an explicit reset height. -/
theorem runBit_even_block_prefix (k m d : Nat) (hd : 2*k+6 ≤ d) :
    ∀ t, t ≤ m → 4*2^k ≤ atHeight k m d →
      runBit (atHeight k m d) t = some (atHeight k (m-t) d) := by
  induction m with
  | zero =>
    intro t ht hlo
    have he : t=0 := by omega
    subst t
    rfl
  | succ m ih =>
    intro t ht hlo
    cases t with
    | zero => rfl
    | succ t =>
      have ht' : t ≤ m := by omega
      have hmono : atHeight k (m+1) d ≤ atHeight k m d := by
        have hp : 2^m ≤ 2^(m+1) := Nat.pow_le_pow_right (by omega) (by omega)
        have hd' := Nat.mul_le_mul_right d hp
        dsimp [atHeight]
        omega
      have hlo' : 4*2^k ≤ atHeight k m d := by omega
      rw [runBit_succ_start]
      rw [bitOutcome_even_block_one k m d hd hlo]
      simpa [show m+1-(t+1)=m-t by omega] using ih t ht' hlo'

/-- Arithmetic-only checker for a source-certified multi-reset skip. -/
def evenBlockCheck (h k m d : Nat) : Bool :=
  decide (h=atHeight k m d ∧ 2*k+6≤d ∧ 4*2^k≤h)

theorem evenBlockCheck_sound (h k m d : Nat)
    (hc : evenBlockCheck h k m d = true) :
    runBit h m = some (atHeight k 0 d) := by
  have ⟨he,hd,hlo⟩ : h=atHeight k m d ∧ 2*k+6≤d ∧ 4*2^k≤h := by
    exact of_decide_eq_true (by simpa [evenBlockCheck] using hc)
  subst h
  exact runBit_even_block k m d hd hlo

#print axioms evenBlockCheck_sound
#print axioms runBit_even_block_prefix

#print axioms bitOutcome_even_block_one
#print axioms runBit_even_block

end CascadeFastReturn
