import ForwardRun
import ScanFail
import StripTwos
set_option maxHeartbeats 0
namespace CascadeFastReturn
open CascadeResetInverse CascadeRank

/-- Primitive computable first-reset successor, using only the dyadic first
    guard and exact extraction of powers of two. Halting returns none. -/
def fastOutcome (h : Nat) : Option Nat :=
  let k := firstFailedK h
  if h+k+4=4*2^k then none
  else if (h+k)%2=0 then some (4*2^k+(h+k)/2)
  else
    let q := 4*2^k+(h+k)/2+3
    let t := (stripTwos q).1
    let d := (stripTwos q).2
    some ((3^(t+1)*d-5)/2)

/-- Every evaluation of the computable program is source-certified as the
    genuine first reset or halt, including arbitrary 2-adic drain depth. -/
theorem fastOutcome_sound (h : Nat) : Outcome (h,0) (fastOutcome h) := by
  let k := firstFailedK h
  have hk := firstFailedK_spec h
  have hg : ∀ j, j<k → 8*2^j≤h+j+5 := by
    intro j hj
    have hj' := hk.2 j hj
    dsimp [failed] at hj'
    omega
  have hhigh : h+k+5<8*2^k := hk.1
  have hlow : 4*2^k≤h+k+4 := first_low h k hg
  by_cases hfat : h+k+4=4*2^k
  · have hs : fastOutcome h=none := by simp [fastOutcome, show firstFailedK h=k from rfl, hfat]
    rw [hs]
    rcases closed_outcome h k hg hhigh with hcase | hcase | hcase
    · exact hcase.2
    · exact False.elim (hcase.1 hfat)
    · rcases hcase with ⟨t,d,hnot,hrest⟩
      exact False.elim (hnot hfat)
  · by_cases hpar : (h+k)%2=0
    · have hs : fastOutcome h=some (4*2^k+(h+k)/2) := by
        simp [fastOutcome, show firstFailedK h=k from rfl, hfat, hpar]
      rw [hs]
      exact even_outcome h k hg hlow hhigh hfat hpar
    · have hodd : (h+k)%2=1 := by omega
      let q := 4*2^k+(h+k)/2+3
      have hq : 0<q := by dsimp [q]; omega
      have hf := stripTwos_spec q hq
      have hfac : 4*2^k+(h+k)/2+3 = 2^(stripTwos q).1*(stripTwos q).2 := by
        exact hf.1
      have hs : fastOutcome h = some ((3^((stripTwos q).1+1)*(stripTwos q).2-5)/2) := by
        simp [fastOutcome, show firstFailedK h=k from rfl, hfat, hpar, q]
      rw [hs]
      exact odd_outcome h k (stripTwos q).1 (stripTwos q).2 hg hlow hhigh hfat hodd hfac hf.2

/-- The executable successor is mathematically identical to the arbitrary
    first-outcome selector used in the bounded root-path theorem. -/
theorem fastOutcome_eq_nextReset (h : Nat) : fastOutcome h = nextReset h :=
  outcome_unique (fastOutcome_sound h)
    (Classical.choose_spec (first_outcome_exists h))

#print axioms fastOutcome_sound
#print axioms fastOutcome_eq_nextReset
end CascadeFastReturn
