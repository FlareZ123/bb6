import BitCarry
namespace BB6.Agent28BitSpread
open BB6.Agent28BitCarry

/-- Inverse of the broadword packing network: every input bit i is transported
    to bit 2*i. The soundness direction suffices for reverse certificates. -/
def spreadStep (L k x : Nat) : Nat :=
  (x ||| (x <<< 2^k)) &&& laneMask (2^k) (L-k)

theorem spreadStep_sound (L k x i : Nat) (hk : k<L) (hi : i<2^L)
    (h : x.testBit (packedPos (k+1) i)=true) :
    (spreadStep L k x).testBit (packedPos k i)=true := by
  rw [spreadStep, Nat.testBit_and, Nat.testBit_or, packedPos_mask k L i (by omega) hi]
  rcases packedPos_step k i with he | he
  · rw [he]
    simp [h]
  · rw [he, Nat.testBit_shiftLeft]
    have hle : 2^k≤packedPos (k+1) i+2^k := by omega
    have hsub : packedPos (k+1) i+2^k-2^k=packedPos (k+1) i := by omega
    simp [hle,hsub,h]

def spreadFrom (L : Nat) : Nat → Nat → Nat
  | 0,x => x
  | k+1,x => spreadFrom L k (spreadStep L k x)

theorem spreadFrom_sound (L k x i : Nat) (hk : k≤L) (hi : i<2^L)
    (h : x.testBit (packedPos k i)=true) :
    (spreadFrom L k x).testBit (packedPos 0 i)=true := by
  induction k generalizing x with
  | zero => exact h
  | succ k ih =>
      exact ih (spreadStep L k x) (by omega) (spreadStep_sound L k x i (by omega) hi h)

def spreadEven (L x : Nat) : Nat := spreadFrom L L x

theorem spreadEven_sound (L x i : Nat) (hi : i<2^L) (h : x.testBit i=true) :
    (spreadEven L x).testBit (2*i)=true := by
  have hpos0 : packedPos 0 i=2*i := by simp [packedPos]; omega
  have hposL : packedPos L i=i := by simp [packedPos,Nat.div_eq_of_lt hi,Nat.mod_eq_of_lt hi]
  have hh : x.testBit (packedPos L i)=true := by rw [hposL]; exact h
  have hs := spreadFrom_sound L L x i (by omega) hi hh
  simpa [spreadEven,hpos0] using hs

/-- Push endpoint bits backwards under c ↦ (2*c+y) mod C, provided all
    genuine endpoints have 2*c+y<2*C. -/
def reverseStep (L C y bits : Nat) : Nat :=
  let u := spreadEven L bits <<< y
  (u ||| (u >>> C)) &&& (2^C-1)

theorem reverseStep_sound (L C y bits c : Nat) (hC : 0<C)
    (hc : c<2^L) (hbound : 2*c+y<2*C) (h : bits.testBit c=true) :
    (reverseStep L C y bits).testBit ((2*c+y)%C)=true := by
  have hsp := spreadEven_sound L bits c hc h
  have hu : (spreadEven L bits <<< y).testBit (2*c+y)=true := by
    simp [show y≤2*c+y by omega,show 2*c+y-y=2*c by omega,hsp]
  have hmod := Nat.mod_lt (2*c+y) hC
  rw [reverseStep,Nat.testBit_and,Nat.testBit_or,Nat.testBit_two_pow_sub_one]
  simp only [decide_eq_true hmod, Bool.and_true]
  by_cases hlo : 2*c+y<C
  · rw [Nat.mod_eq_of_lt hlo]
    simp [hu]
  · have he : (2*c+y)%C=2*c+y-C := by
      rw [Nat.mod_eq_sub_mod (show C≤2*c+y by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [he,Nat.testBit_shiftRight]
    have hadd : C+(2*c+y-C)=2*c+y := by omega
    simp [hadd,hu]

#print axioms spreadEven_sound
#print axioms reverseStep_sound
end BB6.Agent28BitSpread
