import FatalFamilyDigitDecoder
import FatalFamilySource

namespace BB6.Agent41FatalInverseSource
open BB6.Agent41FatalInverse
open BB6.Agent49ParitySource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

def smallLength (k : Nat) : Nat := min k ((k+2).log2+2)

theorem smallLength_le (k : Nat) : smallLength k≤k := Nat.min_le_left ..

theorem smallLength_range (k : Nat) (hk : 7≤k) : 2*(k+2)<3^(smallLength k) := by
  unfold smallLength
  by_cases h : k≤(k+2).log2+2
  · rw [Nat.min_eq_left h]
    have hh := pow_margin k hk
    omega
  · rw [Nat.min_eq_right (by omega : (k+2).log2+2≤k)]
    have hp : k+2<2^((k+2).log2+1) := (Nat.log2_lt (by omega : k+2≠0)).mp (by omega)
    have hm : 2^((k+2).log2+2)≤3^((k+2).log2+2) := Nat.pow_le_pow_left (by decide) _
    rw [Nat.pow_succ] at hp
    rw [show (k+2).log2+2=((k+2).log2+1)+1 by omega,Nat.pow_succ,Nat.pow_succ,Nat.pow_succ,Nat.pow_succ] at hm
    rw [show (k+2).log2+2=((k+2).log2+1)+1 by omega,Nat.pow_succ,Nat.pow_succ]
    omega

def leftCandidate (k : Nat) : Option Nat := decode (smallLength k) (k+1:Nat)
def rightCandidate (k : Nat) : Option Nat := decodeRight (smallLength k) (3*(k+1):Nat)

theorem root_parameter_decoded (k i : Nat) (hk : 7≤k) (ho : k%2=1)
    (h : run i=some (.D (targetX k) (targetY k))) :
    (∃ t, leftCandidate k=some t) ∨ (∃ t, rightCandidate k=some t) := by
  have hr := smallLength_range k hk
  have hm := smallLength_le k
  have he : smallLength k+(k-smallLength k)=k := by omega
  rcases root_parameter k i hk ho h with ⟨t,ht,hl⟩|⟨t,ht,hr'⟩
  · left
    refine ⟨t,?_⟩
    unfold leftCandidate
    apply (left_gate_decode (smallLength k) (k-smallLength k) (k+1) t (by omega)).mp
    rw [he]
    unfold LeftParameter at hl
    unfold leftIndex ow
    omega
  · right
    refine ⟨t,?_⟩
    unfold rightCandidate
    apply (right_gate_decode (smallLength k) (k-smallLength k) (k+1) t (by omega)).mp
    rw [he]
    unfold RightParameter at hr'
    unfold rightIndex bw
    omega

/-- A logarithmic-length digit computation certifies an all-time authentic
root exclusion, without constructing the target counters. -/
theorem root_decoder_excluded (k : Nat) (hk : 7≤k) (ho : k%2=1)
    (hl : leftCandidate k=none) (hr : rightCandidate k=none) :
    ∀ i, run i≠some (.D (targetX k) (targetY k)) := by
  intro i h
  rcases root_parameter_decoded k i hk ho h with ⟨t,ht⟩|⟨t,ht⟩
  · rw [hl] at ht; contradiction
  · rw [hr] at ht; contradiction

#print axioms smallLength_range
#print axioms root_parameter_decoded
#print axioms root_decoder_excluded
end BB6.Agent41FatalInverseSource
