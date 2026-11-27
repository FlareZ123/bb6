import Branch29Roster31
import Lean.Elab.Tactic.Omega

/-!
# Source-rooted branch29 terminal-burst residue restriction modulo 262144

At any true blank-reachable branch-29 final-burst prestate,
the exact reset equation forces n mod262144 into one of 31 classes.
This all-parameter conclusion depends only on the source-sound
31/2048 q-roster and elementary arithmetic, not on finite k scans.
-/
namespace BB429Branch29BurstMod262144
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def admissibleK : List Nat :=
  [63,126,254,278,319,383,398,463,639,719,767,870,894,1023,1046,
   1071,1126,1174,1199,1231,1327,1382,1430,1599,1638,1678,1855,
   1934,1967,2046,2047]

def admissibleN : List Nat := admissibleK.map (fun k => 128*k+127)

theorem count : admissibleN.length = 31 := by decide

private theorem k_partition :
    (List.range 2048).all (fun r =>
      decide ((∃ s ∈ BB429Branch29Roster31.surviving2048,
        (s+3*r+4)%2048=0) → r∈admissibleK)) = true := by
  decide +kernel

private theorem k_necessary (q k : Nat)
    (hroot : BB429NewResidue.Reach (32*q+29) (64*q+55))
    (hsum : (q+3*k+4)%2048=0) : k%2048∈admissibleK := by
  have hr := (BB429Branch29Roster31.rooted_29_q_31_mod2048 q hroot).2
  have hklt : k%2048<2048 := Nat.mod_lt _ (by decide)
  have hp := (List.all_eq_true.mp k_partition) (k%2048) (List.mem_range.mpr hklt)
  have hf : (∃ s ∈ BB429Branch29Roster31.surviving2048,
      (s+3*(k%2048)+4)%2048=0) → k%2048∈admissibleK := of_decide_eq_true hp
  apply hf
  refine ⟨q%2048,hr,?_⟩
  omega

/-- Exact infinitely quantified source-rooted terminal-burst 31-class
necessity modulo 262144; no bound on q,n or simulated root time. -/
theorem rooted_branch29_burst_mod262144 (q n : Nat) (hn : 18≤n)
    (hroot : BB429NewResidue.Reach (32*q+29) (64*q+55))
    (heq : 128*q+3*n+131=3*2^(n+2)) :
    n%262144∈admissibleN := by
  have hpow : 2^(n+2)=128*2^(n-5) := by
    have hsplit : n+2=7+(n-5) := by omega
    rw [hsplit,Nat.pow_add]
  have hmod128 : (128*q+3*n+131)%128=0 := by
    rw [heq,hpow]
    omega
  let k := n/128
  have hnform : n=128*k+127 := by dsimp [k]; omega
  have heq' : 128*q+3*n+131=384*2^(n-5) := by rw [hpow] at heq; omega
  have hq : q+3*k+4=3*2^(n-5) := by omega
  have hdvd : 2^11 ∣ 2^(n-5) := Nat.pow_dvd_pow 2 (by omega)
  have hdvd' : 2048 ∣ 2^(n-5) := by simpa using hdvd
  have hmod : (q+3*k+4)%2048=0 := by
    have hx : (2^(n-5))%2048=0 := Nat.mod_eq_zero_of_dvd hdvd'
    omega
  have hk : k%2048∈admissibleK := k_necessary q k hroot hmod
  have hrem : n%262144=128*(k%2048)+127 := by omega
  exact List.mem_map.mpr ⟨k%2048,hk, by omega⟩

#print axioms rooted_branch29_burst_mod262144
end BB429Branch29BurstMod262144
