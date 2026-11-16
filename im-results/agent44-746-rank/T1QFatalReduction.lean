import LevelDeficitDynamics

set_option maxHeartbeats 0

namespace CascadeT1QFatal

open CascadeLevelDeficit

/-- Repeated application of the exact even-reset height map at a fixed
    level. The level may change only at the final threshold step. -/
def evenIter (k : Nat) : Nat → Nat → Nat
  | 0, h => h
  | n+1, h => evenOutput (evenIter k n h) k

/-- The t=1 source/Q equation determines the child's exact deficit one
    level above the source scale. -/
theorem t1_q_alignment_child_deficit (K a d j u : Nat)
    (hcomp : a+d=2^(K+2))
    (houtput : 2*u+5=9*d)
    (halign :
      9*a+2*K+7 = 2^(K+2)+(2*K+7)*2^(j+1)) :
    deficit u (K+1)=(2*K+7)*2^j := by
  have hpowK : 8*2^(K+1)=4*2^(K+2) := by
    simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hpowJ : 2^(j+1)=2*2^j := by
    rw [Nat.pow_succ]
  have hmul : (2*K+7)*(2*2^j)=2*((2*K+7)*2^j) := by
    ring
  have htwice :
      2*deficit u (K+1)=2*((2*K+7)*2^j) := by
    dsimp [deficit]
    rw [hpowK]
    have hlin :
        2*(4*2^(K+2)+(K+1)-u)=(2*K+7)*2^(j+1) := by
      omega
    rw [hpowJ, hmul] at hlin
    exact hlin
  omega

/-- After m even resets at one fixed level, the deficit has been divided
    by 2^m. This is the exact iterated form of even_deficit_halves. -/
theorem evenIter_deficit_drop (h k c j m : Nat)
    (hm : m≤j)
    (hD : deficit h k=2^j*c) :
    deficit (evenIter k m h) k=2^(j-m)*c := by
  induction m generalizing h with
  | zero =>
      simpa [evenIter] using hD
  | succ m ih =>
      have hm' : m≤j := by omega
      have hDm : deficit (evenIter k m h) k=2^(j-m)*c :=
        ih h hm' hD
      have hexp : j-m=(j-(m+1))+1 := by omega
      have hDtwice :
          deficit (evenIter k m h) k =
            2*(2^(j-(m+1))*c) := by
        rw [hDm, hexp, Nat.pow_succ]
        ring
      have hpar : (evenIter k m h+k)%2=0 := by
        dsimp [deficit] at hDtwice
        omega
      have hhalf :=
        even_deficit_halves (evenIter k m h) k hpar
      have hnext :
          deficit (evenOutput (evenIter k m h) k) k =
            2^(j-(m+1))*c := by
        omega
      simpa [evenIter] using hnext

/-- The complete t=1 Q-parent chain ends at the fatal height F_(K+2):
    after exactly j even-reset maps, the fatal equality holds. -/
theorem t1_q_alignment_even_chain_fatal (K a d j u : Nat)
    (hcomp : a+d=2^(K+2))
    (houtput : 2*u+5=9*d)
    (halign :
      9*a+2*K+7 = 2^(K+2)+(2*K+7)*2^(j+1)) :
    evenIter (K+1) j u + (K+2)+4 = 4*2^(K+2) := by
  have hD := t1_q_alignment_child_deficit K a d j u hcomp houtput halign
  have hD' : deficit u (K+1)=2^j*(2*K+7) := by
    simpa [Nat.mul_comm] using hD
  have hfinal :=
    evenIter_deficit_drop u (K+1) (2*K+7) j j (Nat.le_refl j) hD'
  have hfinal' :
      deficit (evenIter (K+1) j u) (K+1)=2*K+7 := by
    simpa using hfinal
  have hpow : 8*2^(K+1)=4*2^(K+2) := by
    simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  dsimp [deficit] at hfinal'
  omega

#print axioms t1_q_alignment_child_deficit
#print axioms evenIter_deficit_drop
#print axioms t1_q_alignment_even_chain_fatal

end CascadeT1QFatal
