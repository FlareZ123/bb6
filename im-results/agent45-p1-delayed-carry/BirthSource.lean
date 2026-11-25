import BirthBatch
import BatchCarryChunks
namespace BB6.Agent45ReverseBlock
open BB6.Agent9BatchCarry (bitRewind mask packList)

theorem block_packed_start (L F R q d : Nat) (xs : List Nat)
    (hF : F<2^L) (hq : q+d=F) (hlo : 4≤q) (hR : R+4<q)
    (hpack : bitRewind L F (mask F) d=packList xs) :
    BlockVerified F R q q xs :=
  BB6.Agent9BatchCarry.packed_start L F R q d xs hF hq hlo hR hpack

theorem block_verified_interval (F R top lo q : Nat) (xs : List Nat)
    (hq : q≤lo+4) (hR : R+4≤top) (ht : top≤F)
    (hK : F≤2*lo+3) (hl : 14≤lo) (cert : BlockVerified F R top q xs) :
    ∀ n, lo≤n → n≤R → n%2=0 → ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  intro n h₁ h₂ he
  exact BB6.Agent9BatchCarry.critical_reset_no_reach_batch F lo n (by omega) h₁ (by omega) (by omega) he
    (batch_absent_of_verified F R top lo q n xs hq hR ht h₁ h₂ cert)

#print axioms block_packed_start
#print axioms block_verified_interval
end BB6.Agent45ReverseBlock
