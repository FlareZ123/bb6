import DirectBlocks
import Lean.Elab.Tactic.Omega

namespace BB6.Agent12DirectJump
open BB6.Agent42DirectBlocks

def jumpGate (x y : Nat) : Prop :=
  let d := directDepth y
  let u := directOdd y
  2≤d ∧ 3≤u ∧ y+2=2^d*u ∧ (x%4=0 ∨ x%4=3)
instance (x y : Nat) : Decidable (jumpGate x y) := by unfold jumpGate; infer_instance

def jumpTarget (x y : Nat) : Nat × Nat :=
  let r := directDepth y-1
  let k := 2*directOdd y-2
  (x+2*y-2*k-4*r,k)

theorem jump_source (reach : Nat → Nat → Prop) (hd : DirectLaw reach) (x y : Nat)
    (hg : jumpGate x y) : (reach x y ↔ reach (jumpTarget x y).1 (jumpTarget x y).2) ∧
      (jumpTarget x y).1+2*(jumpTarget x y).2+4*(directDepth y-1)=x+2*y ∧ 6≤y := by
  obtain ⟨hdep,hu,he,hx⟩ := hg
  change 2≤directDepth y at hdep
  change 3≤directOdd y at hu
  change y+2=2^(directDepth y)*directOdd y at he
  let r := directDepth y-1
  let u := directOdd y
  have he' : y+2=2^r*(2*u) := by
    have hr : directDepth y=r+1 := by dsimp [r]; omega
    rw [he,hr,Nat.pow_succ,Nat.mul_assoc]
  obtain ⟨a,hreach,hm,hr⟩ := direct_block reach hd r x y (2*u) (by omega) (by omega) he' hx
  have ha : a=x+2*y-2*(2*u-2)-4*r := by omega
  have hy : 6≤y := by
    have hp : 4≤2^directDepth y := Nat.pow_le_pow_right (by decide : 0<2) hdep
    have hmul := Nat.mul_le_mul_right (directOdd y) hp
    omega
  change (reach x y ↔ reach (x+2*y-2*(2*u-2)-4*r) (2*u-2)) ∧
    (x+2*y-2*(2*u-2)-4*r)+2*(2*u-2)+4*r=x+2*y ∧ 6≤y
  rw [←ha]
  exact ⟨hreach,hm,hy⟩

theorem jump_rank (reach : Nat → Nat → Prop) (hd : DirectLaw reach) (x y : Nat)
    (hg : jumpGate x y) : ((jumpTarget x y).1+2*(jumpTarget x y).2)/2<(x+2*y)/2 := by
  have hm := (jump_source reach hd x y hg).2.1
  have hdep : 2≤directDepth y := hg.1
  omega

#print axioms jump_source
#print axioms jump_rank
end BB6.Agent12DirectJump
