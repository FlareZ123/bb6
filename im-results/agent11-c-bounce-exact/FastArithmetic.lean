import SectionFastInverseOriginal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Fast
open BB6.Agent46

/-- Bounded exact-image arithmetic with no recursive section evaluation. -/
def arithmeticValid (a k x y:Nat) : Bool :=
  let powers := List.range (fastCap x y)
  if a=0 then
    if k=0 then false
    else if k=1 then decide (x=0 ∧ y=4)
    else powers.any (fun n => decide
      (x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y))
  else if a=1 then
    if k=0 then false
    else if k=1 then false
    else if k=2 then decide (x=2 ∧ y=5)
    else if k=3 then decide (x=0 ∧ y=7)
    else powers.any (fun n => decide
      (x+y+1=2^n*16 ∧ (2*k-3)+16+3*n=x+2*y+2))
  else if k=0 then false
  else if 2*k≤a then decide (x=a-2*k ∧ y=2*k+2)
  else if a%2=0 then powers.any (fun n => decide
    (x+y=2^n*(2*(a-1)+6) ∧
     (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y))
  else powers.any (fun n => decide
    (x+y+1=2^n*(2*(a-1)+8) ∧
     (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2))

private theorem bounded_pow (x y f n:Nat) (hf:0<f)
    (h:(x+y=2^n*f) ∨ (x+y+1=2^n*f)) : n<fastCap x y := by
  have hle : 2^n ≤ 2^n*f := Nat.le_mul_of_pos_right (2^n) hf
  apply pow_depth_bounded
  rcases h with h|h <;> omega

private theorem any_iff_bounded (x y:Nat) (P:Nat→Prop) [DecidablePred P] :
  ((List.range (fastCap x y)).any (fun n=>decide (P n)))=true ↔
    ∃ n<fastCap x y, P n := by
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]

private theorem bounded_iff (x y :Nat) (P:Nat→Prop) [DecidablePred P]
    (hpow : ∀ n, P n → ∃ f:Nat, 0<f ∧
      (x+y=2^n*f ∨ x+y+1=2^n*f)) :
  ((List.range (fastCap x y)).any (fun n=>decide (P n)))=true ↔
    ∃ n, P n := by
  rw [any_iff_bounded]
  constructor
  · rintro ⟨n,_,hn⟩
    exact ⟨n,hn⟩
  · rintro ⟨n,hn⟩
    obtain ⟨f,hf,h⟩:=hpow n hn
    exact ⟨n,bounded_pow x y f n hf h,hn⟩

