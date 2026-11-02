import P1Triple
namespace BB6.Agent50P1
open BB6.P1Reduction

/-- All four positive G inverse inputs when the output is (16s+4,3), s even. -/
theorem inverse_16s4_three (b d k c s : Nat)
    (h : GAncestor b d k c) (hb : b=16*s+4) (hd:d=3)
    (he:s%2=0) (hs:6≤s) :
    (k=4*s ∧ c=8*s+5) ∨
    (k=6*s+1 ∧ c=4*s+1) ∨
    (k=7*s+1 ∧ c=2*s-1) ∨
    (k=15*s/2+1 ∧ c=s-2) := by
  induction h with
  | upper k d => left; constructor <;> omega
  | nest b d k c h ih =>
      rcases ih hb hd with h1 | h2 | h3 | h4
      · obtain ⟨hk,hc⟩:=h1
        right;left
        constructor <;> omega
      · obtain ⟨hk,hc⟩:=h2
        right;right;left
        constructor <;> omega
      · obtain ⟨hk,hc⟩:=h3
        right;right;right
        constructor <;> omega
      · obtain ⟨hk,hc⟩:=h4
        omega

/-- G inverses to the only surviving first-stage odd feeder. -/
theorem inverse_8sminus4 (b d k c s : Nat)
    (h : GAncestor b d k c) (hb:b=8*s-4) (hd:d=8*s+9)
    (he:s%2=0) (hs:6≤s) :
    (k=2*s-2 ∧ c=12*s+7) ∨
    (k=5*s ∧ c=6*s+2) := by
  induction h with
  | upper k d => left; constructor <;> omega
  | nest b d k c h ih =>
      rcases ih hb hd with h1 | h2
      · obtain ⟨hk,hc⟩:=h1
        right;constructor <;> omega
      · obtain ⟨hk,hc⟩:=h2
        omega

/-- G inverses to the only surviving second-stage odd feeder. -/
theorem inverse_4sminus8 (b d k c s : Nat)
    (h : GAncestor b d k c) (hb:b=4*s-8) (hd:d=12*s+11)
    (he:s%2=0) (hs:6≤s) :
    (k=s-3 ∧ c=14*s+7) ∨
    (k=9*s/2-1 ∧ c=7*s+2) := by
  induction h with
  | upper k d => left; constructor <;> omega
  | nest b d k c h ih =>
      rcases ih hb hd with h1 | h2
      · obtain ⟨hk,hc⟩:=h1
        right;constructor <;> omega
      · obtain ⟨hk,hc⟩:=h2
        omega

#print axioms inverse_16s4_three
#print axioms inverse_8sminus4
#print axioms inverse_4sminus8
end BB6.Agent50P1
