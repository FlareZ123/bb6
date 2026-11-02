import GInverse
namespace BB6.P1Reduction

/-- Exact three positive-output inverse branches of the P1 drain into (16s+12,3). -/
theorem inverse_16s12_three (b d k c s : Nat)
    (h : GAncestor b d k c) (hb : b = 16*s+12) (hd : d=3) :
    (k=4*s+2 ∧ c=8*s+9) ∨
    (k=6*s+4 ∧ c=4*s+3) ∨
    (k=7*s+5 ∧ c=2*s) := by
  induction h with
  | upper k d =>
      left
      constructor <;> omega
  | nest b d k c h ih =>
      rcases ih hb hd with h0 | h1 | h2
      · rcases h0 with ⟨hk,hc⟩
        right;left
        constructor <;> omega
      · rcases h1 with ⟨hk,hc⟩
        right;right
        constructor <;> omega
      · rcases h2 with ⟨hk,hc⟩
        omega

/-- Exhaustive inverse inputs of the first odd-sector predecessor when s is odd. -/
theorem inverse_8s_splus13 (b d k c s : Nat)
    (h : GAncestor b d k c) (hb : b=8*s) (hd : d=8*s+13)
    (hs : s%2=1) (hge : 3≤s) :
    (k=2*s-1 ∧ c=12*s+13) ∨
    (k=5*s+2 ∧ c=6*s+5) ∨
    (k=(13*s+7)/2 ∧ c=3*s+1) := by
  induction h with
  | upper k d =>
      left
      constructor <;> omega
  | nest b d k c h ih =>
      rcases ih hb hd with h0 | h1 | h2
      · rcases h0 with ⟨hk,hc⟩
        right;left
        constructor <;> omega
      · rcases h1 with ⟨hk,hc⟩
        right;right
        constructor <;> omega
      · rcases h2 with ⟨hk,hc⟩
        omega

/-- Exhaustive inverse inputs of the second odd-sector predecessor for odd s. -/
theorem inverse_12s4_4s7 (b d k c s : Nat)
    (h : GAncestor b d k c) (hb : b=12*s+4) (hd : d=4*s+7)
    (hs : s%2=1) :
    (k=3*s ∧ c=10*s+9) ∨
    (k=(11*s+5)/2 ∧ c=5*s+3) := by
  induction h with
  | upper k d =>
      left
      constructor <;> omega
  | nest b d k c h ih =>
      rcases ih hb hd with h0 | h1
      · rcases h0 with ⟨hk,hc⟩
        right
        constructor <;> omega
      · rcases h1 with ⟨hk,hc⟩
        omega

#print axioms inverse_8s_splus13
#print axioms inverse_12s4_4s7
#print axioms inverse_16s12_three
end BB6.P1Reduction
