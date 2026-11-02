import ZeroAncestry

namespace BB6.Agent39Sheep

private theorem parent_deterministic {x y z : Nat}
    (a : Parent0 x y) (b : Parent0 x z) : y=z := by
  rcases a with ⟨_,_,ha⟩
  rcases b with ⟨_,_,hb⟩
  omega

theorem chain_target_unique {h x y z : Nat}
    (c : Chain0 h x y) (d : Chain0 h x z) : y=z := by
  induction c generalizing z with
  | nil x =>
      cases d with
      | nil _ => rfl
  | @cons n x mid y edge tail ih =>
      cases d with
      | @cons n' x' mid' z' edge' tail' =>
          have heq : mid=mid' := parent_deterministic edge edge'
          subst mid'
          exact ih tail'

/-- Every chain of length h+1 has a last predecessor at depth h. -/
theorem chain_last_edge {h x z : Nat}
    (c : Chain0 (h+1) x z) :
    ∃ y, Chain0 h x y ∧ Parent0 y z := by
  induction h generalizing x with
  | zero =>
      cases c with
      | cons edge tail =>
          cases tail with
          | nil _ =>
              exact ⟨_,Chain0.nil _,edge⟩
  | succ h ih =>
      cases c with
      | cons edge tail =>
          obtain ⟨mid,hm,hedge⟩ := ih tail
          exact ⟨mid,Chain0.cons edge hm,hedge⟩

private theorem odd_three_power (h : Nat) : (3^h)%2=1 := by
  induction h with
  | zero => decide
  | succ h ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- The exact maximal zero-valuation odd run and its first even endpoint. -/
theorem maximal_zero_valuation_block (h u : Nat)
    (hu : u%2=1) (hx : 5≤1+2^h*u) :
    Chain0 h (1+2^h*u) (1+3^h*u) ∧
    (1+3^h*u)%2=0 ∧
    ¬∃ z, Chain0 (h+1) (1+2^h*u) z := by
  have hchain := chain_from_power h u (by
    cases h with
    | zero => simp only [Nat.pow_zero,Nat.one_mul] at hx ⊢; omega
    | succ k =>
        cases k with
        | zero =>
            simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul] at hx ⊢
            omega
        | succ k =>
            have hodd : 0<u := by omega
            have hp : 0<2^k := Nat.pow_pos (by decide)
            have hm : 4≤4*(2^k*u) := by
              have he : 0<2^k*u := Nat.mul_pos hp hodd
              omega
            have heq : 2^(k+1+1)=4*2^k := by
              simp only [Nat.pow_succ]
              calc
                (2^k*2)*2=(2*2)*2^k := by ac_rfl
                _=4*2^k := by rfl
            rw [heq]
            simpa only [Nat.mul_assoc] using hm)
  have heven : (1+3^h*u)%2=0 := by
    have h3 := odd_three_power h
    have ho : (3^h*u)%2=1 := by
      rw [Nat.mul_mod,h3,hu]
    omega
  refine ⟨hchain,heven,?_⟩
  rintro ⟨z,hc⟩
  obtain ⟨mid,hprefix,hparent⟩ := chain_last_edge hc
  have heq : mid=1+3^h*u := chain_target_unique hprefix hchain
  have hodd := hparent.2.1
  rw [heq] at hodd
  omega

#print axioms maximal_zero_valuation_block
end BB6.Agent39Sheep
