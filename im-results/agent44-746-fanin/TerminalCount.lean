import ParameterCountBridge
set_option maxHeartbeats 0
namespace CascadeAgent44

/-- The final 3-adic valuation is the sole place where q=7 can create
    the exceptional small odd first-return parent. -/
theorem terminal_odd_param_iff (u n d : Nat)
    (hd : d%2=1) (hz : 2*u+5=3^(n+1)*d) :
    OddParam u n ↔ (2^n*d=7 ∨ BandOdd (2^n*d)) := by
  have hp : 0 < 3^(n+1) := Nat.one_le_pow (n+1) 3 (by decide)
  constructor
  · rintro ⟨k,d',hd',hb,hz'⟩
    have hdeq : d'=d := by
      rw [hz] at hz'
      exact Nat.mul_left_cancel hp hz'.symm
    subst d'
    by_cases hk : k=0
    · left
      subst k
      simp at hb
      omega
    · right
      exact ⟨k,by omega,hb.1,hb.2⟩
  · intro h
    rcases h with heq | ⟨k,hk,hlo,hhi⟩
    · refine ⟨0,d,hd,?_,hz⟩
      simp at heq ⊢
      omega
    · exact ⟨k,d,hd,⟨hlo,hhi⟩,hz⟩

noncomputable def terminalBool (n d : Nat) : Bool := by
  classical
  exact decide (2^n*d=7 ∨ BandOdd (2^n*d))

private theorem terminalBool_iff (n d : Nat) :
    terminalBool n d = true ↔ (2^n*d=7 ∨ BandOdd (2^n*d)) := by
  classical
  simp [terminalBool]

noncomputable def sourceOddCountThrough (u n : Nat) : Nat :=
  (List.range (n+1)).countP (fun t => by
    classical
    exact decide (OddParam u t))

/-- Exact count of all first n+1 odd parameter positions, including
    the terminal dyadic band and q=7 exception. -/
theorem source_odd_count_through (u n d : Nat)
    (hd : d%2=1) (hz : 2*u+5=3^(n+1)*d) :
    sourceOddCountThrough u n + Nat.log2 (3^n*d) +
      (if 0<n ∧ d=1 then 1 else 0) =
        2*n+Nat.log2 d + (if terminalBool n d then 1 else 0) := by
  classical
  have hsource : sourceOddCountThrough u n =
      oddParameterCount u n + (if OddParam u n then 1 else 0) := by
    simp [sourceOddCountThrough,oddParameterCount,List.range_succ,List.countP_append]
  have hprefix := exact_nonterminal_odd_param_count u n d hd hz
  have hterm := terminal_odd_param_iff u n d hd hz
  rw [hsource]
  by_cases h : OddParam u n
  · have hh : terminalBool n d = true :=
      (terminalBool_iff n d).mpr (hterm.mp h)
    simp [h,hh]
    omega
  · have hh : ¬(2^n*d=7 ∨ BandOdd (2^n*d)) := by
      intro ht
      exact h (hterm.mpr ht)
    have hfalse : terminalBool n d = false := by
      cases hb : terminalBool n d with
      | false => rfl
      | true => exact False.elim (hh ((terminalBool_iff n d).mp hb))
    simp [h,hfalse]
    exact hprefix

#print axioms source_odd_count_through
#print axioms terminal_odd_param_iff
end CascadeAgent44
