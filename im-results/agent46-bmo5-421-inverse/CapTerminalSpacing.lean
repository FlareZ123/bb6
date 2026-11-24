import CapSignedMacro

namespace CapSieve

/-- Possible terminal exponent after an exceptional positive exit. -/
def TerminalExponent (k n : Nat) : Prop :=
  ∃ w, 0<w ∧ w%3=2^k%3 ∧ 3^n*w=2*(k+n)+3

theorem two_unit_phase (k : Nat) : 2^k%3=1 ∨ 2^k%3=2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ,Nat.mul_mod]
    rcases ih with h|h <;> rw [h] <;> decide

theorem terminal_exponent_gap {k n m : Nat}
    (hn : TerminalExponent k n) (hm : TerminalExponent k m) (hlt : n<m) :
    ∃ c, m-n=3^n*c ∧ c%3=2^k%3 := by
  obtain ⟨u,hu,hum,he⟩ := hn
  obtain ⟨v,hv,hvm,hf⟩ := hm
  have hnm : n+(m-n)=m := by omega
  have hf' : 3^n*(3^(m-n)*v)=2*(k+m)+3 := by
    rw [←Nat.mul_assoc,←Nat.pow_add,hnm]
    exact hf
  have hprod : 3^n*u < 3^n*(3^(m-n)*v) := by omega
  have hle : u≤3^(m-n)*v := by
    by_cases h : u≤3^(m-n)*v
    · exact h
    · have hh := Nat.mul_le_mul_left (3^n) (show 3^(m-n)*v≤u by omega)
      omega
  let d := 3^(m-n)*v-u
  have heq : 3^n*d=2*(m-n) := by
    dsimp [d]
    rw [Nat.mul_sub]
    omega
  have hodd : ∀ a : Nat, 3^a%2=1 := by
    intro a
    induction a with
    | zero => decide
    | succ a ih => rw [Nat.pow_succ,Nat.mul_mod,ih]
  have hpowodd := hodd n
  have hdeven : d%2=0 := by
    have hmod := congrArg (fun x : Nat => x%2) heq
    change (3^n*d)%2=(2*(m-n))%2 at hmod
    rw [Nat.mul_mod,hpowodd] at hmod
    omega
  let c := d/2
  have hc : d=2*c := by dsimp [c]; omega
  have hgap : m-n=3^n*c := by
    rw [hc,show 3^n*(2*c)=2*(3^n*c) by ac_rfl] at heq
    omega
  have hdiv : (3^(m-n)*v)%3=0 := by
    have h : m-n=(m-n-1)+1 := by omega
    rw [h,Nat.pow_succ,show 3^(m-n-1)*3*v=3*(3^(m-n-1)*v) by ac_rfl]
    omega
  have hd_eq : 3^(m-n)*v=u+d := by dsimp [d]; omega
  rw [hc] at hd_eq
  refine ⟨c,hgap,?_⟩
  omega

theorem terminal_exponent_separated {k n m : Nat}
    (hn : TerminalExponent k n) (hm : TerminalExponent k m) (hlt : n<m) :
    n+3^n*(2^k%3)≤m := by
  obtain ⟨c,hg,hmod⟩ := terminal_exponent_gap hn hm hlt
  have hh : 2^k%3≤c := by rw [←hmod]; exact Nat.mod_le _ _
  have hm := Nat.mul_le_mul_left (3^n) hh
  omega

theorem pow3_linear (n : Nat) : 4*n≤3^n+1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    by_cases hn : n=0
    · subst n; decide
    · have hp : 3≤3^n := by
        simpa using Nat.pow_le_pow_right (by decide : 0<3) (show 1≤n by omega)
      rw [Nat.pow_succ]
      omega

theorem terminal_exponent_bound {k n : Nat} (h : TerminalExponent k n) :
    n≤k+2 ∧ 3^n≤4*k+7 := by
  obtain ⟨w,hw,_,he⟩ := h
  have hh : 3^n≤3^n*w := Nat.le_mul_of_pos_right (3^n) hw
  have hl := pow3_linear n
  omega

/-- Tower-like spacing lower bounds for any increasing candidate sequence. -/
def sepLower (phase : Nat) : Nat → Nat
  | 0 => 0
  | r+1 => sepLower phase r+3^(sepLower phase r)*phase

theorem terminal_chain_bound {k r : Nat} {e : Nat → Nat}
    (hc : ∀ i, i≤r → TerminalExponent k (e i))
    (hi : ∀ i, i<r → e i<e (i+1)) :
    3^(sepLower (2^k%3) r)≤4*k+7 := by
  have h : ∀ i, i≤r → sepLower (2^k%3) i≤e i := by
    intro i
    induction i with
    | zero => simp [sepLower]
    | succ i ih =>
      intro hir
      have hlow := ih (by omega)
      have hgap := terminal_exponent_separated (hc i (by omega)) (hc (i+1) hir) (hi i (by omega))
      have hp := Nat.pow_le_pow_right (by decide : 0<3) hlow
      have hm := Nat.mul_le_mul_right (2^k%3) hp
      rw [sepLower]
      omega
  exact Nat.le_trans (Nat.pow_le_pow_right (by decide : 0<3) (h r (by omega)))
    (terminal_exponent_bound (hc r (by omega))).2

theorem terminal_event_candidate {k q : Nat} (hk : 1≤k) (hv : PosQ k q)
    (ht : (signedEvent k q).2=none) :
    ∃ n, TerminalExponent k n ∧
      3^n*(2*positiveNext k q-3)=2*(k+n)+3 := by
  obtain ⟨n,hn⟩ := (positive_event_terminal_iff hk hv).mp ht
  have hf : positiveNext k q<k+7 := by
    by_cases h : positiveNext k q<k+7
    · exact h
    · have hb : 2*k+7<2*positiveNext k q-3 := by omega
      have := CapNegative.above_grows hb n
      omega
  have hw := entry_weight hv hf
  exact ⟨n,⟨_,hw.1.1,hw.2,hn⟩,hn⟩


theorem terminal_four_bound {k : Nat} {e : Nat → Nat}
    (hc : ∀ i, i≤3 → TerminalExponent k (e i))
    (hi : ∀ i, i<3 → e i<e (i+1)) :
    3^85≤4*k+7 := by
  have h := terminal_chain_bound hc hi
  rcases two_unit_phase k with hp|hp
  · rw [hp] at h
    exact h
  · rw [hp] at h
    have hs : 85≤sepLower 2 3 := by decide
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) hs) h

theorem terminal_three_phase_two_bound {k : Nat} {e : Nat → Nat}
    (hp : 2^k%3=2)
    (hc : ∀ i, i≤2 → TerminalExponent k (e i))
    (hi : ∀ i, i<2 → e i<e (i+1)) :
    3^20≤4*k+7 := by
  have h := terminal_chain_bound hc hi
  rw [hp] at h
  exact h

#print axioms terminal_four_bound
#print axioms terminal_three_phase_two_bound
#print axioms terminal_exponent_gap
#print axioms terminal_exponent_bound
#print axioms terminal_chain_bound
#print axioms terminal_event_candidate
end CapSieve
