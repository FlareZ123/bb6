import R82Gap
namespace BB6.Agent7R82
set_option maxHeartbeats 0

theorem pow_ge_succ (q : Nat) : q+1≤2^q := by
  induction q with
  | zero => decide
  | succ q ih =>
    rw [Nat.pow_succ]
    omega

theorem X_ge_32_succ (q:Nat) :
    32*(q+1) ≤ 2^(65536*q+66) := by
  have hge : q+5≤65536*q+66 := by omega
  have he := Nat.pow_le_pow_right (show 0<2 by decide) hge
  have hpow : 2^(q+5) = 32*2^q := by
    rw [show q+5 = q+5 by rfl, Nat.pow_add]
    simp only [Nat.reducePow]
    omega
  rw [hpow] at he
  have hsmall := pow_ge_succ q
  omega

theorem pow_shift (q : Nat) :
    2^(65536*q+82) = 65536*2^(65536*q+66) := by
  rw [show 65536*q+82=(65536*q+66)+16 by omega, Nat.pow_add]
  simp only [Nat.reducePow]
  omega

def expX (q:Nat) := 2^(65536*q+66)
def paramT (q:Nat) := 7*expX q - (q+1)

theorem param_eq (q:Nat) :
   paramT q +(q+1)=7*expX q := by
  have hX := X_ge_32_succ q
  unfold paramT expX
  omega

theorem root_eq (q:Nat) :
  14*2^(65536*q+82)-2*(65536*q+82)-16 =
  131072*paramT q+130892 := by
  have hm := pow_shift q
  have hX := X_ge_32_succ q
  change 14*2^(65536*q+82)-2*(65536*q+82)-16 =
     131072*(7*2^(65536*q+66)-(q+1))+130892
  omega

theorem lowpow (q:Nat) :
    14*2^(65536*q+81) = 458752*expX q := by
  unfold expX
  rw [show 65536*q+81=(65536*q+66)+15 by omega, Nat.pow_add]
  simp only [Nat.reducePow]
  omega

theorem uppow (q:Nat) :
    14*2^(65536*q+82) = 917504*expX q := by
  have h := pow_shift q
  unfold expX
  omega

theorem param_gap (q A C :Nat)
    (hAlo : 66246 ≤ A) (hAhi : A ≤ 130362)
    (hClo : 66146 ≤ C) (hChi : C ≤ 130166) :
    ∀ j : Nat, A*paramT q+C ≠14*2^j := by
  have hband := generic_band q (expX q) (paramT q) A C
    (param_eq q) (X_ge_32_succ q) hAlo hAhi hClo hChi
  have hlow := lowpow q
  have hhigh := uppow q
  have hh : 14*2^(65536*q+81) < A*paramT q+C ∧
      A*paramT q+C < 14*2^(65536*q+81+1) := by
    rcases hband with ⟨h1,h2⟩
    constructor
    · simpa only [hlow] using h1
    · simpa only [show 65536*q+81+1=65536*q+82 by omega, hhigh] using h2
  exact no_fourteen_between (65536*q+81) (A*paramT q+C) hh.1 hh.2

#print axioms root_eq
#print axioms param_gap
end BB6.Agent7R82
