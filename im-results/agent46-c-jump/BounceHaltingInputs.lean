import BounceHaltLevel
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

theorem haltLevel_mod_two (n : Nat) : ∀ k, haltLevel k n % 2 = (n+1)%2 := by
  induction n with
  | zero =>
    intro k
    simp [haltLevel]
  | succ n ih =>
    intro k
    have hrec := ih (2*k+4)
    have hpar : (haltLevel (2*k+4) n)%2=(n+1)%2 := hrec
    change (2*k+5+haltLevel (2*k+4) n)%2=(n+1+1)%2
    omega

def oddHaltingK (a j : Nat) : Nat :=
  (a-3+haltLevel (a-1) (2*j+1))/2

theorem odd_input_double (a j : Nat) (ha : 3≤a) (he : a%2=1) :
    2*oddHaltingK a j = a-3+haltLevel (a-1) (2*j+1) := by
  have hpar : (haltLevel (a-1) (2*j+1))%2=0 := by
    have h := haltLevel_mod_two (2*j+1) (a-1)
    omega
  have ha2 : (a-3)%2=0 := by omega
  have hnum : (a-3+haltLevel (a-1) (2*j+1))%2=0 := by omega
  have hdiv := Nat.mod_add_div (a-3+haltLevel (a-1) (2*j+1)) 2
  simp only [oddHaltingK]
  omega

/-- For every odd a>=3 and j, the input (a,oddHaltingK(a,j)) halts within one counter section. -/
theorem odd_halt_section_family (a j : Nat) (ha : 3≤a) (he : a%2=1) :
    secNext (a,oddHaltingK a j)=none := by
  let k := oddHaltingK a j
  let h := haltLevel (a-1) (2*j+1)
  have hd : 2*k=a-3+h := odd_input_double a j ha he
  have hfive : 5≤h := haltLevel_ge_five _ _
  have hk : 0<k := by omega
  have hsmall : a<2*k := by omega
  have hC : 2*k-a+3=h := by omega
  have ha0 : a≠0 := by omega
  have ha1 : a≠1 := by omega
  have hk0 : k≠0 := by omega
  have hnot : ¬2*k≤a := by omega
  have hstop := even_halt_bounce (2*j+1) (a-1) (by omega)
  have hf : exactSection (a,k) =
      (a-1+(bounce (a-1) (2*k-a+3)).1,(bounce (a-1) (2*k-a+3)).2) := by
    simp [exactSection,ha0,ha1,hk0,hnot]
  change (exactSection (a,k)).2=none
  rw [hf]
  simpa [hC] using hstop

#print axioms haltLevel_mod_two
#print axioms odd_halt_section_family
end BB6.Agent46
