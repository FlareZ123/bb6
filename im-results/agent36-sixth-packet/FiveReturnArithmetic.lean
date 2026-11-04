import Lean.Elab.Tactic.Omega
namespace BB6.Agent36SixthArithmetic

def k0 (v : Nat) := 81*v+70
def k1 (v : Nat) := 216*v+187
def k2 (v : Nat) := 576*v+501
def k3 (v : Nat) := 1536*v+1338
def k4 (v : Nat) := 4096*v+3570

def d0 (v : Nat) := 12*(k0 v)*(k0 v)+49*(k0 v)+72
def d1 (v : Nat) := 12*(k1 v)*(k1 v)+49*(k1 v)+58
def d2 (v : Nat) := 12*(k2 v)*(k2 v)+49*(k2 v)+40
def d3 (v : Nat) := 12*(k3 v)*(k3 v)+49*(k3 v)+64
def d4 (v : Nat) := 12*(k4 v)*(k4 v)+49*(k4 v)+74

def total (v : Nat) : Nat := d0 v + (d1 v + (d2 v + (d3 v + d4 v)))
theorem total_closed (v : Nat) : total v = 234258060*v*v+408619369*v+178190110 := by
  have hcross (c : Nat) : v*(c*v) = c*(v*v) := by ac_rfl
  simp only [total,d0,d1,d2,d3,d4,k0,k1,k2,k3,k4,Nat.mul_add,Nat.add_mul,Nat.mul_assoc]
  rw [hcross 81, hcross 216, hcross 576, hcross 1536, hcross 4096]
  omega

theorem fifth_unary (v : Nat) : 8*(k4 v)+17 = 32768*v+28577 := by
  simp only [k4]
  omega

theorem parameter_chain (v : Nat) :
    8*(k0 v)+5 = 3*(k1 v)+4 ∧
    8*(k1 v)+9 = 3*(k2 v)+2 ∧
    8*(k2 v)+10 = 3*(k3 v)+4 ∧
    8*(k3 v)+9 = 3*(k4 v)+3 := by
  simp only [k0,k1,k2,k3,k4]
  omega
#print axioms total_closed
#print axioms parameter_chain
end BB6.Agent36SixthArithmetic
