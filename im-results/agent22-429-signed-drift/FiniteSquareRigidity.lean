import Std

/-!
Source-independent finite square-gap theorem for a signed E/S+even-F word.
No original machine source is imported. Lean CI acceptance is pending.
-/
namespace PeriodicSquare

/-- Subtracting two consecutive exact affine-rank word transfers gives
    a purely integral congruence; no third copy is needed. -/
theorem two_transfers_offset (M A B T u0 u1 u2 r0 : Nat)
    (h0 : M*u1 = u0+A*r0+B)
    (h1 : M*u2 = u1+A*(r0+T)+B) :
    ((A*T):Int) =
      (M:Int)*((u2:Int)-(u1:Int))+
      ((u0:Int)-(u1:Int)) := by
  have hi0 : (M:Int)*(u1:Int) =
      (u0:Int)+(A:Int)*(r0:Int)+(B:Int) := by exact_mod_cast h0
  have hi1 : (M:Int)*(u2:Int) =
      (u1:Int)+(A:Int)*((r0:Int)+(T:Int))+(B:Int) := by
    exact_mod_cast h1
  have hdist : (A:Int)*((r0:Int)+(T:Int)) =
      (A:Int)*(r0:Int)+(A:Int)*(T:Int) := by grind
  rw [hdist] at hi1
  calc
    ((A*T):Int) =
        ((M:Int)*(u2:Int)-(M:Int)*(u1:Int))+
        ((u0:Int)-(u1:Int)) := by
      push_cast
      omega
    _ = (M:Int)*((u2:Int)-(u1:Int))+
        ((u0:Int)-(u1:Int)) := by grind

/-- The offset belongs to a bounded asymmetric interval determined by
    the first two paired input heights. This is the paper certificate
    behind the exact modulo-M exclusion in FinitePowerPruner.cjs. -/
theorem two_transfers_gap (M A B T u0 u1 u2 r0 : Nat)
    (h0 : M*u1 = u0+A*r0+B)
    (h1 : M*u2 = u1+A*(r0+T)+B)
    (hsafe0 : 3*u0 ≤ r0) (hsafe1 : 3*u1 ≤ r0+T) :
    ∃ k : Int,
      -(((r0+T)/3):Int) ≤
          ((A*T):Int)-(M:Int)*k ∧
      ((A*T):Int)-(M:Int)*k ≤ ((r0/3):Int) := by
  let k : Int := (u2:Int)-(u1:Int)
  have h0b : u0≤r0/3 := by omega
  have h1b : u1≤(r0+T)/3 := by omega
  have ho := two_transfers_offset M A B T u0 u1 u2 r0 h0 h1
  refine ⟨k,?_⟩
  dsimp [k]
  omega

/-- If a third identical typed word is really entered, its first-input
    parity gives u2-u1 even, strengthening the gap modulus from M to
    2M. Parity is explicit here; it must come from source guards. -/
theorem triple_entry_even_gap (M A B T u0 u1 u2 r0 : Nat)
    (h0 : M*u1 = u0+A*r0+B)
    (h1 : M*u2 = u1+A*(r0+T)+B)
    (hsafe0 : 3*u0 ≤ r0) (hsafe1 : 3*u1 ≤ r0+T)
    (hpar : u1%2=u2%2) :
    ∃ k : Int,
      -(((r0+T)/3):Int) ≤
          ((A*T):Int)-(2*(M:Int))*k ∧
      ((A*T):Int)-(2*(M:Int))*k ≤ ((r0/3):Int) := by
  obtain ⟨m,hm⟩ : ∃ m : Int, (u2:Int)-(u1:Int)=2*m := by
    refine ⟨((u2:Int)-(u1:Int))/2,?_⟩
    omega
  have ho := two_transfers_offset M A B T u0 u1 u2 r0 h0 h1
  have h0b : u0≤r0/3 := by omega
  have h1b : u1≤(r0+T)/3 := by omega
  refine ⟨m,?_⟩
  rw [hm] at ho
  have hmul : (M:Int)*(2*m) = (2*(M:Int))*m := by ac_rfl
  rw [hmul] at ho
  constructor <;> omega

#print axioms two_transfers_offset
#print axioms two_transfers_gap
#print axioms triple_entry_even_gap
end PeriodicSquare
